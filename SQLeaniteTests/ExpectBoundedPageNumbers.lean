import SQLeanite.QueryCost
import SQLeaniteTests.ExpectSignedIntegerCodec

namespace SQLeanite.Tests
open SQLeanite

def expectBoundedPageNumbers : IO Unit := do
  let number : FileFormat.PageNumber :=
    FileFormat.PageNumber.mk ⟨3, by omega⟩ (by decide)
  let bounded : FileFormat.BoundedPageNumber 10 := {
    number
    withinDatabase := by decide }
  let pageId := bounded.toPageId
  let rebuilt := FileFormat.BoundedPageNumber.ofPageId (by decide) pageId
  unless pageId.val == 2 && rebuilt == bounded do
    fail "SQLite one-based page number did not roundtrip through pager PageId"

def expectDatabaseFirstPage : IO Unit := do
  let usable : FileFormat.UsablePageSize := {
    val := 4096
    atLeastMinimum := by decide
    atMostMaximum := by decide }
  let headerPrefix : FileFormat.HeaderPrefix := {
    pageSizeField := ⟨4096, by omega⟩
    writeVersion := 1
    readVersion := 1
    reservedSpace := 0
    changeCounter := ⟨42, by omega⟩ }
  let databaseHeader : FileFormat.DatabaseHeader := {
    headerPrefix
    databaseSizePages := ⟨10, by omega⟩
    firstFreelistTrunk := ⟨0, by omega⟩
    freelistPageCount := ⟨0, by omega⟩
    schemaCookie := ⟨7, by omega⟩
    schemaFormat := ⟨4, by omega⟩
    defaultPageCacheSize := ⟨2000, by omega⟩
    largestRootBTreePage := ⟨0, by omega⟩
    textEncoding := ⟨1, by omega⟩
    userVersion := ⟨3, by omega⟩
    incrementalVacuum := ⟨0, by omega⟩
    applicationId := ⟨0, by omega⟩
    versionValidFor := ⟨42, by omega⟩
    sqliteVersion := ⟨3050004, by omega⟩ }
  let common : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨0, by omega⟩
    cellContentStart := ⟨4096, by omega⟩
    fragmentedFreeBytes := 0 }
  let header : FileFormat.ValidBTreePageHeader usable.val := {
    header := .leafTable common
    wellFormed := by decide }
  let pointers : FileFormat.SizedU16Values 0 := { values := [], length_eq := rfl }
  let pagePrefix : FileFormat.BTreePagePrefix usable.val := {
    header
    pointers
    pointersWithin := by decide }
  let generic : FileFormat.BTreeCellLayout usable.val := {
    pagePrefix
    cells := []
    pointerAgreement := rfl
    afterPrefix := by simp
    pairwiseDisjoint := by simp }
  let typed : FileFormat.TypedBTreePageLayout usable := {
    generic
    cells := []
    placementsAgree := rfl }
  let bounded : FileFormat.BoundedTypedBTreePageLayout usable 10 := {
    layout := typed
    referencesWithin := by decide }
  let firstPage : FileFormat.DatabaseFirstPage usable 10 := {
    databaseHeader
    headerWellFormed := by decide
    layout := bounded
    cellsAfterFirstPrefix := by
      intro cell member
      simp [bounded, typed, generic] at member }
  let validDatabaseHeader : FileFormat.ValidDatabaseHeader usable 10 := {
    header := databaseHeader
    wellFormed := by decide }
  let decodedPrefix : FileFormat.DatabaseFirstPagePrefix usable 10 := {
    databaseHeader := validDatabaseHeader
    btreePrefix := pagePrefix }
  let otherPages : FileFormat.VerifiedPageSet usable 10 := {
    btreePages := []
    overflowChains := []
    pageIdsNodup := by decide }
  let databasePages : FileFormat.VerifiedDatabasePageSet usable 10 := {
    firstPage
    otherPages
    pageIdsNodup := by decide }
  let image := firstPage.encodePage
  unless image.bytes.size == 4096 &&
      image.bytes.toList.take 100 == FileFormat.encodeDatabaseHeader databaseHeader &&
      image.bytes[100]? == some 13 && firstPage.toPageWrite.pageId.val == 0 &&
      databasePages.writes.map (fun write => write.pageId.val) == [0] &&
      FileFormat.decodeDatabaseFirstPagePrefix usable 10
        (decodedPrefix.encode ++ [9]) == some (decodedPrefix, [9]) &&
      image.bytes.toList.take decodedPrefix.encode.length == decodedPrefix.encode do
    fail "SQLite database first page did not place its B-tree header at byte 100"
  match DiskFormat.decodeDatabaseGeometry
      (FileFormat.encodeDatabaseHeader databaseHeader ++ [9]) with
  | some (geometry, [9]) =>
      unless geometry.usable.val == 4096 && geometry.pageCount == 10 do
        fail "database geometry decoder discovered the wrong pager dimensions"
  | _ => fail "database geometry decoder rejected a valid SQLite header"
  let reservedHeader : FileFormat.DatabaseHeader := {
    databaseHeader with
    headerPrefix := { databaseHeader.headerPrefix with reservedSpace := 1 } }
  match DiskFormat.decodeDatabaseGeometry
      (FileFormat.encodeDatabaseHeader reservedHeader) with
  | none => pure ()
  | some _ => fail "database geometry decoder accepted unsupported reserved bytes"
  let emptyDisk : Storage.Disk 4096 10 :=
    Storage.Disk.constant 4096 10 (Storage.Page.zero 4096)
  let physicalDisk := Storage.applyWrites emptyDisk databasePages.writes
  let fileBytes := DiskFormat.encodeDisk physicalDisk
  match DiskFormat.decodeDatabaseImage (fileBytes ++ [9]) with
  | some (opened, [9]) =>
      let firstId : Storage.PageId opened.geometry.pageCount :=
        ⟨0, opened.geometry.header.wellFormed.2.2.2.1⟩
      unless opened.geometry.usable.val == 4096 &&
          opened.geometry.pageCount == 10 &&
          (opened.disk.read firstId).bytes == image.bytes do
        fail "dynamic database image decoder changed its geometry or page one"
  | _ => fail "dynamic database image decoder rejected a complete verified image"
  match DiskFormat.decodeDatabaseImage (fileBytes.take (fileBytes.length - 1)) with
  | none => pure ()
  | some _ => fail "dynamic database image decoder accepted a truncated file"

def expectDiskFormat : IO Unit := do
  let firstPage : Storage.Page 4 := {
    bytes := #[1, 2, 3, 4]
    sizeInvariant := by decide }
  let secondPage : Storage.Page 4 := {
    bytes := #[5, 6, 7, 8]
    sizeInvariant := by decide }
  let disk : Storage.Disk 4 2 := {
    read := fun pageId => if pageId.val = 0 then firstPage else secondPage }
  let encoded := DiskFormat.encodeDisk disk
  unless encoded == [1, 2, 3, 4, 5, 6, 7, 8] do
    fail "whole-disk encoder did not concatenate pages in pager order"
  match DiskFormat.decodeDisk 4 2 (encoded ++ [9]) with
  | none => fail "whole-disk decoder rejected its encoder output"
  | some (decoded, suffix) =>
      let firstId : Storage.PageId 2 := ⟨0, by decide⟩
      let secondId : Storage.PageId 2 := ⟨1, by decide⟩
      unless suffix == [9] && (decoded.read firstId).bytes == firstPage.bytes &&
          (decoded.read secondId).bytes == secondPage.bytes do
        fail "whole-disk decoder changed page bytes or consumed its suffix"
  match DiskFormat.decodeDisk 4 2 (encoded.take 7) with
  | none => pure ()
  | some _ => fail "whole-disk decoder accepted a truncated final page"

open QuerySemantics in
def expectOptimizerSemantics : IO Unit := do
  let one : Core.Value := .integer ⟨1, by decide, by decide⟩
  let two : Core.Value := .integer ⟨2, by decide, by decide⟩
  let five : Core.Value := .integer ⟨5, by decide, by decide⟩
  let seven : Core.Value := .integer ⟨7, by decide, by decide⟩
  let rightText : Core.Value :=
    .text ⟨[114, 105, 103, 104, 116], by decide⟩
  let leftRows : List Row :=
    [.values [one], .values [.null], .values [two]]
  let rightRows : List Row := [.values [rightText]]
  let predicate : Predicate := .equals (.cell 0) one
  let joinPlan : Plan := .innerJoin (.rows leftRows) (.rows rightRows)
  let filtered : Plan := .filter (.onLeft predicate) joinPlan
  let pushed := QuerySemantics.predicatePushdown filtered
  unless evalPlan Core.Database.empty filtered == evalPlan Core.Database.empty pushed do
    fail "verified predicate pushdown changed inner-join rows"
  let constantPredicate : Predicate :=
    .and (.constant .true)
      (.or (.constant .false) (.not (.constant .unknown)))
  let constantPlan : Plan := .filter constantPredicate (.rows leftRows)
  unless evalPlan Core.Database.empty constantPlan ==
      evalPlan Core.Database.empty (QuerySemantics.constantFolding constantPlan) do
    fail "verified constant folding changed three-valued WHERE semantics"
  let identityPlan : Plan := .project .identity joinPlan
  unless evalPlan Core.Database.empty identityPlan ==
      evalPlan Core.Database.empty (QuerySemantics.projectionElimination identityPlan) do
    fail "verified identity projection elimination changed rows"
  let fusedInput : Plan := .filter (.truthy (.cell 0))
    (.filter (.notEquals (.cell 0) .null) (.rows leftRows))
  unless evalPlan Core.Database.empty fusedInput ==
      evalPlan Core.Database.empty (QuerySemantics.filterFusion fusedInput) do
    fail "verified filter fusion changed three-valued WHERE semantics"
  let unionInput : Plan :=
    .unionAll (.rows (leftRows.take 2)) (.rows (leftRows.drop 2))
  let distributedInput : Plan := .filter predicate unionInput
  let distributed := QuerySemantics.unionDistribution distributedInput
  unless evalPlan Core.Database.empty distributedInput ==
      evalPlan Core.Database.empty distributed do
    fail "verified UNION ALL distribution changed row order or 3VL results"
  match distributed with
  | .unionAll (.filter _ _) (.filter _ _) => pure ()
  | _ => fail "explicit filter/UNION distribution did not expose both arms"
  let costSafe := QuerySemantics.optimizePlan distributedInput
  unless (QuerySemantics.cost Core.Database.empty costSafe).total ≤
      (QuerySemantics.cost Core.Database.empty distributedInput).total do
    fail "live optimizer increased the certified logical cost"
  let groupedInput : Plan :=
    .groupSum (fun _ => .values [one]) (fun _ => 2) unionInput
  let groupedDistributed := QuerySemantics.unionDistribution groupedInput
  unless evalPlan Core.Database.empty groupedInput ==
      evalPlan Core.Database.empty groupedDistributed do
    fail "verified grouped UNION ALL distribution changed weighted results"
  match groupedDistributed with
  | .unionAll (.groupSum _ _ _) (.groupSum _ _ _) => pure ()
  | _ => fail "explicit grouped UNION distribution did not expose both arms"
  let ordered : QuerySemantics.Select := {
    plan := filtered
    orderBy := [{ column := .left (.cell 0) }] }
  unless QuerySemantics.eval Core.Database.empty ordered ==
      QuerySemantics.eval Core.Database.empty
        ((Rewrite.predicatePushdown).apply ordered) do
    fail "optimizer rewrite changed observable ORDER BY output"
  let sample : Row := .values [seven]
  if whereRows
      (.or (.constant .unknown) (.not (.constant .unknown))) [sample] ==
      whereRows (.constant .true) [sample] then
    fail "test failed to witness SQL excluded-middle unsoundness"
  if whereRows
      (.onRight (.equals (.cell 0) five))
      (leftJoinRows [sample] [.values [.null]]) ==
      leftJoinRows [sample]
        (whereRows (.equals (.cell 0) five) [.values [.null]]) then
    fail "test failed to witness outer-join predicate-pushdown unsoundness"
  let corePredicate : Core.Predicate :=
    .not (.not (.equal 0 one))
  let coreQuery : Core.Query := {
    columns := [0]
    predicate := some corePredicate }
  let optimized := CoreOptimizerBridge.optimize "items" coreQuery
  match optimized.predicate with
  | some (.equal 0 value) =>
      unless value = one do
        fail "live optimizer changed the normalized comparison value"
  | _ => fail "live optimizer did not eliminate double negation"
  let coreRows : List Core.Row := [
    { rowid := ⟨1, by decide, by decide⟩, values := [one] },
    { rowid := ⟨2, by decide, by decide⟩, values := [two] }]
  unless optimized.eval coreRows = coreQuery.eval coreRows do
    fail "live denotational optimizer changed Core query results"
  let rightCoreRows : List Core.Row := [
    { rowid := ⟨1, by decide, by decide⟩, values := [two] },
    { rowid := ⟨2, by decide, by decide⟩, values := [one] }]
  let joinEquality : CoreJoin.Predicate :=
    .equal (.column ⟨.left, 0⟩) (.column ⟨.right, 0⟩)
  let denotationalJoin := CoreOptimizerBridge.innerJoinPlan
    (some joinEquality) none coreRows rightCoreRows
  unless evalPlan Core.Database.empty
      (QuerySemantics.optimizePlan denotationalJoin) ==
      (CoreJoin.matchingRows (some joinEquality) none
        (CoreJoin.crossRows coreRows rightCoreRows)).map
          CoreOptimizerBridge.joinedRow do
    fail "proved optimizer changed the embedded live inner join"
  let joinQuery : CoreJoin.Query := {
    columns := [.column ⟨.left, 0⟩, .column ⟨.right, 0⟩]
    on := some joinEquality }
  let optimizedJoin := CoreOptimizerBridge.optimizeJoin "left" "right" joinQuery
  unless optimizedJoin.eval coreRows rightCoreRows ==
      joinQuery.eval coreRows rightCoreRows do
    fail "live denotational join optimizer changed Core join results"
  let outerRightRows : List Core.Row := rightCoreRows.take 1
  let outerPlan := CoreOptimizerBridge.leftOuterJoinPlan
    (some joinEquality) none 1 coreRows outerRightRows
  unless evalPlan Core.Database.empty
      (QuerySemantics.optimizePlan outerPlan) ==
      (CoreJoin.leftOuterRows (some joinEquality) 1 coreRows outerRightRows).map
        CoreOptimizerBridge.joinedRow do
    fail "proved optimizer changed width-aware live left-outer rows"
  let leftJoinQuery : CoreJoin.Query := {
    columns := [.column ⟨.left, 0⟩, .column ⟨.right, 0⟩]
    on := some joinEquality
    kind := .left
    rightWidth := 1 }
  let optimizedLeft := CoreOptimizerBridge.optimizeJoin
    "left" "right" leftJoinQuery
  unless optimizedLeft.eval coreRows outerRightRows ==
      leftJoinQuery.eval coreRows outerRightRows do
    fail "live width-aware left-join optimizer changed Core results"
  unless optimizedLeft.eval coreRows outerRightRows ==
      [[one, .null], [two, two]] do
    fail "width-aware left-join denotation lost its NULL-extended row"
  let compoundLeft : List (List Core.Value) := [[one], [two], [one]]
  let compoundRight : List (List Core.Value) := [[two], [one], [two]]
  let checkCompound (operation : CompoundOp) : IO Unit := do
    let expected := (CoreOptimizerBridge.compoundRows operation
      compoundLeft compoundRight).map CoreOptimizerBridge.compoundRow
    unless evalPlan Core.Database.empty
        (QuerySemantics.optimizePlan
          (CoreOptimizerBridge.compoundPlan operation
            compoundLeft compoundRight)) == expected do
      fail "proved compound optimizer changed duplicate-sensitive bag results"
    unless CoreOptimizerBridge.optimizeCompoundOp operation = operation do
      fail "live compound optimizer changed the SQL set operation"
  checkCompound .unionAll
  checkCompound .unionDistinct
  checkCompound .intersect
  checkCompound .except

def expectKRelationSemantics : IO Unit := do
  let left : KRelation.Relation Nat := fun row => if row == 1 then 2 else 0
  let right : KRelation.Relation Nat := fun row => if row == 1 then 3 else 1
  let union := KRelation.unionAll left right
  unless union 1 == 5 && KRelation.distinct union 1 == 1 &&
      KRelation.intersect left right 1 == 2 && KRelation.except right left 1 == 1 do
    fail "multiplicity-valued set operators lost SQL bag counts"
  let selected := KRelation.select
    (fun row => if row == 1 then .unknown else .true) union
  unless selected 1 == 0 && selected 2 == 1 do
    fail "K-relation selection treated UNKNOWN as TRUE"
  let grouped := KRelation.groupCount [1, 2] (fun row => row % 2) union
  unless grouped 0 == 1 && grouped 1 == 5 do
    fail "K-relation grouping did not sum source multiplicities"

end SQLeanite.Tests
