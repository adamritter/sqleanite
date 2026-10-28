import SQLeanite.CoreDecode.ValidateCanonicalIndexGroupsFromEncodeOverflowIndexTableGroups
import SQLeanite.RecursivePageBTree.EncodeIndexRefines
import SQLeanite.RelationalAlgebra.JoinedLeftOuterRowsEval
import SQLeaniteTests.ExpectBoundedPageNumbers

namespace SQLeanite.Tests
open SQLeanite

def expectRelationalAlgebra : IO Unit := do
  let left : RelationalAlgebra.Expr Nat :=
    .relation (RelationalAlgebra.ofList [1, 1, 2])
  let right : RelationalAlgebra.Expr Nat :=
    .relation (RelationalAlgebra.ofList [10, 10])
  let product := RelationalAlgebra.eval (.product left right)
  unless product (1, 10) == 4 && product (2, 10) == 2 do
    fail "typed product lost SQL bag multiplicity"
  let selected := RelationalAlgebra.eval
    (.select (fun row : Nat × Nat => if row.1 == 1 then .true else .unknown)
      (.product left right))
  let pushed := RelationalAlgebra.eval
    (.product (.select (fun row : Nat => if row == 1 then .true else .unknown)
      left) right)
  unless selected (1, 10) == pushed (1, 10) &&
      selected (2, 10) == pushed (2, 10) do
    fail "general algebra predicate pushdown changed 3VL bag semantics"
  let swapped := RelationalAlgebra.eval
    (RelationalAlgebra.swapProduct (.product left right))
  unless swapped (10, 1) == product (1, 10) do
    fail "general algebra product permutation changed multiplicity"
  let third : RelationalAlgebra.Expr Nat :=
    .relation (RelationalAlgebra.ofList [100, 100, 100])
  let associated := RelationalAlgebra.eval
    (RelationalAlgebra.reassociateProduct (.product (.product left right) third))
  let direct := RelationalAlgebra.eval (.product left (.product right third))
  unless associated (1, (10, 100)) == direct (1, (10, 100)) do
    fail "general algebra product reassociation changed multiplicity"
  let emptyRight : RelationalAlgebra.Expr Nat :=
    .relation KRelation.empty
  let rightDomain : RelationalAlgebra.Domain Nat := ⟨[10], by decide⟩
  let outer := RelationalAlgebra.eval
    (.leftOuter inferInstance rightDomain 0
      (fun left right => if left == right then .true else .false)
      left emptyRight)
  unless outer (1, 0) == 2 && outer (2, 0) == 1 do
    fail "general algebra left outer join lost unmatched multiplicity"
  let outerSelected := RelationalAlgebra.eval
    (.select (fun row : Nat × Nat => if row.1 == 1 then .true else .unknown)
      (.leftOuter inferInstance rightDomain 0
        (fun left right => if left == right then .true else .false)
        left emptyRight))
  let outerPushed := RelationalAlgebra.eval
    (.leftOuter inferInstance rightDomain 0
      (fun left right => if left == right then .true else .false)
      (.select (fun row : Nat => if row == 1 then .true else .unknown) left)
      emptyRight)
  unless outerSelected (1, 0) == outerPushed (1, 0) &&
      outerSelected (2, 0) == outerPushed (2, 0) do
    fail "left-side pushdown through outer join changed 3VL bag semantics"
  let duplicated := RelationalAlgebra.eval (.distinct (.distinct left))
  unless duplicated 1 == 1 && duplicated 2 == 1 do
    fail "typed DISTINCT was not idempotent"
  let groupDomain : RelationalAlgebra.Domain Nat := ⟨[1, 2], by decide⟩
  let groupedUnion := RelationalAlgebra.eval
    (.groupSum inferInstance groupDomain (fun row => row % 2) (fun row => row)
      (.unionAll left left))
  unless groupedUnion 0 == 4 && groupedUnion 1 == 4 do
    fail "typed grouped SUM did not preserve UNION ALL multiplicity"
  let materializedCount := RelationalAlgebra.eval
    (.materializeCount inferInstance
      (RelationalAlgebra.supportDomain [1, 1, 2]) (fun row => row) left)
  unless materializedCount (1, 2) == 1 &&
      materializedCount (2, 1) == 1 && materializedCount (1, 1) == 0 do
    fail "materialized COUNT did not emit one exact aggregate row per group"
  let materializedSum := RelationalAlgebra.eval
    (.materializeSum inferInstance
      (RelationalAlgebra.supportDomain [1, 1, 2]) (fun row => row)
      (fun row => if row == 1 then 0 else 3) left)
  unless materializedSum (1, 0) == 1 &&
      materializedSum (2, 3) == 1 && materializedSum (2, 0) == 0 do
    fail "materialized SUM lost a zero-valued group or emitted a wrong value"
  let one : Core.Value := .integer ⟨1, by decide, by decide⟩
  let two : Core.Value := .integer ⟨2, by decide, by decide⟩
  let leftRow : QuerySemantics.Row := .values [one]
  let rightRow : QuerySemantics.Row := .values [two]
  let legacyPlan : QuerySemantics.Plan :=
    .filter (.constant .true)
      (.innerJoin (.rows [leftRow, leftRow]) (.rows [rightRow]))
  match RelationalAlgebra.ofPlan? Core.Database.empty legacyPlan with
  | none => fail "typed algebra rejected the product/filter optimizer basis"
  | some translated =>
      let relation := RelationalAlgebra.eval translated
      unless relation (.joined leftRow rightRow) == 2 do
        fail "optimizer-plan translation changed joined-row multiplicity"
  match RelationalAlgebra.ofPlan? Core.Database.empty
      (.project .left legacyPlan) with
  | none => fail "typed algebra rejected proved finite-support projection"
  | some translated =>
      let relation := RelationalAlgebra.eval translated
      unless relation leftRow == 2 do
        fail "typed algebra projection lost duplicate joined rows"
  let setPlan : QuerySemantics.Plan :=
    .distinct (.unionAll (.rows [leftRow, leftRow]) (.rows [leftRow]))
  match RelationalAlgebra.ofPlan? Core.Database.empty setPlan with
  | none => fail "typed algebra rejected UNION ALL / DISTINCT plan"
  | some translated =>
      let relation := RelationalAlgebra.eval translated
      unless relation leftRow == 1 do
        fail "typed algebra DISTINCT did not collapse UNION ALL multiplicity"
  let intersectPlan : QuerySemantics.Plan :=
    .intersectAll (.rows [leftRow, leftRow, leftRow])
      (.rows [leftRow, leftRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty intersectPlan with
  | none => fail "typed algebra rejected INTERSECT ALL plan"
  | some translated =>
      unless RelationalAlgebra.eval translated leftRow == 2 do
        fail "typed algebra INTERSECT ALL lost minimum multiplicity"
  let exceptPlan : QuerySemantics.Plan :=
    .exceptAll (.rows [leftRow, leftRow, leftRow]) (.rows [leftRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty exceptPlan with
  | none => fail "typed algebra rejected EXCEPT ALL plan"
  | some translated =>
      unless RelationalAlgebra.eval translated leftRow == 2 do
        fail "typed algebra EXCEPT ALL lost truncated difference"
  let outerPlan : QuerySemantics.Plan :=
    .leftOuterJoin (.rows [leftRow, leftRow]) (.rows [])
  match RelationalAlgebra.ofPlan? Core.Database.empty outerPlan with
  | none => fail "typed algebra rejected left outer plan"
  | some translated =>
      unless RelationalAlgebra.eval translated
          (.joined leftRow (.values [])) == 2 do
        fail "typed algebra left outer plan lost NULL-extended multiplicity"
  let matchingOuterPlan : QuerySemantics.Plan :=
    .leftOuterOn (.equals (.right (.cell 0)) two)
      (.rows [leftRow, leftRow]) (.rows [rightRow, rightRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty matchingOuterPlan with
  | none => fail "typed algebra rejected predicate-bearing left outer plan"
  | some translated =>
      unless RelationalAlgebra.eval translated (.joined leftRow rightRow) == 4 do
        fail "predicate-bearing outer join lost duplicate matches"
  let falseOuterPlan : QuerySemantics.Plan :=
    .leftOuterOn (.equals (.right (.cell 0)) one)
      (.rows [leftRow, leftRow]) (.rows [rightRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty falseOuterPlan with
  | none => fail "typed algebra rejected unmatched left outer plan"
  | some translated =>
      unless RelationalAlgebra.eval translated
          (.joined leftRow (.values [])) == 2 do
        fail "predicate-bearing outer join lost false NULL extension"
  let unknownOuterPlan : QuerySemantics.Plan :=
    .leftOuterOn (.equals (.right (.cell 0)) one)
      (.rows [leftRow, leftRow]) (.rows [.values [.null]])
  match RelationalAlgebra.ofPlan? Core.Database.empty unknownOuterPlan with
  | none => fail "typed algebra rejected UNKNOWN left outer plan"
  | some translated =>
      unless RelationalAlgebra.eval translated
          (.joined leftRow (.values [])) == 2 do
        fail "predicate-bearing outer join treated UNKNOWN as a match"
  let groupCountPlan : QuerySemantics.Plan :=
    .groupCount (fun row => row) (.rows [leftRow, leftRow, rightRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty groupCountPlan with
  | none => fail "typed algebra rejected GROUP COUNT plan"
  | some translated =>
      let relation := RelationalAlgebra.eval translated
      unless relation leftRow == 2 && relation rightRow == 1 do
        fail "GROUP COUNT translation lost input multiplicities"
  let groupSumPlan : QuerySemantics.Plan :=
    .groupSum (fun _ => leftRow)
      (fun row => if row == leftRow then 3 else 2)
      (.rows [leftRow, leftRow, rightRow])
  match RelationalAlgebra.ofPlan? Core.Database.empty groupSumPlan with
  | none => fail "typed algebra rejected GROUP SUM plan"
  | some translated =>
      unless RelationalAlgebra.eval translated leftRow == 8 do
        fail "GROUP SUM translation lost weighted duplicate contributions"
  let coreGroupRows : List Core.Row := [
    { rowid := ⟨1, by decide, by decide⟩, values := [one] },
    { rowid := ⟨2, by decide, by decide⟩, values := [one] },
    { rowid := ⟨3, by decide, by decide⟩, values := [two] }]
  let coreGroupQuery : Core.GroupQuery := {
    groupBy := [0]
    outputs := [.key 0, .countStar] }
  unless RelationalAlgebra.materializedCountRows coreGroupQuery.rowKey
      (coreGroupQuery.selectedRows coreGroupRows) ==
      [([one], 2), ([two], 1)] do
    fail "live Core grouped COUNT disagreed with materialized algebra rows"
  let three : Core.Value := .integer ⟨3, by decide, by decide⟩
  let negativeFive : Core.Value := .integer ⟨-5, by decide, by decide⟩
  let negativeTwo : Core.Value := .integer ⟨-2, by decide, by decide⟩
  let coreSumRows : List Core.Row := [
    { rowid := ⟨1, by decide, by decide⟩, values := [one, three] },
    { rowid := ⟨2, by decide, by decide⟩, values := [one, negativeFive] },
    { rowid := ⟨3, by decide, by decide⟩, values := [two, .null] }]
  match coreGroupQuery.outputValue coreSumRows [one] (.sumColumn 1) with
  | .ok value => unless value == negativeTwo do
      fail "live grouped SUM disagreed with the mathematical negative sum"
  | .error message => fail s!"live grouped SUM failed: {message}"
  match coreGroupQuery.outputValue coreSumRows [two] (.sumColumn 1) with
  | .ok value => unless value == .null do
      fail "live grouped SUM did not return NULL for an all-NULL group"
  | .error message => fail s!"live all-NULL grouped SUM failed: {message}"
  let mixedGroupQuery : Core.GroupQuery := {
    groupBy := [0]
    outputs := [.key 0, .countStar, .sumColumn 1] }
  match mixedGroupQuery.eval coreSumRows with
  | .ok rows => unless rows ==
      [[one, .integer ⟨2, by decide, by decide⟩, negativeTwo],
       [two, .integer ⟨1, by decide, by decide⟩, .null]] do
      fail "live mixed aggregate tuple changed key/COUNT/SUM alignment"
  | .error message => fail s!"live mixed aggregate tuple failed: {message}"

def expectPagedBTree : IO Unit := do
  let empty : PagedBTree.Tree String := .empty
  let tree := empty.insert 3 "three" |>.insert 1 "one" |>.insert 2 "two"
  unless tree.toList == [(1, "one"), (2, "two"), (3, "three")] do
    fail "paged B+tree insertion changed sorted observable contents"
  unless tree.pages.length == 2 && tree.pageRefs.length == 2 do
    fail "paged B+tree did not split a full leaf"
  let replaced := tree.insert 2 "TWO"
  unless replaced.toList == [(1, "one"), (2, "TWO"), (3, "three")] do
    fail "paged B+tree replacement duplicated an existing key"
  let merged := replaced.delete 2
  unless merged.toList == [(1, "one"), (3, "three")] &&
      merged.pages.length == 1 do
    fail "paged B+tree deletion did not preserve contents while merging leaves"

def expectRecursiveBPlusTree : IO Unit := do
  let entries := (List.range 64).map fun key => (key, toString key)
  let tree := (RecursiveBPlusTree.Tree.empty :
    RecursiveBPlusTree.Tree String).insertAll entries
  unless tree.toList == entries do
    fail "recursive B+tree insertion changed sorted contents"
  unless tree.height >= 4 && tree.pageCount > 32 do
    fail "recursive B+tree did not propagate splits beyond two levels"
  unless tree.checkBalanced do
    fail "recursive B+tree insertion violated occupancy or leaf depth"
  unless tree.lookup 37 == some "37" do
    fail "recursive B+tree descent missed an inserted key"
  unless tree.rangeScan 20 24 ==
      [(20, "20"), (21, "21"), (22, "22"), (23, "23")] do
    fail "recursive B+tree range scan crossed the wrong leaf interval"
  let replaced := tree.insert 37 "replaced"
  unless replaced.lookup 37 == some "replaced" &&
      replaced.toList.length == tree.toList.length do
    fail "recursive B+tree replacement duplicated its key"
  let deleted := replaced.delete 37
  unless deleted.lookup 37 == none && deleted.toList.length + 1 == tree.toList.length do
    fail "recursive B+tree deletion failed to merge an empty leaf"
  let deletedMany := (List.range 48).foldl
    (fun current key => current.deleteBalanced key) tree
  unless deletedMany.toList == entries.drop 48 && deletedMany.checkBalanced do
    fail "recursive B+tree redistribution or root shrink changed contents/balance"
  let verifiedDeletes := (List.range 48).foldl
    (fun current key => current.delete key) tree
  unless verifiedDeletes.toList == entries.drop 48 &&
      verifiedDeletes.checkRootValid do
    fail "verified recursive B+tree deletion did not preserve its full invariant"
  let (coreState, _) ← match CoreSQL.execute Core.State.empty "
      CREATE TABLE core_tree(id INTEGER PRIMARY KEY,v TEXT);
      INSERT INTO core_tree VALUES(1,'one'),(3,'three'),(5,'five');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"Core B+tree setup failed: {message}"
  let coreTable ← match coreState.database.findTable? "core_tree" with
    | some table => pure table
    | none => fail "Core B+tree setup lost its table"
  let coreTree := coreTable.rowTree.root.erase
  unless coreTree.toList == Core.treeEntries coreTable.rows &&
      coreTree.checkRootValid do
    fail "Core B+tree construction changed signed-rowid order or validity"
  let insertedRow ← match Core.Row.create coreTable.schema
      [.integer ⟨4, by decide, by decide⟩,
        .text ⟨[102, 111, 117, 114], by decide⟩] with
    | .ok row => pure row
    | .error message => fail s!"Core B+tree row construction failed: {message}"
  let insertedTree := coreTree.insert insertedRow.treeKey insertedRow
  unless insertedTree.toList.map (·.2.rowid.value) == [1, 3, 4, 5] &&
      insertedTree.lookup insertedRow.treeKey == some insertedRow do
    fail "Core B+tree localized insertion changed its list abstraction"
  let deletedTree := insertedTree.delete insertedRow.treeKey
  unless deletedTree.toList == Core.treeEntries coreTable.rows &&
      deletedTree.checkRootValid do
    fail "Core B+tree localized deletion changed its list abstraction"

def expectCoreMergeJoin : IO Unit := do
  let sql := "
    CREATE TABLE merge_left(id INTEGER PRIMARY KEY,label TEXT);
    CREATE TABLE merge_right(id INTEGER PRIMARY KEY,label TEXT);
    INSERT INTO merge_left VALUES(1,'left one'),(3,'left three'),(5,'left five');
    INSERT INTO merge_right VALUES(2,'right two'),(3,'right three'),(5,'right five');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"merge join setup failed: {message}"
  let left ← match state.database.findTable? "merge_left" with
    | some table => pure table
    | none => fail "merge join setup lost its left table"
  let right ← match state.database.findTable? "merge_right" with
    | some table => pure table
    | none => fail "merge join setup lost its right table"
  let query : CoreJoin.Query := {
    columns := [.column ⟨.left, 0⟩, .column ⟨.left, 1⟩, .column ⟨.right, 1⟩]
    on := some (CoreJoin.rowidOn left.schema.primaryKey right.schema.primaryKey) }
  unless query.evalPlanned left right == query.eval left.rows right.rows do
    fail "primary-key merge join changed nested-loop semantics"
  unless query.evalPlanned left right == [
      [.integer ⟨3, by decide, by decide⟩,
        .text ⟨[108, 101, 102, 116, 32, 116, 104, 114, 101, 101], by decide⟩,
        .text ⟨[114, 105, 103, 104, 116, 32, 116, 104, 114, 101, 101], by decide⟩],
      [.integer ⟨5, by decide, by decide⟩,
        .text ⟨[108, 101, 102, 116, 32, 102, 105, 118, 101], by decide⟩,
        .text ⟨[114, 105, 103, 104, 116, 32, 102, 105, 118, 101], by decide⟩]] do
    fail "primary-key merge join returned the wrong matching rows"
  let leftOnly : CoreJoin.Predicate :=
    .equal (.column ⟨.left, left.schema.primaryKey⟩)
      (.literal (.integer ⟨1, by decide, by decide⟩))
  unless leftOnly.leftOnly do
    fail "join planner did not recognize a left-only predicate"
  let filteredQuery := { query with where_ := some leftOnly }
  unless filteredQuery.evalPlanned left right ==
      filteredQuery.eval left.rows right.rows do
    fail "live inner-join left-predicate pushdown changed semantics"
  let outerKind := { filteredQuery with kind := CoreJoin.JoinKind.left }
  let outerQuery := { outerKind with rightWidth := right.schema.columns.length }
  unless outerQuery.evalPlanned left right ==
      outerQuery.eval left.rows right.rows do
    fail "live left-outer-join left-predicate pushdown changed semantics"
  unless outerQuery.evalPlanned left right == [[
      .integer ⟨1, by decide, by decide⟩,
      .text ⟨[108, 101, 102, 116, 32, 111, 110, 101], by decide⟩,
      .null]] do
    fail "live left-predicate pushdown lost the unmatched outer row"

def expectRecursivePhysicalPageBTree : IO Unit := do
  let payload := String.mk (List.replicate 900 'p')
  let values := String.intercalate ","
    ((List.range 60).map fun offset =>
      let id := offset + 1
      s!"({id},'{payload}{id}')")
  let sql := s!"
    CREATE TABLE deep_pages(id INTEGER PRIMARY KEY,value TEXT NOT NULL);
    CREATE TABLE auxiliary(id INTEGER PRIMARY KEY,label TEXT NOT NULL);
    CREATE INDEX auxiliary_label ON auxiliary(label);
    INSERT INTO deep_pages VALUES {values};
    INSERT INTO auxiliary VALUES(1,'one'),(2,'two');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"recursive physical setup failed: {message}"
  let table ← match state.database.findTable? "deep_pages" with
    | some table => pure table
    | none => fail "recursive physical setup lost its table"
  let leaves ← match CoreFile.tableLeaves table with
    | some leaves => pure leaves
    | none => fail "recursive physical setup could not encode its leaf cells"
  let plan ← match RecursivePageBTree.build leaves with
    | some plan => pure plan
    | none => fail "recursive physical page planner rejected nonempty leaves"
  unless plan.height >= 3 && plan.checkBalanced &&
      plan.toCells == leaves.flatten do
    fail "recursive physical page planner did not build a balanced deep tree"
  let image ← match RecursivePageBTree.encode state.database with
    | some image => pure image
    | none => fail "recursive physical encoder rejected supported tables"
  unless image.pageCount > plan.pageCount + 2 do
    fail "recursive physical image did not allocate later table/index roots"
  let reopened ← match CoreDecode.decode image.fileBytes with
    | some database => pure database
    | none => fail "general decoder rejected an arbitrary-depth table tree"
  unless reopened.Equiv state.database do
    fail "arbitrary-depth table encoding changed the logical database"
  let path : System.FilePath := ".lake/build/sqleanite-recursive-pages.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*) FROM deep_pages; SELECT count(*) FROM auxiliary; SELECT name FROM sqlite_master WHERE type='index';"] }
  unless output.exitCode == 0 &&
      output.stdout == "ok\n60\n2\nauxiliary_label\n" do
    fail s!"sqlite3 rejected the arbitrary-depth table tree: {output.stderr}{output.stdout}"

end SQLeanite.Tests
