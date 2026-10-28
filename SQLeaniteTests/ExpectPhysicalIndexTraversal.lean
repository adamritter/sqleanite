import SQLeaniteTests.ExpectGeneralMVPFileInterop

namespace SQLeanite.Tests
open SQLeanite

def expectPhysicalIndexTraversal : IO Unit := do
  let payload := String.mk (List.replicate 96 'x')
  let values := String.intercalate ","
    ((List.range 120).map fun offset =>
      let id := offset + 1
      s!"({id},'{payload}{id}',{id * 10},'old')")
  let sql := s!"
    CREATE TABLE indexed(id INTEGER PRIMARY KEY,value TEXT NOT NULL,score INTEGER NOT NULL,note TEXT NOT NULL);
    CREATE INDEX indexed_value ON indexed(value);
    CREATE INDEX indexed_score ON indexed(score);
    INSERT INTO indexed VALUES {values};
    CREATE TABLE signed_keys(id INTEGER PRIMARY KEY,value TEXT NOT NULL);
    INSERT INTO signed_keys VALUES(4,'positive');
    CREATE TABLE join_probe(id INTEGER PRIMARY KEY,label TEXT NOT NULL);
    INSERT INTO join_probe VALUES(2,'two'),(3,'three');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"physical index setup failed: {message}"
  let attachedTable ← match state.database.findTableMember? "indexed" with
    | some table => pure table
    | none => fail "physical index setup lost its table"
  let table := attachedTable.val
  let index ← match table.indexes.find? (·.name == "indexed_value") with
    | some index => pure index
    | none => fail "physical index setup lost its index"
  let integerIndex ← match table.indexes.find? (·.name == "indexed_score") with
    | some index => pure index
    | none => fail "physical index setup lost its integer index"
  let threshold := (table.rows[60]?).map (fun row => row.value index.column)
    |>.getD .null
  let primaryValue := (table.rows[60]?).map (fun row => row.value 0)
    |>.getD .null
  let primaryQuery : Core.Query := {
    columns := [0, 1]
    predicate := some (.equal table.schema.primaryKey primaryValue) }
  match table.chooseAccessPath primaryQuery.predicate with
  | .primaryKey rowid =>
      unless rowid.value == 61 &&
          (table.plannedRows primaryQuery).map (fun row => row.rowid.value) == [61] do
        fail "primary-key planner returned the wrong routed row"
  | _ => fail "cost-aware planner did not select routed primary lookup"
  unless primaryQuery.eval (table.plannedRows primaryQuery) ==
      primaryQuery.eval table.rows do
    fail "routed primary-key lookup changed query semantics"
  let rangeQuery : Core.Query := {
    columns := [0]
    predicate := some (.compare .greaterEqual index.column threshold) }
  match table.chooseAccessPath rangeQuery.predicate with
  | .rangeIndex chosen =>
      unless chosen == index do
        fail "cost-aware range planner selected the wrong index"
  | _ => fail "cost-aware planner did not select a range index"
  unless rangeQuery.eval (table.plannedRows rangeQuery) ==
      rangeQuery.eval table.rows do
    fail "range index plan changed query semantics"
  let indexLeaves ← match CoreFile.indexLeaves table index with
    | some leaves => pure leaves
    | none => fail "physical index cells did not paginate"
  let indexPlan ← match RecursivePageBTree.buildIndex indexLeaves with
    | some plan => pure plan
    | none => fail "recursive physical index planner rejected valid leaves"
  unless indexPlan.height >= 2 && indexPlan.checkBalanced &&
      indexPlan.toCells == indexLeaves.flatten do
    fail "recursive physical index promotion changed contents or balance"
  let image ← match RecursivePageBTree.encode state.database with
    | some image => pure image
    | none => fail "physical index encoder rejected a multipage index"
  unless image.pages.length > 6 do
    fail "physical index test did not force multiple table and index leaves"
  let reopened ← match CoreDecode.decode image.fileBytes with
    | some database => pure database
    | none => fail "physical index traversal rejected its own multipage tree"
  unless reopened.Equiv state.database do
    fail "physical index traversal changed the indexed database"
  let physicalPages := CoreDecode.pages image.pageCount image.fileBytes
  let source := CoreDecode.PageSource.ofList physicalPages
  let catalog ← match physicalPages.head?.bind CoreDecode.decodeCatalog with
    | some catalog => pure catalog
    | none => fail "physical index certificate could not decode the catalog"
  let integerCatalog ← match catalog.find? fun entry =>
      entry.kind == "index" && entry.name == integerIndex.name with
    | some entry => pure entry
    | none => fail "physical index certificate lost the integer root"
  unless integerCatalog.sql.bind CanonicalIndexSQL.parseIntegerCertified |>.isSome do
    fail "integer-only physical index lost its persisted catalog certificate"
  let textCatalog ← match catalog.find? fun entry =>
      entry.kind == "index" && entry.name == index.name with
    | some entry => pure entry
    | none => fail "physical index certificate lost the text root"
  unless (textCatalog.sql.bind
      CanonicalIndexSQL.parseIntegerCertified).isNone do
    fail "mixed/text physical index received an integer-only certificate"
  unless (textCatalog.sql.bind
      CanonicalIndexSQL.parseTextCertified).isSome do
    fail "generated TEXT index lost its persisted routing certificate"
  let expected := CoreDecode.expectedIndexEntries table integerIndex
  let integerCertificate ← match CoreDecode.certifyIntegerIndex source
      (physicalPages.length + 1) integerCatalog.rootPage expected with
    | some certificate => pure certificate
    | none => fail "proof-producing integer index certification failed"
  let integerTarget := (table.rows[60]?).map
    (fun row => row.value integerIndex.column) |>.getD .null
  unless CoreDecode.lookupIndexValueFrom source integerTarget
      (physicalPages.length + 1) integerCatalog.rootPage ==
        some (expected.filter (fun entry => entry.matchesValue integerTarget)) do
    fail "certified integer equality traversal was not exact"
  unless CoreDecode.lookupIndexRangeFrom source .greaterEqual integerTarget
      (physicalPages.length + 1) integerCatalog.rootPage ==
        some (expected.filter
          (fun entry => entry.matchesRange .greaterEqual integerTarget)) do
    fail "certified integer range traversal was not exact"
  let textExpected := CoreDecode.expectedIndexEntries table index
  unless CoreDecode.indexPrefixFrom source 80 (physicalPages.length + 1)
      textCatalog.rootPage == some (textExpected.take 80) do
    fail "multi-leaf index cursor did not return the exact promoted-key prefix"
  let integerQuery : Core.Query := {
    columns := [0, integerIndex.column]
    predicate := some (.equal integerIndex.column integerTarget) }
  let retainedCertificates := CoreFileAdapter.certifyIntegerIndexes physicalPages
    catalog state.database
  let updatedState ← match CoreSQL.execute state
      "UPDATE indexed SET note='new' WHERE id=61;" with
    | .ok (updated, _) => pure updated
    | .error message => fail s!"certificate retarget setup failed: {message}"
  let attachedUpdatedTable ← match
      updatedState.database.findTableMember? "indexed" with
    | some updated => pure updated
    | none => fail "certificate retarget lost its logical table"
  let updatedTable := attachedUpdatedTable.val
  let retargeted := CoreFileAdapter.retargetIntegerIndexCertificates
    retainedCertificates updatedState.database
  let retargetQuery : Core.Query := {
    columns := [0, 3]
    predicate := some (.equal integerIndex.column integerTarget) }
  let retargetLookup ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates retargeted updatedTable
        attachedUpdatedTable.property retargetQuery with
    | some lookup => pure lookup
    | none => fail "index-preserving update discarded its certificate"
  match retargetLookup.result.rows with
  | [[.integer id, .text note]] =>
      unless id.value == 61 && note.bytes == "new".toUTF8.toList do
        fail "retargeted certificate resolved rows from the old primary tree"
  | _ => fail "retargeted certificate returned the wrong result shape"
  let certifiedCandidates ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates retainedCertificates table
        attachedTable.property integerQuery with
    | some lookup => pure lookup
    | none => fail "integer index certificate was not reusable by a query"
  unless certifiedCandidates.candidates.map (·.rowid.value) == [61] do
    fail "certified candidate resolution changed primary-tree row order"
  let path : System.FilePath := ".lake/build/sqleanite-recursive-index.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let paths : CoreFileAdapter.Paths := {
    main := path
    journal := ".lake/build/sqleanite-recursive-index.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  let some geometry ← CoreFileAdapter.readGeneratedFileGeometry paths |
    fail "cached primary setup lost generated geometry"
  let primaryKeys : List Core.Integer :=
    [⟨-1, by decide, by decide⟩] ++
      (List.range 122).filterMap CoreFile.signedNat?
  for capacity in [0, 1, 512] do
    let cache ← CoreFileAdapter.PageReadCache.create capacity
    -- Visit multiple leaves, hits and both sides of the key range, then
    -- revisit them in reverse. A disabled or saturated cache must be exact.
    for key in primaryKeys ++ primaryKeys.reverse do
      let some actual ← CoreFileAdapter.lookupGeneratedPrimaryRowWith geometry
          paths "indexed" table.schema cache key |
        fail "cached primary reader rejected a valid tree"
      let expected := table.rows.find? (fun row => row.rowid = key)
      unless actual.map (·.values) == expected.map (·.values) do
        fail s!"cached primary reader changed row {key.value} at capacity {capacity}"
    unless (← cache.pages.get).size ≤ capacity do
      fail "primary reader exceeded the page-cache bound"
    unless (← cache.tableCursors.get).size ≤ capacity do
      fail "primary reader exceeded the cursor-cache bound"
    unless (← cache.tableViews.get).size ≤ capacity do
      fail "primary reader exceeded the batch-wide checked-page cache bound"
    for (_, cursor) in (← cache.tableCursors.get).toList do
      unless (← cursor.views.get).size ≤ capacity do
        fail "primary reader exceeded the checked-page cache bound"
    unless (← CoreFileAdapter.lookupGeneratedPrimaryRowWith geometry paths
        "join_probe" table.schema cache ⟨2, by decide, by decide⟩).isNone do
      fail "primary reader accepted a schema from another table"
  for capacity in [1, 2] do
    let shared ← CoreFileAdapter.PageReadCache.create capacity
    for name in ["indexed", "signed_keys", "indexed", "signed_keys"] do
      let some schema := geometry.tableSchema? name | fail "shared-view test lost schema"
      for key in [1, 4, 120] do
        let some integer := CoreFile.signedNat? key | fail "shared-view key out of range"
        unless (← CoreFileAdapter.lookupGeneratedPrimaryRowWith geometry paths
            name schema shared integer).isSome do
          fail "shared view cache rejected a valid cross-table read"
      unless (← shared.tableViews.get).size ≤ capacity do
        fail "view capacity multiplied by the number of table cursors"
  let primaryBatch := "SELECT id,value FROM indexed WHERE id=1;
    SELECT id,value FROM signed_keys WHERE id=4;
    SELECT id,value FROM indexed WHERE id=120;
    SELECT id,value FROM indexed WHERE id=999;
    SELECT id,value FROM indexed WHERE id=1;"
  let expectedBatch ← match CoreSQL.execute state primaryBatch with
    | .ok (_, results) => pure results
    | .error message => fail s!"primary batch reference failed: {message}"
  match ← CoreLazyFileEngine.execute? paths primaryBatch with
  | some (.ok actual) =>
      unless actual.map (·.rows) == expectedBatch.map (·.rows) do
        fail "cached primary batch changed projection, ordering, or table identity"
  | _ => fail "primary batch missed the generated fast path"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,value FROM indexed WHERE id=999;" with
  | some (.ok [{ rows := [], changes := _ }]) => pure ()
  | _ => fail "generated-image primary miss did not stay page-directed"
  let coldIndexQuery : Core.Query := {
    columns := [0, integerIndex.column]
    predicate := some (.equal integerIndex.column integerTarget) }
  let coldIndexLookup ← match ←
      CoreFileAdapter.lookupGeneratedIndexCandidates paths "indexed"
        table.schema coldIndexQuery with
    | some lookup => pure lookup
    | none => fail "generated INTEGER index did not take the cold path"
  unless coldIndexLookup.candidates.map (·.rowid.value) == [61] &&
      coldIndexLookup.pagesRead < image.pages.length do
    fail "cold INTEGER index lookup did not remain page-directed"
  let coldTextQuery : Core.Query := {
    columns := [0, index.column]
    predicate := some (.equal index.column threshold) }
  let coldTextLookup ← match ←
      CoreFileAdapter.lookupGeneratedIndexCandidates paths "indexed"
        table.schema coldTextQuery with
    | some lookup => pure lookup
    | none => fail "generated TEXT index did not take the cold path"
  unless coldTextLookup.candidates.map (·.rowid.value) == [61] &&
      coldTextLookup.pagesRead < image.pages.length do
    fail "cold TEXT index lookup did not remain page-directed"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,score FROM indexed WHERE score=610;" with
  | some (.ok [{ rows := [[.integer id, .integer score]], .. }]) =>
      unless id.value == 61 && score.value == 610 do
        fail "cold secondary equality SELECT returned the wrong row"
  | _ => fail "cold secondary equality SELECT missed the page-directed path"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,score FROM indexed WHERE score>=1190 ORDER BY id;" with
  | some (.ok [{ rows := rows, .. }]) =>
      unless rows == [[.integer ⟨119, by decide, by decide⟩,
          .integer ⟨1190, by decide, by decide⟩],
        [.integer ⟨120, by decide, by decide⟩,
          .integer ⟨1200, by decide, by decide⟩]] do
        fail "cold secondary range SELECT returned the wrong rows"
  | _ => fail "cold secondary range SELECT missed the page-directed path"
  let orderedQuery : Core.Query := {
    columns := [0, index.column]
    orderBy := [(index.column, false)]
    limit := some 5 }
  let orderedPrefix ← match ←
      CoreFileAdapter.lookupGeneratedOrderedPrefix paths "indexed" table.schema
        orderedQuery with
    | some lookup => pure lookup
    | none => fail "generated ORDER BY prefix did not take the cold path"
  let prefixIds := (orderedQuery.selectedRows orderedPrefix.candidates).map
    (fun row => row.rowid.value)
  let expectedIds := (orderedQuery.selectedRows table.rows).map
    (fun row => row.rowid.value)
  unless orderedQuery.eval orderedPrefix.candidates ==
      orderedQuery.eval table.rows && orderedPrefix.candidates.length == 5 do
    fail s!"cold ORDER BY prefix mismatch: candidate ids={repr prefixIds} expected ids={repr expectedIds} reads={orderedPrefix.pagesRead}/{image.pages.length}"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,value FROM indexed ORDER BY value LIMIT 5;" with
  | some (.ok [{ rows := rows, .. }]) =>
      unless rows == orderedQuery.eval table.rows do
        fail "cold ORDER BY LIMIT SELECT returned the wrong rows"
  | _ => fail "cold ORDER BY LIMIT SELECT missed the page-directed path"
  let multiLeafQuery : Core.Query := {
    columns := [0, index.column]
    orderBy := [(index.column, false)]
    limit := some 80 }
  let multiLeafPrefix ← match ←
      CoreFileAdapter.lookupGeneratedOrderedPrefix paths "indexed" table.schema
        multiLeafQuery with
    | some lookup => pure lookup
    | none => fail "multi-leaf ORDER BY prefix missed the cold cursor"
  unless multiLeafPrefix.candidates.length == 80 &&
      multiLeafQuery.eval multiLeafPrefix.candidates ==
        multiLeafQuery.eval table.rows do
    fail "multi-leaf ORDER BY prefix changed query results"
  let primaryRange ← match ← CoreFileAdapter.lookupGeneratedPrimaryRange
      paths "indexed" table.schema .greater ⟨115, by decide, by decide⟩ with
    | some lookup => pure lookup
    | none => fail "generated primary range did not take the cold path"
  unless primaryRange.candidates.map (·.rowid.value) == [116, 117, 118, 119, 120] &&
      primaryRange.pagesRead < image.pages.length do
    fail "cold primary range did not remain separator-directed"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,score FROM indexed WHERE id>115;" with
  | some (.ok [{ rows := rows, .. }]) =>
      unless rows.map (fun row => row[0]?) ==
          [some (.integer ⟨116, by decide, by decide⟩),
           some (.integer ⟨117, by decide, by decide⟩),
           some (.integer ⟨118, by decide, by decide⟩),
           some (.integer ⟨119, by decide, by decide⟩),
           some (.integer ⟨120, by decide, by decide⟩)] do
        fail "cold primary range SELECT returned the wrong rows"
  | _ => fail "cold primary range SELECT missed the page-directed path"
  let joinLookup ← match ← CoreFileAdapter.lookupGeneratedPrimaryJoin paths
      "indexed" "join_probe" with
    | some lookup => pure lookup
    | none => fail "generated primary-key join did not take the cold path"
  unless joinLookup.leftCandidates.map (·.rowid.value) == [1, 2, 3] &&
      joinLookup.rightRows.map (·.rowid.value) == [2, 3] &&
      joinLookup.bound.map (·.value) == some 3 &&
      joinLookup.pagesRead < image.pages.length do
    fail "cold primary-key join did not remain range-directed"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT indexed.id,join_probe.label FROM indexed JOIN join_probe ON indexed.id=join_probe.id;" with
  | some (.ok [{ rows := rows, .. }]) =>
      unless rows ==
          [[.integer ⟨2, by decide, by decide⟩,
            .text ⟨[116, 119, 111], by decide⟩],
           [.integer ⟨3, by decide, by decide⟩,
            .text ⟨[116, 104, 114, 101, 101], by decide⟩]] do
        fail "cold primary-key join returned the wrong rows"
  | _ => fail "cold primary-key join missed the page-directed path"
  let signedMutation ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "INSERT INTO signed_keys VALUES(-7,'negative');"] }
  unless signedMutation.exitCode == 0 do
    fail s!"sqlite3 could not add a negative rowid: {signedMutation.stderr}"
  let primaryLookup ← match ←
      CoreFileAdapter.lookupPrimaryRow paths "indexed"
        ⟨61, by decide, by decide⟩ with
    | some lookup => pure lookup
    | none => fail "cold primary lookup rejected a valid row"
  unless primaryLookup.row.rowid.value == 61 &&
      primaryLookup.pagesRead < image.pages.length do
    fail s!"cold primary lookup visited {primaryLookup.pagesRead} of {image.pages.length} pages"
  let cold ← CoreLazyFileEngine.execute? paths
    "SELECT id,value FROM indexed WHERE id=61;"
  match cold with
  | some (.ok [{ rows := [[.integer id, .text value]], .. }]) =>
      unless id.value == 61 && value.bytes.length == 98 do
        fail "cold primary SELECT returned the wrong row"
  | _ => fail "cold primary SELECT did not use the page-directed path"
  let negativeLookup ← match ←
      CoreFileAdapter.lookupPrimaryRow paths "signed_keys"
        ⟨-7, by decide, by decide⟩ with
    | some lookup => pure lookup
    | none => fail "cold primary lookup rejected a negative rowid"
  unless negativeLookup.row.rowid.value == -7 &&
      negativeLookup.pagesRead < image.pages.length + 2 do
    fail "cold primary lookup changed signed rowid routing"
  match ← CoreLazyFileEngine.execute? paths
      "SELECT id,value FROM signed_keys WHERE id=-7;" with
  | some (.ok [{ rows := [[.integer id, .text value]], .. }]) =>
      unless id.value == -7 && value.bytes == "negative".toUTF8.toList do
        fail "cold primary SELECT changed a negative rowid result"
  | _ => fail "cold primary SELECT did not recognize a negative rowid"
  unless (← CoreLazyFileEngine.execute? paths
      "SELECT id,value FROM indexed WHERE id=999;").isNone do
    fail "C-mutated primary miss bypassed the validating fallback"
  unless (← CoreFileAdapter.lookupGeneratedIndexCandidates paths "indexed"
      table.schema coldIndexQuery).isNone do
    fail "C-mutated index bypassed the generated-image fallback"
  let equalityQuery : Core.Query := {
    columns := [0, 1]
    predicate := some (.equal index.column threshold) }
  let lookup ← match ←
      CoreFileAdapter.lookupIndexCandidates paths table equalityQuery with
    | some lookup => pure lookup
    | none => fail "persisted equality lookup rejected a valid index"
  unless lookup.candidates.length == 1 &&
      lookup.candidates.head?.map (·.rowid.value) == some 61 &&
      lookup.pagesRead < indexPlan.pageCount do
    fail s!"page-directed lookup visited {lookup.pagesRead} of {indexPlan.pageCount} index pages"
  let rangeLookup ← match ←
      CoreFileAdapter.lookupIndexCandidates paths table rangeQuery with
    | some lookup => pure lookup
    | none => fail "persisted range lookup rejected a valid index"
  unless rangeQuery.eval rangeLookup.candidates == rangeQuery.eval table.rows &&
      rangeLookup.pagesRead < indexPlan.pageCount do
    fail s!"page-directed range visited {rangeLookup.pagesRead} of {indexPlan.pageCount} index pages"
  let connection ← CoreFileEngine.reopen .system paths
  let live ← CoreFileEngine.execute connection
    s!"SELECT id,value FROM indexed WHERE value='{payload}61';"
  match live with
  | .ok [{ rows := [[.integer id, .text value]], .. }] =>
      unless id.value == 61 && value.bytes.length == 98 do
        fail "live persisted-index lookup returned the wrong row"
  | _ => fail "live query did not execute through persisted-index candidates"
  let certifiedLive ← CoreFileEngine.execute connection
    "SELECT id,score FROM indexed WHERE score=610;"
  match certifiedLive with
  | .ok [{ rows := [[.integer id, .integer score]], .. }] =>
      unless id.value == 61 && score.value == 610 do
        fail "live certified integer index returned the wrong row"
  | _ => fail "live certified integer index did not execute"
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*) FROM indexed INDEXED BY indexed_value;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n120\n" do
    fail s!"sqlite3 rejected the recursive physical index: {output.stderr}{output.stdout}"

end SQLeanite.Tests
