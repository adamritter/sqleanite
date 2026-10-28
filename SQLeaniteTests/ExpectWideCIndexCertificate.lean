import SQLeaniteTests.ExpectPhysicalIndexTraversal
import SQLeaniteTests.ExpectPhysicalMVPTableBTree

namespace SQLeanite.Tests
open SQLeanite

def expectWideCIndexCertificate : IO Unit := do
  let path : System.FilePath := ".lake/build/sqleanite-wide-c-index.db"
  let paths : CoreFileAdapter.Paths := {
    main := path
    journal := ".lake/build/sqleanite-wide-c-index.db-journal" }
  if ← path.pathExists then IO.FS.removeFile path
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  let created ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString,
      "PRAGMA page_size=4096; VACUUM; CREATE TABLE wide(id INTEGER PRIMARY KEY,score INTEGER NOT NULL,payload TEXT NOT NULL); WITH RECURSIVE n(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM n WHERE x<4000) INSERT INTO wide SELECT x,x*10,printf('payload-%d',x) FROM n; CREATE INDEX wide_score ON wide(score); CREATE TABLE mixed(id INTEGER PRIMARY KEY,v); INSERT INTO mixed VALUES(1,NULL),(2,5),(3,5.5),(4,'five'),(5,x'05'); CREATE INDEX mixed_v ON mixed(v);"] }
  unless created.exitCode == 0 do
    fail s!"sqlite3 could not create a wide index: {created.stderr}"
  let database ← CoreFileAdapter.reopen paths
  let attachedTable ← match database.findTableMember? "wide" with
    | some table => pure table
    | none => fail "general decoder lost the C-produced wide table"
  let table := attachedTable.val
  let index ← match table.indexes.find? (·.name == "wide_score") with
    | some index => pure index
    | none => fail "general decoder lost the C-produced wide index"
  let certificates ←
    CoreFileAdapter.loadIntegerIndexCertificates paths database
  let stored ← match certificates.find? fun stored =>
      stored.table.schema.name == "wide" && stored.index.name == "wide_score" with
    | some stored => pure stored
    | none => fail "wide C-produced index did not receive a certificate"
  match stored.certificate with
  | .general _ => pure ()
  | .generated _ =>
      fail "wide C-produced index unexpectedly used the generated 2-3 decoder"
  | .allValues _ =>
      fail "integer-only wide index received a conservative mixed certificate"
  | .text _ =>
      fail "integer-only wide index received a text certificate"
  let target : Core.Value := .integer ⟨20000, by decide, by decide⟩
  let query : Core.Query := {
    columns := [0, index.column]
    predicate := some (.equal index.column target) }
  let certified ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates certificates table
        attachedTable.property query with
    | some certified => pure certified
    | none => fail "wide C-produced index fell back to a full query"
  match certified.result.rows with
  | [[.integer id, .integer score]] =>
      unless id.value == 2000 && score.value == 20000 do
        fail "wide C-produced certificate returned the wrong row"
  | _ => fail "wide C-produced certificate returned the wrong result shape"
  let attachedMixedTable ← match database.findTableMember? "mixed" with
    | some table => pure table
    | none => fail "general decoder lost the mixed-storage table"
  let mixedTable := attachedMixedTable.val
  let mixedIndex ← match mixedTable.indexes.find? (·.name == "mixed_v") with
    | some index => pure index
    | none => fail "general decoder lost the mixed-storage index"
  let mixedStored ← match certificates.find? fun stored =>
      stored.table.schema.name == "mixed" && stored.index.name == "mixed_v" with
    | some stored => pure stored
    | none => fail "mixed-storage index did not receive an exact certificate"
  match mixedStored.certificate with
  | .allValues _ => pure ()
  | _ => fail "mixed-storage index received an invalid ordered certificate"
  let textTarget ← match mixedTable.rows.find? (·.rowid.value == 4) with
    | some row => pure (row.value mixedIndex.column)
    | none => fail "mixed-storage test lost its text row"
  let mixedQuery : Core.Query := {
    columns := [0]
    predicate := some (.equal mixedIndex.column textTarget) }
  let mixedCertified ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates certificates mixedTable
        attachedMixedTable.property mixedQuery with
    | some certified => pure certified
    | none => fail "mixed-storage equality query fell back to a full plan"
  match mixedCertified.result.rows with
  | [[.integer id]] =>
      unless id.value == 4 do
        fail "mixed-storage certificate returned the wrong equality row"
  | _ => fail "mixed-storage certificate returned the wrong equality shape"
  let mixedRange : Core.Query := {
    columns := [0]
    predicate := some (.compare .greaterEqual mixedIndex.column textTarget) }
  let rangeCertified ← match
      CoreFileAdapter.lookupCertifiedIndexCandidates certificates mixedTable
        attachedMixedTable.property mixedRange with
    | some certified => pure certified
    | none => fail "mixed-storage range query fell back to a full plan"
  unless rangeCertified.result.rows ==
      mixedRange.eval mixedTable.rows do
    fail "mixed-storage exact certificate changed range semantics"

def expectCoreFreelistShrink : IO Unit := do
  let payload := String.mk (List.replicate 96 'f')
  let values := String.intercalate ","
    ((List.range 128).map fun offset =>
      let id := offset + 1
      s!"({id},'{payload}{id}')")
  let setupSQL := s!"
    CREATE TABLE shrinking(id INTEGER PRIMARY KEY,value TEXT NOT NULL);
    CREATE INDEX shrinking_value ON shrinking(value);
    INSERT INTO shrinking VALUES {values};"
  let (largeState, _) ← match CoreSQL.execute Core.State.empty setupSQL with
    | .ok outcome => pure outcome
    | .error message => fail s!"Core freelist setup failed: {message}"
  let path : System.FilePath := ".lake/build/sqleanite-core-freelist.db"
  let paths : CoreFileAdapter.Paths := {
    main := path
    journal := ".lake/build/sqleanite-core-freelist.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  CoreFileAdapter.create .system paths largeState.database
  let oldBytes ← IO.FS.readBinFile path
  let oldPages := oldBytes.size / PhysicalCodec.pageSize
  let validatedBefore ← match ← CoreFileAdapter.loadOpenState paths with
    | some value => pure value
    | none => fail "full-chunk index setup did not validate"
  let (insertedState, _) ← match CoreSQL.execute largeState
      "INSERT INTO shrinking VALUES(129,'split');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"split-reuse insert failed: {message}"
  let insertedDelta ← match CoreChunkPageDelta.updateStateCandidate?
      validatedBefore.state insertedState.database with
    | some value => pure value
    | none => fail "full-chunk insert did not produce a physical delta"
  unless insertedDelta.after.nextPage == validatedBefore.state.nextPage &&
      insertedDelta.table.freedPageNumbers.isEmpty do
    fail "split insertion did not recycle the pages released by its old chunk"
  let (smallState, _) ← match CoreSQL.execute largeState
      "DELETE FROM shrinking WHERE id>1;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"Core freelist delete failed: {message}"
  let validated ← match ← CoreFileAdapter.loadOpenState paths with
    | some value => pure value
    | none => fail "indexed shrink did not produce a validated physical state"
  let deltaResult : { delta : CoreChunkPageDelta.StateDelta //
      CoreChunkPageDelta.updateStateCandidate? validated.state
        smallState.database = some delta } ←
    match candidate : CoreChunkPageDelta.updateStateCandidate?
        validated.state smallState.database with
    | some value =>
        pure (⟨value, candidate⟩ : { delta : CoreChunkPageDelta.StateDelta //
          CoreChunkPageDelta.updateStateCandidate? validated.state
            smallState.database = some delta })
    | none => fail "indexed shrink did not produce a proof-carrying table delta"
  let delta := deltaResult.val
  have canonicalCandidate :
      CoreChunkPageDelta.updateStateCandidate? delta.before
        delta.after.database = some delta := by
    have endpoints := CoreChunkPageDelta.updateStateCandidate?_endpoints
      deltaResult.property
    rw [endpoints.1, endpoints.2]
    exact deltaResult.property
  if delta.table.tablePagesSufficient then
    fail "changed index was incorrectly treated as an unchanged page image"
  let input ← IO.FS.readBinFile path
  let prepared ← match CoreFileAdapter.prepareLocalizedLastIndex? validated
      input.data.toList delta canonicalCandidate with
    | some value => pure value
    | none => fail "tail-owned changed index did not produce a localized delta"
  unless prepared.writes.length < oldPages do
    fail "localized indexed shrink rewrote the whole file"
  let connection ← CoreFileEngine.reopen .system paths
  match ← CoreFileEngine.execute connection
      "DELETE FROM shrinking WHERE id>1;" with
  | .error message => fail s!"live localized indexed shrink failed: {message}"
  | .ok _ => pure ()
  let reopened ← CoreFileAdapter.reopen paths
  unless reopened.Equiv smallState.database do
    fail "Core freelist commit changed the logical database"
  let newBytes ← IO.FS.readBinFile path
  unless newBytes.size / PhysicalCodec.pageSize == oldPages do
    fail "Core freelist shrink changed the physical file size"
  let check ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; PRAGMA freelist_count; SELECT count(*) FROM shrinking;"] }
  let lines := check.stdout.trimAscii.toString.splitOn "\n"
  unless check.exitCode == 0 && lines.length == 3 && lines[0]? == some "ok" &&
      lines[2]? == some "1" do
    fail s!"SQLite rejected the Core freelist image: {check.stderr}{check.stdout}"
  let free ← match lines[1]?.bind String.toNat? with
    | some count => pure count
    | none => fail "SQLite did not report the Core freelist count"
  unless 0 < free do
    fail "Core shrink did not publish any pages on the freelist"

def expectCoreDirtyPageCommit : IO Unit := do
  let payload := String.mk (List.replicate 96 'd')
  let values := String.intercalate ","
    ((List.range 100).map fun offset => s!"({offset + 1},'{payload}')")
  let setup := s!"CREATE TABLE dirty_rows(
      id INTEGER PRIMARY KEY,payload TEXT NOT NULL);
    INSERT INTO dirty_rows VALUES {values};"
  let (oldState, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok outcome => pure outcome
    | .error message => fail s!"dirty-page setup failed: {message}"
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-dirty-pages.db"
    journal := ".lake/build/sqleanite-dirty-pages.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  CoreFileAdapter.create .system paths oldState.database
  let oldBytes ← IO.FS.readBinFile paths.main
  let oldPages := oldBytes.size / PhysicalCodec.pageSize
  let replacement := String.mk (List.replicate 96 'e')
  let (newState, _) ← match CoreSQL.execute oldState
      s!"UPDATE dirty_rows SET payload='{replacement}' WHERE id=50;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"dirty-page update failed: {message}"
  let physical ← match ← CoreFileAdapter.loadPageState paths oldState.database with
    | some state => pure state
    | none => fail "stable physical image did not load into its proved representation"
  let (bulkUpdated, _) ← match CoreSQL.execute oldState
      s!"UPDATE dirty_rows SET payload='{replacement}' WHERE id>=40;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"bulk dirty-page update failed: {message}"
  let bulkUpdateDelta ← match CoreChunkPageDelta.updateState?
      physical bulkUpdated.database with
    | some value => pure value
    | none => fail "same-key bulk update did not produce a proved page delta"
  unless bulkUpdateDelta.after.database.Equiv bulkUpdated.database do
    fail "same-key bulk update delta changed the represented database"
  let (bulkDeleted, _) ← match CoreSQL.execute oldState
      "DELETE FROM dirty_rows WHERE id>=40;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"bulk dirty-page delete failed: {message}"
  let bulkDeleteDelta ← match CoreChunkPageDelta.updateState?
      physical bulkDeleted.database with
    | some value => pure value
    | none => fail "bulk retain did not produce a proved page delta"
  unless bulkDeleteDelta.after.database.Equiv bulkDeleted.database do
    fail "bulk retain delta changed the represented database"
  unless bulkDeleteDelta.table.after.tree.root.pageIds.Pairwise
      (fun left right => left ≠ right) &&
      bulkDeleteDelta.table.freedPageNumbers.Pairwise
        (fun left right => left ≠ right) &&
      !bulkDeleteDelta.table.freedPageNumbers.any
        bulkDeleteDelta.table.after.tree.root.pageIds.contains do
    fail "bulk retain duplicated or freed an active persistent page ID"
  let delta ← match CoreChunkPageDelta.updateState? physical newState.database with
    | some delta => pure delta
    | none => fail "single-row update did not produce a proved page delta"
  let writes ← match CoreChunkPageDelta.writes delta.table with
    | some writes => pure writes
    | none => fail "proved page delta contained an invalid page number"
  let before ← match CoreChunkPageDelta.beforeWrites delta.table with
    | some writes => pure writes
    | none => fail "proved before-image path contained an invalid page number"
  let committed ← match ← CoreFileAdapter.commitLocalizedCertified
      .system paths before writes with
    | some committed => pure committed
    | none => fail "on-disk pages did not match the proved before-image"
  have _traceExact : committed.requests =
      CoreFileAdapter.preparedCommitPlan committed.journal
        committed.prepared.writes := committed.trace_eq
  let plan := committed.requests
  -- Materialize the persistent protocol's crash checkpoint after the new main
  -- pages reached disk but before the active journal was retired. The live
  -- recovery path must restore the exact old logical database and then leave
  -- the retained inode in its non-hot inactive state.
  let encodableJournal ← match
      PhysicalJournalCodec.ofJournal? committed.journal with
    | some value => pure value
    | none => fail "localized recovery journal exceeded its encoded bounds"
  let persistentJournal ← match
      PhysicalJournalCodec.ofEncodable? encodableJournal with
    | some value => pure value
    | none => fail "localized recovery journal exceeded its persistent bounds"
  IO.FS.writeBinFile paths.journal
    (PhysicalJournalCodec.encodePersistentActiveBytes persistentJournal)
  CoreFileAdapter.recoverInPlace .system paths
  let recoveredOld ← CoreFileAdapter.reopen paths
  unless recoveredOld.Equiv oldState.database do
    fail "persistent active journal did not restore the old Core database"
  let retiredJournal ← IO.FS.readBinFile paths.journal
  match PhysicalJournalCodec.decodePersistent retiredJournal.data.toList with
  | some none => pure ()
  | _ => fail "persistent recovery did not retire the journal inode"
  unless (← CoreFileAdapter.commitLocalizedCertified
      .system paths before writes).isSome do
    fail "localized commit did not replay after persistent recovery"
  let (deletedState, _) ← match CoreSQL.execute newState
      "DELETE FROM dirty_rows WHERE id=51;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"dirty-page delete failed: {message}"
  let deletedDelta ← match CoreChunkPageDelta.updateState?
      delta.after deletedState.database with
    | some value => pure value
    | none => fail "single-row delete did not produce a proved page delta"
  let deletedBefore ← match CoreChunkPageDelta.beforeWrites deletedDelta.table with
    | some value => pure value
    | none => fail "delete before-image contained page zero"
  let deletedWrites ← match CoreChunkPageDelta.writes deletedDelta.table with
    | some value => pure value
    | none => fail "delete delta contained page zero"
  unless (← CoreFileAdapter.commitLocalized .system paths deletedBefore
      deletedWrites).isSome do
    fail "delete pages did not match their proved before-image"
  let (insertedState, _) ← match CoreSQL.execute deletedState
      s!"INSERT INTO dirty_rows VALUES(101,'{payload}');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"dirty-page insert failed: {message}"
  let insertedDelta ← match CoreChunkPageDelta.updateState?
      deletedDelta.after insertedState.database with
    | some value => pure value
    | none => fail "single-row insert did not produce a proved page delta"
  let insertedBefore ← match CoreChunkPageDelta.beforeWrites insertedDelta.table with
    | some value => pure value
    | none => fail "insert before-image contained page zero"
  let insertedWrites ← match CoreChunkPageDelta.writes insertedDelta.table with
    | some value => pure value
    | none => fail "insert delta contained page zero"
  unless (← CoreFileAdapter.commitLocalized .system paths insertedBefore
      insertedWrites insertedDelta.after.freePages).isSome do
    fail "insert pages did not match their proved before-image"
  -- Fill the final chunk and force an identified leaf/interior split.  The
  -- writer may recycle released identities or append genuinely new pages; in
  -- either case the localized image must remain readable by stock SQLite.
  let mut splitLogical := insertedState
  let mut splitPhysical := insertedDelta.after
  for offset in List.range 12 do
    let rowid := 102 + offset
    let (nextLogical, _) ← match CoreSQL.execute splitLogical
        s!"INSERT INTO dirty_rows VALUES({rowid},'{payload}');" with
      | .ok outcome => pure outcome
      | .error message => fail s!"split insert {rowid} failed: {message}"
    let nextDelta ← match CoreChunkPageDelta.updateState?
        splitPhysical nextLogical.database with
      | some value => pure value
      | none => fail s!"split insert {rowid} did not produce a proved delta"
    let nextBefore ← match CoreChunkPageDelta.beforeWrites nextDelta.table with
      | some value => pure value
      | none => fail s!"split insert {rowid} before-image contained page zero"
    let nextWrites ← match CoreChunkPageDelta.writes nextDelta.table with
      | some value => pure value
      | none => fail s!"split insert {rowid} delta contained page zero"
    unless (← CoreFileAdapter.commitLocalized .system paths nextBefore
        nextWrites nextDelta.after.freePages).isSome do
      fail s!"split insert {rowid} pages did not match their before-images"
    splitLogical := nextLogical
    splitPhysical := nextDelta.after
  let mut mergedLogical := splitLogical
  let mut mergedPhysical := splitPhysical
  -- Remove both chunks produced by the split.  Removing only the new right
  -- chunk can leave a valid one-entry leaf and therefore has no physical page
  -- to free; removing 97..113 forces borrow/merge and exercises the live
  -- SQLite freelist encoding.
  for offset in List.range 17 do
    let rowid := 97 + offset
    let (nextLogical, _) ← match CoreSQL.execute mergedLogical
        s!"DELETE FROM dirty_rows WHERE id={rowid};" with
      | .ok outcome => pure outcome
      | .error message => fail s!"merge delete {rowid} failed: {message}"
    let nextDelta ← match CoreChunkPageDelta.updateState?
        mergedPhysical nextLogical.database with
      | some value => pure value
      | none =>
          let detail := match mergedPhysical.tables.head?,
              nextLogical.database.tables.head? with
            | some oldTable, some nextTable =>
                let deleted := CoreChunkPageDelta.firstDeleted
                  oldTable.table.rows nextTable.rows
                let entry := deleted.bind fun row =>
                  CoreChunkPageDelta.findChunkFor? row.treeKey oldTable.tree.root
                let direct := deleted.bind fun row =>
                  CoreChunkPageDelta.delete? oldTable mergedPhysical.nextPage row
                    nextTable
                let deletedIds := deleted.map fun (row : Core.Row) => row.rowid.value
                let entryRows := entry.map fun
                  (e : PagedBTree.Entry CoreChunkPageState.Chunk) =>
                    (e.1, e.2.map fun (row : Core.Row) => row.rowid.value)
                let allEntries := oldTable.tree.root.erase.toList.map fun
                    (e : PagedBTree.Entry CoreChunkPageState.Chunk) =>
                  let first := e.2.head?.map fun (row : Core.Row) => row.rowid.value
                  let last := e.2.getLast?.map fun (row : Core.Row) => row.rowid.value
                  s!"{e.1}:{first.map (fun (value : Int) => toString value)}-{last.map (fun (value : Int) => toString value)}/{e.2.length}"
                s!"deleted={repr deletedIds}, entry={repr entryRows}, direct={direct.isSome}, entries={String.intercalate ";" allEntries}"
            | _, _ => "missing table"
          fail s!"merge delete {rowid} did not produce a proved delta: {detail}"
    let nextBefore ← match CoreChunkPageDelta.beforeWrites nextDelta.table with
      | some value => pure value
      | none => fail s!"merge delete {rowid} before-image contained page zero"
    let nextWrites ← match CoreChunkPageDelta.writes nextDelta.table with
      | some value => pure value
      | none => fail s!"merge delete {rowid} delta contained page zero"
    unless (← CoreFileAdapter.commitLocalized .system paths nextBefore
        nextWrites nextDelta.after.freePages).isSome do
      fail s!"merge delete {rowid} pages did not match their before-images"
    let checkpoint ← CoreFileAdapter.reopen paths
    unless checkpoint.Equiv nextLogical.database do
      fail s!"merge delete {rowid} did not preserve the represented database; writes={nextWrites.map (·.pageId)}, freed={nextDelta.table.freedPageNumbers}"
    mergedLogical := nextLogical
    mergedPhysical := nextDelta.after
  let reopened ← CoreFileAdapter.reopen paths
  let reloaded ← match ← CoreFileAdapter.loadPageState paths reopened with
    | some value => pure value
    | none => fail "merged physical tree or freelist did not reload"
  let grownBytes ← paths.main.metadata
  let grownPages := grownBytes.byteSize.toNat / PhysicalCodec.pageSize
  let dirtyPages := plan.filterMap fun request => match request with
    | .pwriteMain write => some write.pageId
    | _ => none
  unless reopened.Equiv mergedLogical.database &&
      reloaded.database.Equiv mergedLogical.database && oldPages ≤ grownPages &&
      0 < dirtyPages.length &&
      dirtyPages.length < oldPages do
    fail s!"localized commit wrote {dirtyPages.length} of {oldPages} pages"
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*),length(payload) FROM dirty_rows WHERE payload LIKE 'e%'; SELECT count(*) FROM dirty_rows; SELECT count(*) FROM dirty_rows WHERE id=105;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n1|96\n95\n0\n" do
    fail s!"SQLite rejected the dirty-page commit: {output.stderr}{output.stdout}"

def expectHeaderMetadata : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'a'),(2,'b');CREATE INDEX t_v ON t(v);" with
    | .ok result => pure result
    | .error message => fail message
  let image ← match CorePageCodec.encodeBulk state.database with
    | some image => pure image
    | none => fail "metadata: encode failed"
  let base ← match CoreMultiFreelist.ofImageTotal? image (image.pageCount + 2) with
    | some layout => pure layout
    | none => fail "metadata: layout failed"
  let metadata : CoreMultiFreelist.HeaderMetadata := {
    applicationId := ⟨4294967295, by omega⟩
    userVersion := ⟨42, by omega⟩ }
  let layout := { base with metadata }
  let (header, _) ← match FileFormat.decodeDatabaseHeader layout.paddedImage.fileBytes with
    | some result => pure result
    | none => fail "metadata: header failed"
  unless header.applicationId.val == 4294967295 && header.userVersion.val == 42 &&
      header.databaseSizePages.val == image.pageCount + 2 && header.freelistPageCount.val == 2 do
    fail "metadata fields or geometry changed"
  unless layout.schemaPage.bytes.drop 100 == layout.firstPage.bytes.drop 100 do
    fail "metadata changed the schema B-tree body"
  let decoded ← match CoreDecode.decode layout.paddedImage.fileBytes with
    | some database => pure database
    | none => fail "metadata: padded image failed to decode"
  unless decoded.contents == state.database.contents do fail "metadata changed logical rows"
  unless !CoreFile.hasGeneratedImageStamp header do fail "nondefault metadata entered the generated fast path"
  let zeroApp := { header with applicationId := ⟨0, by omega⟩ }
  unless !CoreFile.hasGeneratedImageStamp zeroApp do fail "nonzero user version entered the generated fast path"

end SQLeanite.Tests
