import SQLeaniteTests.ExpectWideCIndexCertificate

namespace SQLeanite.Tests
open SQLeanite

def expectCoreMultiFreelist : IO Unit := do
  let (state, _) ← match CoreSQL.execute { database := Core.Database.empty }
      "CREATE TABLE multi_free(id INTEGER PRIMARY KEY,value TEXT);
       INSERT INTO multi_free VALUES(1,'kept');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"multi-trunk setup failed: {message}"
  let image ← match RecursivePageBTree.encode state.database with
    | some image => pure image
    | none => fail "multi-trunk setup did not encode"
  let freeCount := 2050
  let total := image.pageCount + freeCount
  let layout ← match CoreMultiFreelist.ofImageTotal? image total with
    | some layout => pure layout
    | none => fail "multi-trunk layout rejected a bounded page count"
  unless layout.pages.length == total && layout.freelistPages.length == freeCount do
    fail "multi-trunk layout emitted the wrong number of pages"
  let path : System.FilePath := ".lake/build/sqleanite-multi-freelist.db"
  IO.FS.writeBinFile path (ByteArray.mk layout.paddedImage.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; PRAGMA freelist_count; SELECT count(*) FROM multi_free;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n2050\n1\n" do
    fail s!"SQLite rejected the verified multi-trunk freelist: {output.stderr}{output.stdout}"

def expectLazyReachablePageDecode : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty "
      CREATE TABLE lazy_rows(id INTEGER PRIMARY KEY,value TEXT NOT NULL);
      CREATE INDEX lazy_value ON lazy_rows(value);
      INSERT INTO lazy_rows VALUES(1,'one'),(2,'two');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"lazy pager setup failed: {message}"
  let image ← match CoreFile.encode state.database with
    | some image => pure image
    | none => fail "lazy pager encoder rejected a small database"
  let layout ← match CoreFreelist.ofImageTotal? image 100 with
    | some layout => pure layout
    | none => fail "lazy pager could not build a bounded padded image"
  let physicalPages := layout.pages.map CoreFile.Page.bytes
  let reads ← IO.mkRef 0
  let source : CoreDecode.IOPageSource := {
    pageCount := physicalPages.length
    readPage := fun pageNumber => do
      let count ← reads.get
      reads.set (count + 1)
      return CoreDecode.page? physicalPages pageNumber }
  let decoded ← match ← CoreDecode.decodeFromIOPageSource source with
    | some database => pure database
    | none => fail "lazy pager rejected reachable table or index pages"
  unless decoded.Equiv state.database do
    fail "lazy pager changed the decoded database"
  let readCount ← reads.get
  unless readCount < physicalPages.length do
    fail "lazy pager requested unreachable freelist pages"

def expectGeneralMVPFileEngine : IO Unit := do
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-general-live.db"
    journal := ".lake/build/sqleanite-general-live.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  let connection ← CoreFileEngine.create .system paths
  let setup ← CoreFileEngine.execute connection "
    BEGIN;
    CREATE TABLE users(id INTEGER PRIMARY KEY,name TEXT NOT NULL);
    CREATE TABLE notes(body TEXT,note_id INTEGER PRIMARY KEY,owner INTEGER NOT NULL);
    CREATE INDEX users_name ON users(name);
    INSERT INTO users VALUES(2,'Ada'),(1,'Lin');
    INSERT INTO notes VALUES('kernel',10,1);
    COMMIT;"
  if let .error message := setup then
    fail s!"general persisted setup failed: {message}"
  let rolledBack ← CoreFileEngine.execute connection "
    BEGIN; INSERT INTO users VALUES(9,'rollback'); ROLLBACK;"
  if let .error message := rolledBack then
    fail s!"general persisted rollback failed: {message}"
  let cInsert ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch",
      "INSERT INTO users VALUES(3,'C'); INSERT INTO notes VALUES('interop',11,3);"] }
  unless cInsert.exitCode == 0 do
    fail s!"C SQLite could not update the generalized live path: {cInsert.stderr}"
  let reopened ← CoreFileEngine.reopen .system paths
  let leanInsert ← CoreFileEngine.execute reopened
    "INSERT INTO users VALUES(4,'Lean');"
  if let .error message := leanInsert then
    fail s!"Lean could not commit after a C-written image: {message}"
  let modified ← CoreFileEngine.execute reopened "
    BEGIN;
    UPDATE users SET name='Lean updated' WHERE id=4;
    DELETE FROM users WHERE id=2;
    DELETE FROM notes WHERE note_id=10;
    COMMIT;"
  if let .error message := modified then
    fail s!"general live UPDATE/DELETE failed: {message}"
  let rejected ← CoreFileEngine.execute reopened
    "UPDATE users SET name=NULL WHERE id=1;"
  if rejected.isOk then
    fail "general live UPDATE admitted a NOT NULL violation"
  let check ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader", "
      PRAGMA integrity_check;
      SELECT id,name FROM users ORDER BY id;
      SELECT note_id,body,owner FROM notes ORDER BY note_id;"] }
  unless check.exitCode == 0 && check.stdout ==
      "ok\n1|Lin\n3|C\n4|Lean updated\n11|interop|3\n" do
    fail s!"general live path failed C/Lean roundtrip: {check.stderr}{check.stdout}"
  let selected ← CoreFileEngine.execute reopened
    "SELECT name,id FROM users ORDER BY id DESC LIMIT 2;"
  match selected with
  | .error message => fail s!"general live SELECT failed: {message}"
  | .ok results =>
      let rows := results.flatMap (·.rows)
      unless rows.length == 2 do
        fail "general live SELECT returned the wrong row count"
  let joined ← CoreFileEngine.execute reopened "
    SELECT users.name,notes.body FROM users
    INNER JOIN notes ON users.id=notes.owner
    WHERE notes.note_id>=11 ORDER BY users.id;"
  match joined with
  | .error message => fail s!"general live INNER JOIN failed: {message}"
  | .ok results =>
      let rows := results.flatMap (·.rows)
      unless rows == [[.text ⟨[67], by decide⟩,
          .text ⟨[105, 110, 116, 101, 114, 111, 112], by decide⟩]] do
        fail "general live INNER JOIN returned the wrong rows"

def expectMVPRecordCells : IO Unit := do
  let rowid : FileFormat.SignedInteger .eight := ⟨7, by decide, by decide⟩
  let text : PhysicalCodec.Text := ⟨[97, 108, 112, 104, 97], by decide⟩
  let row : PhysicalCodec.Row := {
    rowid
    first := .integer ⟨-4, by decide, by decide⟩
    second := .text text }
  match PhysicalCodec.decodeRowCell (row.encodeCell ++ [99]) with
  | some (decoded, [99]) =>
      unless decoded == row do
        fail "MVP table-leaf cell codec changed a logical row"
  | _ => fail "MVP table-leaf cell codec failed"
  let rows := [row, { row with rowid := ⟨8, by decide, by decide⟩, first := .null }]
  unless PhysicalCodec.decodeCells rows.length (PhysicalCodec.encodeCells rows) ==
      some (rows, []) do
    fail "MVP table-leaf cell-list codec failed"

def expectSQLiteFileInterop : IO Unit := do
  let alpha : PhysicalCodec.Text := ⟨[97, 108, 112, 104, 97], by decide⟩
  let beta : PhysicalCodec.Text := ⟨[98, 101, 116, 97], by decide⟩
  let first : PhysicalCodec.Row := {
    rowid := ⟨1, by decide, by decide⟩
    first := .text alpha
    second := .null }
  let second : PhysicalCodec.Row := {
    rowid := ⟨2, by decide, by decide⟩
    first := .integer ⟨-4, by decide, by decide⟩
    second := .text beta }
  let database : PhysicalCodec.Database := {
    rows := [first, second]
    rowidsSorted := by simp [PhysicalCodec.Row.keyLess, first, second]
    pageFits := by
      unfold PhysicalCodec.PageFit PhysicalCodec.cellBytes PhysicalCodec.pageSize
      decide }
  let path : System.FilePath := ".lake/build/sqleanite-mvp-interop.db"
  match PhysicalCodec.decodeFile database.fileBytes with
  | some reopened =>
      unless reopened.rows == database.rows do
        fail "verified MVP file decoder changed the logical rows"
  | none => fail "verified MVP file decoder rejected its own image"
  match PhysicalCodec.decodeStorageImage database.storageImage with
  | some reopened =>
      unless reopened.rows == database.rows do
        fail "verified pager reopen changed the logical rows"
  | none => fail "verified pager reopen rejected its own image"
  IO.FS.writeBinFile path (ByteArray.mk database.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT id,first,second FROM items ORDER BY id;"] }
  unless output.exitCode == 0 do
    fail s!"sqlite3 rejected the verified MVP image: {output.stderr}"
  unless output.stdout == "ok\n1|alpha|\n2|-4|beta\n" do
    fail s!"sqlite3 read unexpected MVP rows: {repr output.stdout}"

def expectMVPFileAdapter : IO Unit := do
  let alpha : PhysicalCodec.Text := ⟨[97, 108, 112, 104, 97], by decide⟩
  let beta : PhysicalCodec.Text := ⟨[98, 101, 116, 97], by decide⟩
  let first : PhysicalCodec.Row := {
    rowid := ⟨1, by decide, by decide⟩
    first := .text alpha
    second := .null }
  let second : PhysicalCodec.Row := {
    rowid := ⟨2, by decide, by decide⟩
    first := .integer ⟨-4, by decide, by decide⟩
    second := .text beta }
  let old : PhysicalCodec.Database := {
    rows := [second]
    rowidsSorted := by simp [PhysicalCodec.Row.keyLess, second]
    pageFits := by
      unfold PhysicalCodec.PageFit PhysicalCodec.cellBytes PhysicalCodec.pageSize
      decide }
  let new ← match old.insertChecked first with
    | .ok database => pure database
    | .error message => fail s!"verified MVP arbitrary-order insert failed: {message}"
  unless new.rows == [first, second] do
    fail "verified MVP arbitrary-order insert produced the wrong rows"
  let updated ← match new.updatePayload 2 .null (.text alpha) with
    | .ok database => pure database
    | .error message => fail s!"verified MVP update failed: {message}"
  match updated.findRow? 2 with
  | some row =>
      unless row.first == .null && row.second == .text alpha do
        fail "verified MVP update changed the wrong payload"
  | none => fail "verified MVP update lost its target row"
  let deleted ← match updated.deleteRowid 1 with
    | .ok database => pure database
    | .error message => fail s!"verified MVP delete failed: {message}"
  unless deleted.rows.length == 1 && (deleted.findRow? 2).isSome do
    fail "verified MVP delete removed the wrong row"
  if (new.insertChecked first).isOk then
    fail "verified MVP insert admitted a duplicate primary key"
  let paths : PhysicalFileAdapter.Paths := {
    main := ".lake/build/sqleanite-mvp-adapter.db"
    journal := ".lake/build/sqleanite-mvp-adapter.db-journal" }
  PhysicalFileAdapter.create .system paths old
  let openedOld ← PhysicalFileAdapter.reopen paths
  unless openedOld.rows == old.rows do
    fail "MVP file adapter did not reopen its initial database"
  let (openedNew, trace) ← PhysicalFileAdapter.commit .system paths new
  unless openedNew.rows == new.rows do
    fail "MVP file adapter did not reopen its committed database"
  let newTree ← match PhysicalTableBTree.build new with
    | some tree => pure tree
    | none => fail "MVP adapter test database did not build a physical tree"
  unless trace.length == (PhysicalMultiPageCodec.transactionWrites newTree).length + 7 do
    fail s!"MVP file adapter emitted the wrong VFS plan: {trace.length} requests"
  if ← paths.journal.pathExists then
    fail "MVP file adapter returned before journal deletion"
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT id,first,second FROM items ORDER BY id;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n1|alpha|\n2|-4|beta\n" do
    fail s!"sqlite3 rejected the adapter's committed image: {output.stderr}{output.stdout}"

  let third : PhysicalCodec.Row := {
    rowid := ⟨3, by decide, by decide⟩
    first := .integer ⟨33, by decide, by decide⟩
    second := .null }
  let fourth : PhysicalCodec.Row := {
    rowid := ⟨4, by decide, by decide⟩
    first := .integer ⟨44, by decide, by decide⟩
    second := .null }
  let fifth : PhysicalCodec.Row := {
    rowid := ⟨5, by decide, by decide⟩
    first := .integer ⟨55, by decide, by decide⟩
    second := .null }
  let grown ← match new.insertChecked third with
    | .error message => fail s!"MVP growth insert three failed: {message}"
    | .ok afterThird => match afterThird.insertChecked fourth with
      | .error message => fail s!"MVP growth insert four failed: {message}"
      | .ok afterFourth => match afterFourth.insertChecked fifth with
        | .error message => fail s!"MVP growth insert five failed: {message}"
        | .ok database => pure database
  let (openedGrown, growthTrace) ← PhysicalFileAdapter.commit .system paths grown
  unless openedGrown.rows == grown.rows do
    fail "MVP file adapter did not reopen its split multi-page commit"
  let grownTree ← match PhysicalTableBTree.build grown with
    | some tree => pure tree
    | none => fail "MVP grown database did not build a physical tree"
  unless PhysicalMultiPageCodec.filePageCount grownTree == 5 &&
      growthTrace.length == 12 do
    fail "MVP file adapter did not emit the expected five-page growth plan"
  let grownBytes ← IO.FS.readBinFile paths.main
  unless grownBytes.size == 5 * PhysicalCodec.pageSize do
    fail "MVP file adapter did not physically grow the main file"
  let grownCheck ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT count(*) FROM items;"] }
  unless grownCheck.exitCode == 0 && grownCheck.stdout == "ok\n5\n" do
    fail s!"sqlite3 rejected the adapter's grown image: {grownCheck.stderr}{grownCheck.stdout}"

  let shrunk ← match grown.deleteRowid 3 with
    | .error message => fail s!"MVP shrink delete three failed: {message}"
    | .ok afterThird => match afterThird.deleteRowid 4 with
      | .error message => fail s!"MVP shrink delete four failed: {message}"
      | .ok afterFourth => match afterFourth.deleteRowid 5 with
        | .error message => fail s!"MVP shrink delete five failed: {message}"
        | .ok database => pure database
  let (openedShrunk, shrinkTrace) ← PhysicalFileAdapter.commit .system paths shrunk
  unless openedShrunk.rows == shrunk.rows && shrinkTrace.length == 12 do
    fail "MVP file adapter did not reopen its freelist-backed shrink"
  let shrunkBytes ← IO.FS.readBinFile paths.main
  unless shrunkBytes.size == 5 * PhysicalCodec.pageSize do
    fail "MVP freelist shrink unexpectedly truncated the committed file"
  let shrinkCheck ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; PRAGMA freelist_count; SELECT count(*) FROM items;"] }
  unless shrinkCheck.exitCode == 0 && shrinkCheck.stdout == "ok\n3\n2\n" do
    fail s!"sqlite3 rejected the freelist shrink: {shrinkCheck.stderr}{shrinkCheck.stdout}"

  -- Inject the crash state after the new main page was written but before the
  -- page-level journal was deleted. Recovery must restore old pages and
  -- truncate the three newly grown pages.
  PhysicalFileAdapter.create .system paths old
  let oldTree ← match PhysicalTableBTree.build old with
    | some tree => pure tree
    | none => fail "MVP adapter old database did not build a physical tree"
  let crashJournal := GrowableStorage.makeJournal
    (PhysicalMultiPageCodec.storageImage oldTree)
    (PhysicalMultiPageCodec.transactionWrites grownTree)
  let encodedCrashJournal ← match PhysicalJournalCodec.ofJournal? crashJournal with
    | some journal => pure (PhysicalJournalCodec.encodeChecked journal)
    | none => fail "MVP adapter crash journal exceeded encoded bounds"
  IO.FS.writeBinFile paths.journal (ByteArray.mk encodedCrashJournal.toArray)
  IO.FS.writeBinFile paths.main
    (ByteArray.mk (PhysicalMultiPageCodec.fileBytes grownTree).toArray)
  let recovered ← PhysicalFileAdapter.recover .system paths
  unless recovered.rows == old.rows do
    fail "MVP file adapter failed to restore its page-level undo journal"
  let recoveredBytes ← IO.FS.readBinFile paths.main
  unless recoveredBytes.size == 2 * PhysicalCodec.pageSize do
    fail "MVP file adapter recovery did not truncate grown pages"

  -- Deterministically materialize the POSIX model's namespace checkpoints.
  -- These complement the quantified pure theorem with tests of the concrete
  -- executable's file-name handling.
  let noSync : PhysicalFileAdapter.SyncOps := {
    syncFile := fun _ => pure ()
    syncDeletion := fun _ => pure () }
  PhysicalFileAdapter.create noSync paths old
  IO.FS.writeBinFile paths.journalTemp
    (ByteArray.mk encodedCrashJournal.toArray)
  let tempRecovered ← PhysicalFileAdapter.recover noSync paths
  let tempStillExists ← paths.journalTemp.pathExists
  unless tempRecovered.rows == old.rows && !tempStillExists do
    fail "orphan temporary journal was published or not removed"

  PhysicalFileAdapter.create noSync paths old
  IO.FS.writeBinFile paths.journal
    (ByteArray.mk encodedCrashJournal.toArray)
  let publishedRecovered ← PhysicalFileAdapter.recover noSync paths
  unless publishedRecovered.rows == old.rows do
    fail "published journal without main writes did not recover the old image"

  PhysicalFileAdapter.create noSync paths old
  IO.FS.writeBinFile paths.main
    (ByteArray.mk (PhysicalMultiPageCodec.fileBytes grownTree).toArray)
  let deletedRecovered ← PhysicalFileAdapter.recover noSync paths
  unless deletedRecovered.rows == grown.rows do
    fail "deleted journal checkpoint did not retain the new image"

  PhysicalFileAdapter.create noSync paths old
  let corruptJournal := encodedCrashJournal.modify 20 (fun byte => byte + 1)
  IO.FS.writeBinFile paths.journal (ByteArray.mk corruptJournal.toArray)
  let corruptRejected ←
    try
      let _ ← PhysicalFileAdapter.recover noSync paths
      pure false
    catch _ => pure true
  unless corruptRejected do
    fail "live recovery accepted a deterministically corrupted journal"
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal

end SQLeanite.Tests
