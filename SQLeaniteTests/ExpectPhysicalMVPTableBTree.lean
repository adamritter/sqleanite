import SQLeanite.CoreWALFileAdapter
import SQLeanite.PageCache
import SQLeanite.PageReuse
import SQLeanite.TornStorage
import SQLeaniteTests.ExpectRelationalAlgebra

namespace SQLeanite.Tests
open SQLeanite

def expectPhysicalMVPTableBTree : IO Unit := do
  let first : PhysicalCodec.Row := {
    rowid := ⟨1, by decide, by decide⟩
    first := .integer ⟨11, by decide, by decide⟩
    second := .null }
  let second : PhysicalCodec.Row := {
    rowid := ⟨2, by decide, by decide⟩
    first := .integer ⟨22, by decide, by decide⟩
    second := .null }
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
  let database : PhysicalCodec.Database := {
    rows := [first, second, third, fourth, fifth]
    rowidsSorted := by
      simp [PhysicalCodec.Row.keyLess, first, second, third, fourth, fifth]
    pageFits := by
      unfold PhysicalCodec.PageFit PhysicalCodec.cellBytes PhysicalCodec.pageSize
      decide }
  let tree ← match PhysicalTableBTree.build database with
    | some tree => pure tree
    | none => fail "physical MVP table B-tree rejected a fitting database"
  unless tree.toList == database.rows do
    fail "physical MVP table B-tree partition changed observable rows"
  unless tree.leaves.map List.length == [2, 2, 1] do
    fail s!"physical MVP table B-tree split rows incorrectly: {tree.leaves.map List.length}"
  unless tree.interiorCells.map (fun cell => cell.leftChildPage.value.val) == [3, 4] &&
      tree.interiorCells.map (fun cell => cell.key.value) == [2, 4] &&
      tree.rightmostPage.val == 5 do
    fail "physical MVP table B-tree emitted incorrect bounded child references"
  let pages := tree.tablePages
  unless pages.map (fun page => page.bytes[0]?) ==
      [some 5, some 13, some 13, some 13] do
    fail "physical MVP table B-tree emitted incorrect SQLite page types"
  unless pages.all (fun page => page.bytes.size == PhysicalCodec.pageSize) do
    fail "physical MVP table B-tree emitted a non-4096-byte page"
  let fileBytes := PhysicalMultiPageCodec.fileBytes tree
  match DiskFormat.decodeDatabaseImage fileBytes with
  | some (image, []) =>
      unless image.geometry.pageCount == 5 do
        fail "verified multi-page image decoder recovered the wrong page count"
  | _ => fail "verified multi-page image decoder rejected its own bytes"
  match PhysicalMultiPageCodec.decodeFile fileBytes with
  | some reopened =>
      unless reopened.rows == database.rows do
        fail "verified multi-page logical decoder changed the row sequence"
  | none => fail "verified multi-page logical decoder rejected its own image"
  let journal := GrowableStorage.makeJournal
    (PhysicalMultiPageCodec.storageImage tree)
    (PhysicalMultiPageCodec.transactionWrites tree)
  let encodable ← match PhysicalJournalCodec.ofJournal? journal with
    | some value => pure value
    | none => fail "multi-page rollback journal exceeded its encoded bounds"
  match PhysicalJournalCodec.decode (PhysicalJournalCodec.encode encodable) with
  | some (decoded, []) =>
      unless decoded.originalPageCount == journal.originalPageCount &&
          decoded.undo.map (fun record => record.pageId) ==
            journal.undo.map (fun record => record.pageId) &&
          decoded.undo.map (fun record => record.before.bytes) ==
            journal.undo.map (fun record => record.before.bytes) do
        fail "multi-page rollback journal codec changed an undo record"
  | _ => fail "multi-page rollback journal codec rejected its own bytes"
  let checked := PhysicalJournalCodec.encodeChecked encodable
  unless PhysicalJournalCodec.decodeChecked checked |>.isSome do
    fail "checksummed rollback journal rejected its own bytes"
  let corrupted := checked.modify 20 (fun byte => byte + 1)
  unless PhysicalJournalCodec.decodeChecked corrupted |>.isNone do
    fail "checksummed rollback journal accepted a changed covered byte"
  let persistent ← match PhysicalJournalCodec.ofEncodable? encodable with
    | some value => pure value
    | none => fail "rollback journal exceeded persistent length bounds"
  let active := PhysicalJournalCodec.encodePersistentActive persistent ++
    List.replicate 4096 0
  match PhysicalJournalCodec.decodePersistent active with
  | some (some decoded) =>
      unless decoded.originalPageCount == journal.originalPageCount &&
          decoded.undo.map (fun record => record.pageId) ==
            journal.undo.map (fun record => record.pageId) &&
          decoded.undo.map (fun record => record.before.bytes) ==
            journal.undo.map (fun record => record.before.bytes) do
        fail "persistent rollback journal changed an active undo record"
  | _ => fail "persistent rollback journal rejected an active record with spare capacity"
  match PhysicalJournalCodec.decodePersistent
      PhysicalJournalCodec.initialInactiveBytes.data.toList with
  | some none => pure ()
  | _ => fail "persistent rollback journal rejected its durable inactive marker"
  let path : System.FilePath := ".lake/build/sqleanite-mvp-multipage.db"
  IO.FS.writeBinFile path (ByteArray.mk fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT id,first,second FROM items ORDER BY id;"] }
  unless output.exitCode == 0 do
    fail s!"sqlite3 rejected the verified multi-page B-tree: {output.stderr}"
  unless output.stdout == "ok\n1|11|\n2|22|\n3|33|\n4|44|\n5|55|\n" do
    fail s!"sqlite3 read unexpected multi-page rows: {repr output.stdout}"

def expectGrowableRollbackJournal : IO Unit := do
  let oldPage : Storage.Page 4 := ⟨#[1, 2, 3, 4], by decide⟩
  let changedPage : Storage.Page 4 := ⟨#[5, 6, 7, 8], by decide⟩
  let grownPage : Storage.Page 4 := ⟨#[9, 10, 11, 12], by decide⟩
  let old : GrowableStorage.Image 4 := {
    pageCount := 1
    read := fun _ => oldPage }
  let writes : List (GrowableStorage.PageWrite 4) :=
    [⟨0, changedPage⟩, ⟨1, grownPage⟩]
  let journal := GrowableStorage.makeJournal old writes
  unless journal.originalPageCount == 1 && journal.undo.length == 1 do
    fail "growable rollback journal recorded a new page instead of only old pre-images"
  let committed := GrowableStorage.applyWrites old writes
  unless committed.pageCount == 2 && (committed.read 0).bytes == changedPage.bytes &&
      (committed.read 1).bytes == grownPage.bytes do
    fail "growable page writes did not modify and extend the image"
  let recovered := GrowableStorage.recoverWithJournal committed (some journal)
  unless recovered.pageCount == 1 && (recovered.read 0).bytes == oldPage.bytes do
    fail "page-level rollback did not restore old contents and truncate growth"
  let recoveredAgain :=
    GrowableStorage.recoverRepeatedly committed (some journal) 100
  unless recoveredAgain.pageCount == recovered.pageCount &&
      (recoveredAgain.read 0).bytes == (recovered.read 0).bytes do
    fail "repeated recovery was not idempotent across restarts"
  let interruptedMain := GrowableStorage.applyWrites committed
    (GrowableStorage.recoveryWrites journal)
  let recoveredAfterCopyCrash :=
    GrowableStorage.recoverWithJournal interruptedMain (some journal)
  unless recoveredAfterCopyCrash.pageCount == recovered.pageCount &&
      (recoveredAfterCopyCrash.read 0).bytes == (recovered.read 0).bytes do
    fail "recovery restart changed the result after page preimages were copied"
  let kept := GrowableStorage.recoverWithJournal committed none
  unless kept.pageCount == 2 && (kept.read 1).bytes == grownPage.bytes do
    fail "journal deletion did not retain the committed grown image"
  let target : GrowableStorage.Image 4 := {
    pageCount := 2
    read := fun pageId => if pageId = 0 then oldPage else grownPage }
  let delta := GrowableStorage.deltaWrites old target
  unless delta.length == 1 && delta.head?.map (·.pageId) == some 1 do
    fail "changed-page transaction retained an unchanged old page"
  let appliedDelta := GrowableStorage.applyWrites old delta
  unless appliedDelta.pageCount == 2 &&
      (appliedDelta.read 0).bytes == oldPage.bytes &&
      (appliedDelta.read 1).bytes == grownPage.bytes do
    fail "changed-page transaction did not refine the target image"
  -- This count is deliberately above the former native-stack ceiling.  Bulk
  -- creation compares an empty image with one write per physical page, so the
  -- old direct recursion crashed before it could return this list.
  let empty : GrowableStorage.Image 4 := {
    pageCount := 0
    read := fun _ => oldPage }
  let largeTarget : GrowableStorage.Image 4 := {
    pageCount := 200000
    read := fun _ => grownPage }
  let largeDelta := GrowableStorage.deltaWrites empty largeTarget
  unless largeDelta.length == 200000 &&
      largeDelta.head?.map (·.pageId) == some 199999 do
    fail "changed-page transaction did not remain stack-safe at 200,000 pages"

def expectTornSectorModel : IO Unit := do
  unless TornStorage.tornWitnessPage.bytes == #[1, 1, 0, 0] do
    fail "sector crash witness did not retain exactly one written sector"
  unless TornStorage.tornWitnessPage.bytes != TornStorage.oldWitnessPage.bytes &&
      TornStorage.tornWitnessPage.bytes != TornStorage.intendedWitnessPage.bytes do
    fail "sector crash model collapsed to page-atomic outcomes"

def expectPOSIXVFSPlan : IO Unit := do
  let page : Storage.Page 4 := ⟨#[1, 2, 3, 4], by decide⟩
  let old : GrowableStorage.Image 4 := { pageCount := 1, read := fun _ => page }
  let writes : List (GrowableStorage.PageWrite 4) := [⟨0, page⟩]
  let plan := POSIXVFS.commitPlan old writes
  unless plan.length == 8 do
    fail "POSIX VFS plan omitted a data or directory durability barrier"

def expectGroupCommit : IO Unit := do
  let wal : GroupCommit.WAL Nat := { main := 0 }
  let batch := [1, 2, 3, 4]
  let grouped := wal.commitGroup batch
  let sequential := wal.commitSequential batch
  unless grouped.visible == 4 && grouped.durableFrames == [4, 3, 2, 1] &&
      grouped.durableFrames == sequential.durableFrames do
    fail "group commit changed serial full-image semantics"
  let staged : GroupCommit.WAL Nat := { main := 0, pendingFrames := [4, 3, 2, 1] }
  unless staged.absorbPending.sync.visible == staged.sync.visible do
    fail "full-image write absorption changed the published state"
  unless GroupCommit.syncCount (GroupCommit.groupProtocol batch) == 1 &&
      GroupCommit.syncCount (GroupCommit.sequentialProtocol batch) == 4 do
    fail "group commit did not reduce four durability barriers to one"

def expectPhysicalGroupCommit : IO Unit := do
  let (created, _) ← match CoreSQL.execute { database := Core.Database.empty }
      "CREATE TABLE batched(id INTEGER PRIMARY KEY,value TEXT);" with
    | .ok outcome => pure outcome
    | .error message => fail s!"physical group setup failed: {message}"
  let (first, _) ← match CoreSQL.execute created
      "INSERT INTO batched VALUES(1,'a');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"physical group first state failed: {message}"
  let (second, _) ← match CoreSQL.execute first
      "INSERT INTO batched VALUES(2,'b');" with
    | .ok outcome => pure outcome
    | .error message => fail s!"physical group second state failed: {message}"
  let paths : CoreWALFileAdapter.Paths := {
    main := ".lake/build/sqleanite-group-commit.db"
    wal := ".lake/build/sqleanite-group-commit.db-wal" }
  CoreWALFileAdapter.create {
    syncFile := fun _ => pure ()
    syncDeletion := fun _ => pure () } paths created.database
  let syncs ← IO.mkRef 0
  let syncOps : CoreWALFileAdapter.SyncOps := {
    syncFile := fun _ => syncs.modify (· + 1)
    syncDeletion := fun _ => pure () }
  let reopened ← CoreWALFileAdapter.commitBatch syncOps paths
    [first.database, second.database]
  unless reopened.Equiv second.database && (← syncs.get) == 1 do
    fail "physical group commit changed the newest state or used multiple file syncs"

def expectVerifiedPageCache : IO Unit := do
  let store : Nat → Option Nat := fun key => some (key * 10)
  let cache := (PageCache.ReadCache.empty 2).insert 1 10 |>.insert 2 20
  unless cache.read 1 == some 10 && cache.read 2 == some 20 &&
      cache.entries.length == 2 do
    fail "bounded verified read cache lost a resident page"
  let evicted := cache.insert 3 30
  unless evicted.read 3 == some 30 && evicted.entries.length == 2 do
    fail "bounded verified read cache violated its capacity"
  let buffer := (PageCache.WriteBuffer.empty.put 7 70).put 7 71 |>.put 8 80
  unless buffer.entries.length == 2 && buffer.read 7 == some 71 &&
      buffer.flush.1.length == 2 && buffer.flush.2.entries.isEmpty do
    fail "deferred write buffer failed to absorb or flush writes"
  let _ := store

def expectSafePageReuse : IO Unit := do
  let pending : List PageReuse.FreePage :=
    [{ pageId := 7, safeAfterEpoch := 3 },
     { pageId := 8, safeAfterEpoch := 9 }]
  unless PageReuse.takeReusable 10 pending |>.isNone do
    fail "page allocator reused a free page before its durability barrier"
  let durable := PageReuse.crossDurabilityBarrier pending
  match PageReuse.takeReusable 5 durable with
  | some (page, _) =>
      unless page.pageId == 7 do
        fail "page allocator ignored the oldest-reader epoch barrier"
  | none => fail "page allocator rejected a durable snapshot-safe page"

def expectPhysicalWALCodec : IO Unit := do
  let header : PhysicalWAL.Header := {
    checkpointSequence := ⟨7, by decide⟩
    saltFirst := ⟨0x12345678, by decide⟩
    saltSecond := ⟨0x9abcdef0, by decide⟩ }
  unless PhysicalWAL.checksumBytes .zero header.prefix == header.checksum do
    fail "physical WAL header checksum disagreed with its byte recurrence"
  let first : PhysicalWAL.Frame := {
    pageNumber := ⟨⟨1, by decide⟩, by decide⟩
    databaseSize := ⟨2, by decide⟩
    page := Storage.Page.zero PhysicalCodec.pageSize }
  let secondPage : Storage.Page PhysicalCodec.pageSize := {
    bytes := Array.replicate PhysicalCodec.pageSize 42
    sizeInvariant := by simp }
  let second : PhysicalWAL.Frame := {
    pageNumber := ⟨⟨2, by decide⟩, by decide⟩
    databaseSize := ⟨2, by decide⟩
    page := secondPage }
  let wal : PhysicalWAL.WAL := { header, frames := [first, second] }
  match PhysicalWAL.decode wal.encode with
  | some decoded =>
      unless decoded.header == header && decoded.frames.length == 2 do
        fail "physical WAL decoder changed its header or frame count"
      match decoded.frames with
      | [decodedFirst, decodedSecond] =>
          unless decodedFirst.pageNumber == first.pageNumber &&
              decodedFirst.databaseSize == first.databaseSize &&
              decodedFirst.page.bytes == first.page.bytes &&
              decodedSecond.pageNumber == second.pageNumber &&
              decodedSecond.databaseSize == second.databaseSize &&
              decodedSecond.page.bytes == second.page.bytes do
            fail "physical WAL decoder changed a frame"
      | _ => fail "physical WAL decoder returned the wrong frame shape"
  | none => fail "physical WAL decoder rejected its own bytes"

def expectGeneralMVPSchemaCore : IO Unit := do
  let users : Core.Schema := {
    name := "users"
    columns := [
      { name := "user_id", notNull := true, integerPrimaryKey := true },
      { name := "name", notNull := true },
      { name := "note" }]
    primaryKey := 0 }
  let posts : Core.Schema := {
    name := "posts"
    columns := [
      { name := "body" },
      { name := "post_id", notNull := true, integerPrimaryKey := true },
      { name := "author_id", notNull := true }]
    primaryKey := 1 }
  let withUsers ← match Core.Database.empty.createTable users with
    | .ok database => pure database
    | .error message => fail s!"general MVP rejected users schema: {message}"
  let database ← match withUsers.createTable posts with
    | .ok database => pure database
    | .error message => fail s!"general MVP rejected posts schema: {message}"
  if (database.createTable users).isOk then
    fail "general MVP admitted a duplicate table name"
  let usersTable ← match database.findTable? "users" with
    | some table => pure table
    | none => fail "general MVP lost users table"
  let alice : PhysicalCodec.Text := ⟨[65, 108, 105, 99, 101], by decide⟩
  let insertedUsers ← match usersTable.insertValues
      [.integer ⟨1, by decide, by decide⟩, .text alice, .null] with
    | .ok table => pure table
    | .error message => fail s!"general MVP rejected a valid user: {message}"
  if (insertedUsers.insertValues
      [.integer ⟨2, by decide, by decide⟩, .null, .null]).isOk then
    fail "general MVP admitted NULL in a NOT NULL column"
  let indexedUsers ← match insertedUsers.addIndex { name := "users_name", column := 1 } with
    | .ok table => pure table
    | .error message => fail s!"general MVP rejected a valid index: {message}"
  let database ← match database.updateTable indexedUsers with
    | .ok database => pure database
    | .error message => fail s!"general MVP failed to replace users table: {message}"
  let postsTable ← match database.findTable? "posts" with
    | some table => pure table
    | none => fail "general MVP lost posts table"
  let hello : PhysicalCodec.Text := ⟨[104, 101, 108, 108, 111], by decide⟩
  let insertedPosts ← match postsTable.insertValues
      [.text hello, .integer ⟨10, by decide, by decide⟩,
        .integer ⟨1, by decide, by decide⟩] with
    | .ok table => pure table
    | .error message => fail s!"general MVP rejected non-leading primary key: {message}"
  let database ← match database.updateTable insertedPosts with
    | .ok database => pure database
    | .error message => fail s!"general MVP failed to replace posts table: {message}"
  unless database.tables.length == 2 && indexedUsers.indexes.length == 1 &&
      indexedUsers.rows.length == 1 && insertedPosts.rows.length == 1 do
    fail "general MVP changed a table, index, or row count"

def expectGeneralMVPSQL : IO Unit := do
  let sql := "
    CREATE TABLE users(user_id INTEGER PRIMARY KEY,name TEXT NOT NULL,note TEXT);
    CREATE TABLE posts(body TEXT,post_id INTEGER PRIMARY KEY,author_id INTEGER NOT NULL);
    CREATE INDEX users_name ON users(name);
    INSERT INTO users(name,user_id) VALUES('Ada',2),('Lin',1);
    UPDATE users SET note=X'0102' WHERE user_id=2;
    INSERT INTO posts VALUES('proofs',10,2),('storage',9,2);
    SELECT name,user_id FROM users WHERE NOT NOT name!='nobody' ORDER BY user_id;
    SELECT post_id,body FROM posts WHERE author_id>=1 ORDER BY post_id DESC LIMIT 1;
    SELECT DISTINCT author_id FROM posts ORDER BY author_id;
    SELECT count(*) FROM posts WHERE author_id=2;
    SELECT author_id,count(*),count(body),sum(post_id),min(post_id),max(post_id)
      FROM posts GROUP BY author_id;
    SELECT count(note) FROM users;
    SELECT sum(post_id) FROM posts WHERE author_id=2;
    SELECT min(post_id) FROM posts;
    SELECT max(post_id) FROM posts;
    SELECT min(note) FROM users WHERE user_id=99;
    SELECT note FROM users WHERE user_id=2;
    UPDATE users SET note=1.5 WHERE user_id=1;
    SELECT note FROM users WHERE user_id=1;
    SELECT user_id FROM users WHERE note=1.5;
    SELECT user_id FROM users UNION ALL SELECT author_id FROM posts;
    SELECT user_id FROM users UNION SELECT author_id FROM posts;
    SELECT user_id FROM users INTERSECT SELECT author_id FROM posts;
    SELECT user_id FROM users EXCEPT SELECT author_id FROM posts;
    SELECT users.user_id,posts.body FROM users
      LEFT JOIN posts ON users.user_id=posts.author_id;"
  let (state, results) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"general MVP SQL rejected supported schema: {message}"
  unless state.database.tables.length == 2 do
    fail "general MVP SQL did not retain both tables"
  for table in state.database.tables do
    let tree := table.rowTree.root.erase
    unless tree.toList == Core.treeEntries table.rows && tree.checkRootValid do
      fail "general MVP SQL could not materialize its verified table tree"
    for row in table.rows do
      let cell ← match CoreRecord.encodeCell? table.schema row with
        | some cell => pure cell
        | none => fail "general MVP row exceeded the physical record bounds"
      match CoreRecord.decodeRowCell table.schema (cell ++ [99]) with
      | some (decoded, [99]) =>
          unless decoded == row do
            fail "general MVP physical record changed an arbitrary-schema row"
      | _ => fail "general MVP physical record rejected its own cell"
  let projected := results.filter (fun result => !result.rows.isEmpty)
  unless projected.map (·.rows) ==
      [
        [[.text ⟨[76, 105, 110], by decide⟩, .integer ⟨1, by decide, by decide⟩],
         [.text ⟨[65, 100, 97], by decide⟩, .integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨10, by decide, by decide⟩,
          .text ⟨[112, 114, 111, 111, 102, 115], by decide⟩]],
        [[.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨2, by decide, by decide⟩,
          .integer ⟨2, by decide, by decide⟩,
          .integer ⟨2, by decide, by decide⟩,
          .integer ⟨19, by decide, by decide⟩,
          .integer ⟨9, by decide, by decide⟩,
          .integer ⟨10, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩]],
        [[.integer ⟨19, by decide, by decide⟩]],
        [[.integer ⟨9, by decide, by decide⟩]],
        [[.integer ⟨10, by decide, by decide⟩]],
        [[.null]],
        [[.blob ⟨[1, 2], by decide⟩]],
        -- TEXT affinity renders the assigned REAL, as in C SQLite.
        [[.text ⟨[49, 46, 53], by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩],
         [.integer ⟨2, by decide, by decide⟩],
         [.integer ⟨2, by decide, by decide⟩],
         [.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩],
         [.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨2, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩]],
        [[.integer ⟨1, by decide, by decide⟩, .null],
         [.integer ⟨2, by decide, by decide⟩,
          .text ⟨[115, 116, 111, 114, 97, 103, 101], by decide⟩],
         [.integer ⟨2, by decide, by decide⟩,
          .text ⟨[112, 114, 111, 111, 102, 115], by decide⟩]]
      ] do
    fail "general MVP SQL returned the wrong arbitrary-schema rows"
  match CoreSQL.execute state
      "INSERT INTO users VALUES(3,NULL,NULL);" with
  | .ok _ => fail "general MVP SQL admitted a NOT NULL violation"
  | .error _ => pure ()
  let (_, nestedResults) ← match CoreSQL.execute state
      "SELECT user_id FROM users UNION ALL SELECT author_id FROM posts INTERSECT SELECT user_id FROM users;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"nested Core compound read failed: {message}"
  unless nestedResults.map (fun result => result.rows) ==
      [[[
        .integer ⟨1, by decide, by decide⟩],
        [.integer ⟨2, by decide, by decide⟩]]] do
    fail "nested Core compound read changed left-to-right bag semantics"

def expectBinary64Core : IO Unit := do
  let positiveZero : FileFormat.U64Value := ⟨0, by decide⟩
  let negativeZero : FileFormat.U64Value := ⟨9223372036854775808, by decide⟩
  let one : FileFormat.U64Value := ⟨4607182418800017408, by decide⟩
  let oneAndHalf : FileFormat.U64Value := ⟨4609434218613702656, by decide⟩
  unless Binary64.compareBits positiveZero negativeZero == .eq &&
      Binary64.compareInteger 1 one == .eq &&
      Binary64.compareInteger 1 oneAndHalf == .lt &&
      PhysicalQuery.sqlEquals
        (.integer ⟨1, by decide, by decide⟩) (.realBits one) == .true do
    fail "exact binary64 comparison disagreed with SQLite numeric semantics"

end SQLeanite.Tests
