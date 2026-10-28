import SQLeanite.CoreFileEngine
import SQLeanite.CoreLazyFileEngine
import SQLeaniteTests.ExpectRelationalAlgebra

namespace SQLeanite.Tests
open SQLeanite

def expectGeneralMVPFileInterop : IO Unit := do
  let sql := "
    CREATE TABLE users(user_id INTEGER PRIMARY KEY,name TEXT NOT NULL,note TEXT);
    CREATE TABLE posts(body TEXT,post_id INTEGER PRIMARY KEY,author_id INTEGER NOT NULL);
    CREATE INDEX users_name ON users(name);
    INSERT INTO users(name,user_id,note) VALUES('Ada',2,X'0102'),('Lin',1,1.5);
    INSERT INTO posts VALUES('proofs',10,2),('storage',9,1);"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"general MVP file setup failed: {message}"
  let image ← match CoreFile.encode state.database with
    | some image => pure image
    | none => fail "general MVP file encoder rejected a small valid database"
  let canonical ← match CoreDecode.decodeCanonicalFile image.fileBytes with
    | some database => pure database
    | none => fail "strict canonical decoder rejected its own general image"
  unless canonical.Equiv state.database do
    fail "strict canonical decoder changed the logical database"
  unless image.fileBytes.length == PhysicalCodec.pageSize * 4 do
    fail "general MVP file encoder produced the wrong physical page count"
  let path : System.FilePath := ".lake/build/sqleanite-general-mvp.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader", "
      PRAGMA integrity_check;
      SELECT user_id,name,typeof(note),quote(note) FROM users ORDER BY user_id;
      SELECT post_id,body,author_id FROM posts ORDER BY post_id;
      SELECT name FROM sqlite_master WHERE type='index' ORDER BY name;"] }
  unless output.exitCode == 0 && output.stdout ==
      "ok\n1|Lin|text|'1.5'\n2|Ada|blob|X'0102'\n9|storage|1\n10|proofs|2\nusers_name\n" do
    fail s!"sqlite3 rejected the arbitrary-schema image: {output.stderr}{output.stdout}"
  let mutation ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch",
      "INSERT INTO users VALUES(3,'C sqlite',2.25); UPDATE users SET note=X'CAFE' WHERE user_id=2; INSERT INTO posts VALUES('compact',11,3);"] }
  unless mutation.exitCode == 0 do
    fail s!"sqlite3 could not mutate the arbitrary-schema image: {mutation.stderr}"
  let mutatedBytes ← IO.FS.readBinFile path
  let decoded ← match CoreDecode.decode mutatedBytes.data.toList with
    | some database => pure database
    | none => fail "general decoder rejected an SQLite-written image"
  let users ← match decoded.findTable? "users" with
    | some table => pure table
    | none => fail "general decoder lost the users table"
  let posts ← match decoded.findTable? "posts" with
    | some table => pure table
    | none => fail "general decoder lost the posts table"
  unless users.rows.length == 3 && posts.rows.length == 3 &&
      users.indexes.map (·.name) == ["users_name"] do
    fail "general decoder lost a C-written row or index declaration"
  let cRow ← match users.rows.find? (fun row => row.rowid.value == 3) with
    | some row => pure row
    | none => fail "general decoder lost the compact C-written rowid"
  unless (cRow.value 1) == .text ⟨[67, 32, 115, 113, 108, 105, 116, 101], by decide⟩ do
    fail "general decoder changed C-written TEXT"
  unless (cRow.value 2) == .text ⟨[50, 46, 50, 53], by decide⟩ do
    fail "general decoder changed C-written TEXT affinity value"
  let adaRow ← match users.rows.find? (fun row => row.rowid.value == 2) with
    | some row => pure row
    | none => fail "general decoder lost the C-updated BLOB row"
  unless (adaRow.value 2) == .blob ⟨[202, 254], by decide⟩ do
    fail "general decoder changed C-written BLOB"
  let compact ← match posts.rows.find? (fun row => row.rowid.value == 11) with
    | some row => pure row
    | none => fail "general decoder lost the second C-written row"
  unless compact.value 2 == .integer ⟨3, by decide, by decide⟩ do
    fail "general decoder did not widen SQLite's compact integer serial type"

def expectTextPrimaryKeyInterop : IO Unit := do
  let ddl :=
    "CREATE TABLE usertable (ycsb_key TEXT PRIMARY KEY, field0 TEXT);"
  let (state, results) ← match CoreSQL.execute Core.State.empty s!"
      {ddl}
      INSERT INTO usertable VALUES('user1','value1');
      SELECT * FROM usertable WHERE ycsb_key='user1';" with
    | .ok outcome => pure outcome
    | .error message => fail s!"TEXT PRIMARY KEY setup failed: {message}"
  unless results.getLast?.map (·.rows) == some [[
      .text ⟨[117, 115, 101, 114, 49], by decide⟩,
      .text ⟨[118, 97, 108, 117, 101, 49], by decide⟩]] do
    fail "TEXT PRIMARY KEY SELECT * exposed the internal rowid"
  let table ← match state.database.findTable? "usertable" with
    | some table => pure table
    | none => fail "TEXT PRIMARY KEY setup lost its table"
  let implicitIndex := match table.indexes with
    | [index] => index.isImplicitPrimary table.schema
    | _ => false
  unless table.schema.hasHiddenRowid && table.schema.catalogColumns.length == 2 &&
      implicitIndex do
    fail "TEXT PRIMARY KEY was not lowered through its proof-carrying automatic index"
  let routedUpdate := table.pointUpdateRowid?
    [(1, .text ⟨[117, 112, 100, 97, 116, 101, 100], by decide⟩)]
    (some (.equal table.schema.declaredPrimaryKey
      (.text ⟨[117, 115, 101, 114, 49], by decide⟩)))
  unless routedUpdate.isSome do
    fail "TEXT PRIMARY KEY UPDATE did not use the declared-key point route"
  let image ← match CoreFile.encode state.database with
    | some image => pure image
    | none => fail "TEXT PRIMARY KEY physical encoder rejected a valid row"
  let path : System.FilePath := ".lake/build/sqleanite-text-primary.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let paths : CoreFileAdapter.Paths := {
    main := path
    journal := ".lake/build/sqleanite-text-primary.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  match ← CoreLazyFileEngine.execute? paths "
      SELECT * FROM usertable WHERE ycsb_key='user1';
      SELECT * FROM usertable WHERE ycsb_key='missing';" with
  | some (.ok [{ rows := found, changes := _ }, { rows := missing, changes := _ }]) =>
      unless found == [[
          .text ⟨[117, 115, 101, 114, 49], by decide⟩,
          .text ⟨[118, 97, 108, 117, 101, 49], by decide⟩]] &&
          missing.isEmpty do
        fail "page-directed TEXT PRIMARY KEY batch returned wrong rows"
  | _ => fail "TEXT PRIMARY KEY read batch missed the certified cold path"
  let inspected ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader", "
      SELECT sql FROM sqlite_master WHERE type='table' AND name='usertable';
      SELECT sql IS NULL FROM sqlite_master WHERE type='index';
      SELECT * FROM usertable;
      PRAGMA integrity_check;"] }
  unless inspected.exitCode == 0 && inspected.stdout ==
      "CREATE TABLE \"usertable\"(\"ycsb_key\" TEXT PRIMARY KEY,\"field0\" \"TEXT\")\n1\nuser1|value1\nok\n" do
    fail s!"SQLite rejected the exact TEXT PRIMARY KEY image: {inspected.stderr}{inspected.stdout}"
  let mutated ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch",
      "INSERT INTO usertable VALUES('user2','value2');"] }
  unless mutated.exitCode == 0 do
    fail s!"SQLite could not insert through the automatic TEXT PRIMARY KEY index: {mutated.stderr}"
  let bytes ← IO.FS.readBinFile path
  let reopened ← match CoreDecode.decode bytes.data.toList with
    | some database => pure database
    | none => fail "Lean rejected a C-written TEXT PRIMARY KEY row"
  let reopenedTable ← match reopened.findTable? "usertable" with
    | some table => pure table
    | none => fail "Lean reopen lost the TEXT PRIMARY KEY table"
  unless reopenedTable.rows.length == 2 && reopenedTable.indexes.length == 1 do
    fail "Lean reopen lost a C-written row or automatic index"
  match CoreSQL.execute { database := reopened }
      "INSERT INTO usertable VALUES('user2','different');" with
  | .ok _ => fail "TEXT PRIMARY KEY admitted a duplicate key after C interop"
  | .error message =>
      unless message == "UNIQUE constraint failed: PRIMARY KEY" do
        fail s!"TEXT PRIMARY KEY returned the wrong duplicate error: {message}"
  -- Exercise the exact file-backed statement shapes used by VeriBetrKV's
  -- YCSB A/B/C/D/F runs.  This deliberately uses the paper schema verbatim:
  -- there is no surrogate integer key or separately declared index.
  let connection ← CoreFileEngine.reopen .system paths
  let workload ← CoreFileEngine.execute connection "
    BEGIN;
    SELECT field0 FROM usertable WHERE ycsb_key='user1';
    UPDATE usertable SET field0='updated1' WHERE ycsb_key='user1';
    INSERT INTO usertable VALUES('user3','value3');
    SELECT field0 FROM usertable WHERE ycsb_key='user2';
    UPDATE usertable SET field0='updated2' WHERE ycsb_key='user2';
    COMMIT;"
  match workload with
  | .error message =>
      fail s!"file-backed TEXT PRIMARY KEY YCSB shapes failed: {message}"
  | .ok results =>
      let rows := results.flatMap (·.rows)
      unless rows == [
          [.text ⟨[118, 97, 108, 117, 101, 49], by decide⟩],
          [.text ⟨[118, 97, 108, 117, 101, 50], by decide⟩]] do
        fail "file-backed TEXT PRIMARY KEY reads returned wrong YCSB values"
  let workloadCheck ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader", "
      PRAGMA integrity_check;
      SELECT ycsb_key,field0 FROM usertable ORDER BY ycsb_key;"] }
  unless workloadCheck.exitCode == 0 && workloadCheck.stdout ==
      "ok\nuser1|updated1\nuser2|updated2\nuser3|value3\n" do
    fail s!"SQLite rejected the file-backed TEXT PRIMARY KEY workload: {workloadCheck.stderr}{workloadCheck.stdout}"

def expectLiveOverflowInterop : IO Unit := do
  let large := String.mk (List.replicate 9000 'x')
  let sql := s!"
    CREATE TABLE overflowing(id INTEGER PRIMARY KEY,payload TEXT NOT NULL);
    CREATE INDEX overflowing_payload ON overflowing(payload);
    INSERT INTO overflowing VALUES(1,'{large}');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"overflow SQL setup failed: {message}"
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-overflow.db"
    journal := ".lake/build/sqleanite-overflow.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  CoreFileAdapter.create .system paths state.database
  let reopened ← CoreFileAdapter.reopen paths
  unless reopened.Equiv state.database do
    fail "Lean overflow reopen changed the logical database"
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT length(payload) FROM overflowing INDEXED BY overflowing_payload; SELECT count(*) FROM overflowing;"] }
  unless output.exitCode == 0 && output.stdout == "ok\n9000\n1\n" do
    fail s!"sqlite3 rejected Lean overflow chains: {output.stderr}{output.stdout}"
  let mutation ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch",
      "UPDATE overflowing SET payload=hex(zeroblob(3500)) WHERE id=1;"] }
  unless mutation.exitCode == 0 do
    fail s!"sqlite3 could not rewrite the overflow chain: {mutation.stderr}"
  let cWritten ← CoreFileAdapter.reopen paths
  let table ← match cWritten.findTable? "overflowing" with
    | some table => pure table
    | none => fail "Lean lost the C-written overflow table"
  let row ← match table.rows.head? with
    | some row => pure row
    | none => fail "Lean lost the C-written overflow row"
  match row.value 1 with
  | .text value =>
      unless value.bytes.length == 7000 &&
          value.bytes.all (fun byte => byte == 48) do
        fail "Lean changed C-written overflow TEXT bytes"
  | _ => fail "Lean decoded C-written overflow TEXT as another storage class"

def expectEscapedCatalogIdentifiers : IO Unit := do
  let sql := "
    CREATE TABLE \"odd\"\"table,one\"(
      \"id\"\"key\" INTEGER PRIMARY KEY,\"value,part\" TEXT NOT NULL);
    CREATE INDEX \"idx\"\"comma,\" ON \"odd\"\"table,one\"(\"value,part\");
    INSERT INTO \"odd\"\"table,one\" VALUES(1,'kept');"
  let (state, _) ← match CoreSQL.execute Core.State.empty sql with
    | .ok outcome => pure outcome
    | .error message => fail s!"escaped catalog setup failed: {message}"
  let image ← match CoreFile.encode state.database with
    | some image => pure image
    | none => fail "escaped catalog encoder rejected a valid database"
  let decoded ← match CoreDecode.decode image.fileBytes with
    | some database => pure database
    | none => fail "escaped catalog decoder rejected its own image"
  let table ← match decoded.findTable? "odd\"table,one" with
    | some table => pure table
    | none => fail "escaped table name did not round-trip"
  unless table.schema.columns.map (·.name) == ["id\"key", "value,part"] &&
      table.indexes.map (·.name) == ["idx\"comma,"] && table.rows.length == 1 do
    fail "escaped catalog metadata changed during file round-trip"
  let path : System.FilePath := ".lake/build/sqleanite-escaped-catalog.db"
  IO.FS.writeBinFile path (ByteArray.mk image.fileBytes.toArray)
  let output ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-noheader",
      "PRAGMA integrity_check; SELECT \"value,part\" FROM \"odd\"\"table,one\";"] }
  unless output.exitCode == 0 && output.stdout == "ok\nkept\n" do
    fail s!"sqlite3 rejected escaped catalog identifiers: {output.stderr}{output.stdout}"

end SQLeanite.Tests
