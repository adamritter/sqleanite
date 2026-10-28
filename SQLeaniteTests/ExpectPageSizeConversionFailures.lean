import SQLeanite.SQLite.CLI
import SQLeaniteTests.ExpectPersistentPageTree

namespace SQLeanite.Tests
open SQLeanite

def expectPageSizeConversionFailures : IO Unit := do
  for fault in [0, 1, 2] do
    let main : System.FilePath := s!".lake/build/sqleanite-conversion-{fault}.db"
    let paths : CoreFileAdapter.Paths := { main, journal := main.toString ++ "-journal" }
    let temporary : System.FilePath := main.toString ++ ".sqleanite-image.tmp"
    for path in [main, paths.journal, paths.journalTemp, temporary] do
      if ← path.pathExists then IO.FS.removeFile path
    let setup ← IO.Process.output {
      cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
      args := #[main.toString, "PRAGMA page_size=512; CREATE TABLE t(v); INSERT INTO t VALUES('old');"] }
    unless setup.exitCode == 0 do fail s!"conversion fixture: {setup.stderr}"
    CoreFileAdapter.recoverInPlace .system paths
    let original ← IO.FS.readBinFile main
    let database ← CoreFileAdapter.reopen paths
    let (next, _) ← match CoreSQL.execute { database } "INSERT INTO t VALUES('new');" with
      | .ok result => pure result
      | .error message => fail message
    let syncOps : CoreFileAdapter.SyncOps := {
      syncFile := fun path => do
        if path.toString.endsWith ".sqleanite-image.tmp" then
          if fault == 0 then throw (IO.userError "injected temporary-file sync failure")
          if fault == 1 then IO.FS.writeBinFile path (ByteArray.mk #[0])
        (PhysicalFileAdapter.SyncOps.system).syncFile path
      syncDeletion := fun path => do
        if fault == 2 then throw (IO.userError "injected directory sync failure")
        (PhysicalFileAdapter.SyncOps.system).syncDeletion path }
    let failed ← try
        discard <| CoreFileAdapter.convertPageSize syncOps paths next.database
        pure false
      catch _ => pure true
    unless failed do fail "conversion fault injection did not fail"
    if fault < 2 then
      unless (← IO.FS.readBinFile main) == original do
        fail "unpublished conversion changed the original file"
    let checked ← IO.Process.output {
      cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
      args := #[main.toString, "PRAGMA integrity_check;SELECT count(*) FROM t;"] }
    unless checked.exitCode == 0 && checked.stdout == (if fault < 2 then "ok\n1\n" else "ok\n2\n") do
      fail s!"conversion exposed an incomplete image: {checked.stdout}{checked.stderr}"
    discard <| CoreFileAdapter.convertPageSize .system paths next.database
    let reopened ← CoreFileAdapter.reopen paths
    unless reopened.Equiv next.database do fail "conversion retry changed logical contents"

def expectSQLiteSchemaAdmission : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER,v);CREATE TABLE other(v);CREATE INDEX ix ON t(v);CREATE TABLE shadow(rowid);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  for sql in ["CREATE TABLE IF NOT EXISTS t(v TEXT);",
      "CREATE INDEX IF NOT EXISTS ix ON other(missing);",
      "CREATE UNIQUE INDEX IF NOT EXISTS ix ON t(unknown_function(v));",
      "CREATE INDEX IF NOT EXISTS ix ON t(v) WHERE missing;"] do
    let (next, results) ← match CoreSQL.execute initial sql with
      | .ok result => pure result
      | .error message => fail s!"schema no-op: {sql}: {message}"
    unless next.database.Equiv initial.database do fail s!"schema no-op changed database: {sql}"
    unless results.length == 1 && results.all (fun r => r.changes == 0 && r.rows.isEmpty) do
      fail s!"schema no-op changed result: {sql}"
  for sql in ["CREATE TABLE IF NOT EXISTS ix(v);", "CREATE INDEX IF NOT EXISTS t ON t(v);",
      "CREATE INDEX ix ON other(v);", "CREATE INDEX IF NOT EXISTS ix ON missing(v);",
      "CREATE TABLE sqlite_x(v);", "CREATE INDEX sqlite_x ON t(v);",
      "CREATE INDEX ir ON t(rowid);", "CREATE INDEX iq ON t(t.v);"] do
    match CoreSQL.execute initial sql with
    | .ok _ => fail s!"invalid schema admitted: {sql}"
    | .error _ => pure ()
  match CoreSQL.execute initial "CREATE INDEX ir ON shadow(rowid);" with
  | .ok _ => pure ()
  | .error message => fail s!"real rowid-named column rejected: {message}"

def expectSQLiteUniqueIndexes : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,a,b TEXT); INSERT INTO t VALUES(1,1,'a'),(2,2,'b'),(3,NULL,NULL),(4,NULL,NULL); CREATE UNIQUE INDEX ua ON t(a); CREATE UNIQUE INDEX ub ON t(b);"
  let cases : List (String × List (List Value)) := [
    ("SELECT id,a,b FROM t ORDER BY id;",
      [[.integer 1,.integer 1,.text "a"],[.integer 2,.integer 2,.text "b"],
       [.integer 3,.null,.null],[.integer 4,.null,.null]]),
    ("INSERT OR REPLACE INTO t VALUES(10,2,'a'); SELECT id,a,b FROM t ORDER BY id;",
      [[.integer 3,.null,.null],[.integer 4,.null,.null],[.integer 10,.integer 2,.text "a"]]),
    ("UPDATE t SET a=a+10 WHERE id<3; SELECT id,a,b FROM t WHERE id<3 ORDER BY id;",
      [[.integer 1,.integer 11,.text "a"],[.integer 2,.integer 12,.text "b"]]),
    ("INSERT INTO t VALUES(10,'1','c'); SELECT id,a,b FROM t WHERE id=10;",
      [[.integer 10,.text "1",.text "c"]])]
  for (sql, expected) in cases do
    let (state, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"UNIQUE index: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"UNIQUE result: {sql}"
    let some table := state.database.findTable? "t" | fail "UNIQUE lost table"
    unless table.indexes.length == 2 && table.indexes.all (·.unique) do
      fail "UNIQUE metadata lost"
  for sql in ["INSERT INTO t VALUES(10,1.0,'new');", "UPDATE t SET a=2 WHERE id=1;",
      "UPDATE t SET a=a+1 WHERE id<3;", "UPDATE t SET b='same';",
      "UPDATE t SET id=10,a=1 WHERE id=2;",
      "INSERT INTO t VALUES(10,10,'new'),(11,2,'other');"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"UNIQUE accepted duplicate: {sql}"
    | .error _ => pure ()
  match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(v); INSERT INTO t VALUES(1),(1.0); CREATE UNIQUE INDEX uv ON t(v);" with
  | .ok _ => fail "UNIQUE creation accepted numeric duplicates"
  | .error _ => pure ()
  for unique in [false, true] do
    let spec : CanonicalIndexSQL.Spec := { name := "quoted\"index", table := "t", column := "v", unique }
    unless CanonicalIndexSQL.parse (CanonicalIndexSQL.print spec) == some spec do
      fail "UNIQUE index SQL failed roundtrip"

def expectSQLitePatterns : IO Unit := do
  let cases : List (String × List Value) := [
    ("SELECT 'ABC' LIKE 'a%', 'Á' LIKE 'á', 'ABC' GLOB 'a*', 'abc' GLOB '[a-z]*';",
      [.integer 1,.integer 0,.integer 0,.integer 1]),
    ("SELECT 'a_b' LIKE 'a!_b' ESCAPE '!', 'abc' NOT LIKE 'a%', 'abc' NOT GLOB 'A*';",
      [.integer 1,.integer 0,.integer 1]),
    ("SELECT glob('[]]',']'),glob('[^]]','a'),glob('[z-a]','z'),glob('[z-a]','a'),glob('[','a');",
      [.integer 1,.integer 1,.integer 1,.integer 0,.integer 0]),
    ("SELECT X'80' GLOB '?',X'C080' LIKE '_',like('a',X'410078'),glob(X'',X'');",
      [.integer 1,.integer 1,.integer 1,.integer 1]),
    ("SELECT NULL LIKE '%',glob('*',NULL),like('a','a',NULL),like('a','a',CAST(X'210078' AS TEXT));",
      [.null,.null,.null,.integer 1])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"patterns: {message}"
    let row ← match expected.mapM SQLSurface.value with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [row] do fail s!"pattern result: {sql}"
  for sql in ["SELECT NULL LIKE '%' ESCAPE '';", "SELECT like(NULL,NULL,'ab');",
      "SELECT glob('a','a','x');", "SELECT like('a','a',char(0));"] do
    match CoreSQL.execute Core.State.empty sql with
    | .ok _ => fail s!"pattern accepted invalid input: {sql}"
    | .error _ => pure ()
  let tokens ← match lex "SELECT 'a_b' LIKE 'a!_b' ESCAPE '!';" with
    | .ok tokens => pure tokens
    | .error message => fail message
  let wrong ← match parse "SELECT like('a!_b','changed','!');" with
    | .ok statements => pure statements
    | .error message => fail message
  if (CoreTokenGrammar.check tokens wrong).isOk then fail "ESCAPE grammar accepted a changed operand"

def expectSQLiteRound : IO Unit := do
  let cases : List (String × List Value) := [
    ("SELECT round(0.5),round(-0.5),round(2.5),round(-2.5);",
      [.real 1.0,.real (-1.0),.real 3.0,.real (-3.0)]),
    ("SELECT round(2.675,2),round(1.005,2),round(0.05,1),round(-0.05,1);",
      [.real 2.67,.real 1.0,.real 0.1,.real (-0.1)]),
    ("SELECT round(12.5,-1),round(1.25,'1x'),round(1.25,'1e2'),round('bad');",
      [.real 13.0,.real 1.3,.real 1.3,.real 0.0]),
    ("SELECT round(NULL),round(1,NULL),round(1.25,31),typeof(round(1));",
      [.null,.null,.real 1.25,.text "real"])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"round: {message}"
    let row ← match expected.mapM SQLSurface.value with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [row] do fail s!"round result: {sql}"
  for sql in ["SELECT round();", "SELECT round(1,2,3);",
      "SELECT round(NULL,abs(-9223372036854775808));",
      "SELECT round(abs(-9223372036854775808),NULL);"] do
    match CoreSQL.execute Core.State.empty sql with
    | .ok _ => fail s!"round accepted invalid input: {sql}"
    | .error _ => pure ()

def expectSQLiteRowidUpdates : IO Unit := do
  let cases : List (String × Nat × List (List Value)) := [
    ("CREATE TABLE t(v); INSERT INTO t(rowid,v) VALUES(-5,'a'),(2,'b'); UPDATE t SET rowid=rowid+20,v=v||rowid; SELECT rowid,v FROM t ORDER BY rowid;",
      2, [[.integer 15,.text "a-5"],[.integer 22,.text "b2"]]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,'a'),(2,'b'); UPDATE t SET id=-id,v=id; SELECT id,v FROM t ORDER BY id;",
      2, [[.integer (-2),.integer 2],[.integer (-1),.integer 1]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES('a'); UPDATE t SET rowid=abs(-9223372036854775808),_rowid_=rowid+20; SELECT rowid,v FROM t;",
      1, [[.integer 21,.text "a"]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES('a'); UPDATE t SET rowid='9223372036854775807'; SELECT rowid,v FROM t;",
      1, [[.integer 9223372036854775807,.text "a"]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES('a'); UPDATE t SET rowid=NULL WHERE 0; SELECT rowid,v FROM t;",
      0, [[.integer 1,.text "a"]]),
    ("CREATE TABLE t(v); UPDATE t SET rowid=NULL; SELECT rowid,v FROM t;", 0, [])]
  for (sql, changed, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"rowid UPDATE: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"rowid UPDATE result: {sql}"
    unless (results.reverse[1]?).map (·.changes) == some changed do
      fail s!"rowid UPDATE changes count: {sql}"
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v NOT NULL); INSERT INTO t VALUES(1,'a'),(2,'b');"
  for sql in ["UPDATE t SET id=id+1;", "UPDATE t SET id=NULL;", "UPDATE t SET id=1.5;",
      "UPDATE t SET id='42x';", "UPDATE t SET id=id+10,v=NULL;",
      "UPDATE t SET id=missing,id=id+10;",
      "UPDATE t SET id=CASE WHEN id=2 THEN abs(-9223372036854775808) ELSE 100 END;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"rowid UPDATE accepted invalid input: {sql}"
    | .error _ => pure ()

def expectSQLiteImplicitRowid : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("CREATE TABLE t(v); INSERT INTO t VALUES('a'),('a'); SELECT rowid,v FROM t ORDER BY rowid;",
      [[.integer 1,.text "a"],[.integer 2,.text "a"]]),
    ("CREATE TABLE t(v); INSERT INTO t(rowid,v) VALUES(-5,'a'); INSERT INTO t(v) VALUES('b'); SELECT rowid,v FROM t ORDER BY rowid;",
      [[.integer (-5),.text "a"],[.integer (-4),.text "b"]]),
    ("CREATE TABLE t(v); INSERT INTO t DEFAULT VALUES; INSERT INTO t(rowid,v) VALUES(12,'x'); INSERT INTO t VALUES('y'); SELECT rowid,v FROM t ORDER BY rowid;",
      [[.integer 1,.null],[.integer 12,.text "x"],[.integer 13,.text "y"]]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t(v) VALUES('a'); INSERT INTO t DEFAULT VALUES; INSERT INTO t VALUES(NULL,'b'); SELECT * FROM t ORDER BY id;",
      [[.integer 1,.text "a"],[.integer 2,.null],[.integer 3,.text "b"]]),
    ("CREATE TABLE t(rowid,oid,_rowid_,v); INSERT INTO t VALUES('a','b','c',1); SELECT * FROM t;",
      [[.text "a",.text "b",.text "c",.integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"implicit rowid: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"implicit rowid result: {sql}"
  for sql in ["INSERT INTO t(unknown) VALUES(1);", "INSERT INTO t(unknown) DEFAULT VALUES;",
      "INSERT INTO t VALUES();", "INSERT INTO t(rowid) VALUES('bad');",
      "INSERT INTO t(rowid) VALUES(1),(1);"] do
    match CoreSQL.execute Core.State.empty ("CREATE TABLE t(v);" ++ sql) with
    | .ok _ => fail s!"rowid insertion accepted invalid input: {sql}"
    | .error _ => pure ()

def expectSQLiteAggregateExpressions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,1),(2,1.0),(3,2),(4,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT count(DISTINCT v),sum(DISTINCT v),avg(DISTINCT v),total(DISTINCT v) FROM t;",
      [[.integer 2, .integer 3, .real 1.5, .real 3.0]]),
    ("SELECT count(*),sum(v+1),avg(v),count(v*0) FROM t WHERE v+1>2;",
      [[.integer 1, .integer 3, .real 2.0, .integer 1]]),
    ("SELECT count(*),sum(v),avg(v),total(v),min(v),max(v) FROM t WHERE id<0;",
      [[.integer 0, .null, .null, .real 0.0, .null, .null]]),
    ("SELECT count(abs(-9223372036854775808)) FROM t LIMIT 0;", []),
    ("SELECT count(*) FROM t LIMIT 1 OFFSET 1;", []),
    ("SELECT count() FROM t;", [[.integer 4]]),
    ("SELECT count(x.v) FROM t AS x;", [[.integer 3]]),
    ("SELECT count(*) FROM t WHERE abs(-9223372036854775808) LIMIT 0;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate expression: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do
      fail s!"aggregate expression result: {sql}"
  for sql in ["SELECT count(missing) FROM t LIMIT 0;", "SELECT count(sum(v)) FROM t;",
      "SELECT count(t.v) FROM t AS x;", "SELECT sum(unknown.v) FROM t;",
      "SELECT sum(*) FROM t;", "SELECT count(abs(-9223372036854775808)) FROM t LIMIT 1 OFFSET 1;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"aggregate accepted invalid expression: {sql}"
    | .error _ => pure ()

def expectSQLiteRawText : IO Unit := do
  unless SQLite.CLI.listTextBytes [65,1,13,10,9,10,13,0,255] == [65,94,65,13,10,9,10,94,77] do
    fail "CLI control-byte rendering differs from the pinned default list mode"
  let cases : List (String × List (List Value)) := [
    ("SELECT CAST(X'FF8041' AS TEXT),typeof(CAST(X'FF8041' AS TEXT)),length(CAST(X'FF8041' AS TEXT));",
      [[.textBytes #[255,128,65], .text "text", .integer 2]]),
    ("SELECT substr(CAST(X'41808142' AS TEXT),2,2),instr(CAST(X'41808142' AS TEXT),'B');",
      [[.textBytes #[128,129], .integer 2]]),
    ("SELECT trim(CAST(X'FF41FF' AS TEXT),CAST(X'FF' AS TEXT));", [[.text "A"]]),
    ("SELECT hex(replace(CAST(X'C3A9FF' AS TEXT),CAST(X'A9' AS TEXT),CAST(X'80' AS TEXT)));", [[.text "C380FF"]]),
    ("SELECT hex(quote(CAST(X'FF270080' AS TEXT)));", [[.text "27FF272727"]]),
    ("SELECT unhex(CAST(X'3441FF3432' AS TEXT),CAST(X'FF' AS TEXT));", [[.blob #[74,66]]]),
    ("SELECT hex(char(55296)),typeof(char(55296)),unicode(char(55296));",
      [[.text "EDA080", .text "text", .integer 65533]]),
    ("SELECT CAST(CAST(X'3132FF' AS TEXT) AS NUMERIC),CAST(X'3132FF' AS TEXT)=CAST(12 AS INT);",
      [[.integer 12, .integer 0]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES(CAST(X'FF' AS TEXT)); UPDATE t SET v=v||'a'; SELECT v,typeof(v) FROM t;",
      [[.textBytes #[255,97], .text "text"]]),
    ("CREATE TABLE t(v); INSERT INTO t VALUES(CAST(X'FF' AS TEXT)); SELECT coalesce(min(v),'a'),count(v) FROM t;",
      [[.textBytes #[255], .integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"raw TEXT: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"raw TEXT mismatch: {sql}"

def expectSQLiteWALIndexFixture (walPath shmPath : String) : IO Nat := do
  let wal ← IO.FS.readBinFile walPath
  let shm ← IO.FS.readBinFile shmPath
  let some header := SQLite.WALIndex.decodeCopies false shm.data |
    throw (IO.userError "wal-index header rejected")
  unless header.encode false == shm.data.extract 0 48 do
    throw (IO.userError "wal-index header re-encoding mismatch")
  let log ← match SQLite.WALAppend.read wal.data with
    | .ok (some log) => pure log
    | .ok none => fail "WAL append parser rejected the reference log"
    | .error message => fail message
  unless log.committedFrames == header.maxFrame.val && log.pageCount == header.databaseSize.val &&
      log.checksum == header.frameChecksum do
    fail "WAL parser and independent wal-index disagree"
  let some decodedBig := SQLite.WALIndex.decodeHeader true (header.encode true) |
    throw (IO.userError "big-endian component header round-trip failed")
  unless decodedBig.encode true == header.encode true do
    throw (IO.userError "big-endian component header changed")
  let mut pages := #[]
  for i in [:header.maxFrame.val] do
    let some page := SQLite.WALIndex.number? true wal.data (32 + i * (24 + header.pageSize)) 4 |
      throw (IO.userError "WAL page number is truncated")
    pages := pages.push page
  for splitAt in [0, 1, 2, 73, 4061, 4062, 4063, header.maxFrame.val] do
    let count := min splitAt pages.size
    let first ← match SQLite.WALIndex.append false 0 (pages.extract 0 count) #[] with
      | .ok value => pure value
      | .error error => throw (IO.userError error)
    -- Simulate a writer that put an uncommitted suffix into the shared hash.
    let dirty ← match SQLite.WALIndex.append false count #[99999, 88888, 77777] first.bytes with
      | .ok value => pure value
      | .error error => throw (IO.userError error)
    let complete ← match SQLite.WALIndex.append false count (pages.extract count pages.size) dirty.bytes with
      | .ok value => pure value
      | .error error => throw (IO.userError error)
    let expectedBytes := ((SQLite.WALIndex.frameRegion header.maxFrame.val) + 1) * 32768
    unless complete.bytes.extract 136 expectedBytes == shm.data.extract 136 expectedBytes do
      throw (IO.userError s!"wal-index mapping mismatch at split {count}")
  return pages.size

def exportSQLiteWALAppend (walPath imagePath destination : String) : IO Nat := do
  let original ← IO.FS.readBinFile walPath
  let image ← IO.FS.readBinFile imagePath
  let log ← match SQLite.WALAppend.read original.data with
    | .ok (some log) => pure log
    | .ok none => fail "WAL append fixture has no valid log header"
    | .error message => fail message
  unless image.size % log.header.pageSize = 0 do fail "unaligned fixture image"
  let pages := (Array.range (image.size / log.header.pageSize)).map fun i =>
    (image.extract (i * log.header.pageSize) ((i + 1) * log.header.pageSize)).data
  let prepared ← match SQLite.WALAppend.prepare log pages with
    | .ok prepared => pure prepared
    | .error message => fail message
  IO.FS.withFile destination .write fun handle => do
    handle.write (original.extract 0 log.endOffset)
    let mut offset := log.endOffset
    for write in prepared.writes do
      unless write.offset = offset do fail "WAL append touched an old prefix or left a gap"
      handle.write (ByteArray.mk write.bytes)
      offset := offset + write.bytes.size
    unless offset = prepared.endOffset do fail "WAL append endpoint mismatch"
  return prepared.committedFrames.val

def expectSQLiteWALIndex : IO Unit := do
  for big in [false, true] do
    for pageSize in [512, 4096, 65536] do
      let header : SQLite.WALIndex.Header := {
        change := ⟨1234, by decide⟩, bigEndianChecksum := !big, pageSize
        maxFrame := ⟨4063, by decide⟩, databaseSize := ⟨99, by decide⟩
        frameChecksum := ⟨⟨1234567, by decide⟩, ⟨9876543, by decide⟩⟩
        saltFirst := ⟨0x12345678, by decide⟩, saltSecond := ⟨0x90abcdef, by decide⟩ }
      let encoded := header.encode big
      let some decoded := SQLite.WALIndex.decodeCopies big (encoded ++ encoded) |
        fail "WAL index header round-trip rejected"
      unless decoded.encode big == encoded do fail "WAL index header bytes changed"
      unless (SQLite.WALIndex.decodeCopies big (encoded ++ encoded.set! 8 255)).isNone do
        fail "WAL index accepted different copies"
      unless (SQLite.WALIndex.decodeCopies big ((encoded.set! 0 255) ++ (encoded.set! 0 255))).isNone do
        fail "WAL index accepted invalid version/checksum"

def expectSQLiteLargeValueBounds : IO Unit := do
  for (size, overhead, accepted) in [(1000000000, 0, true), (1000000001, 0, false),
      (999999999, 1, true), (1000000000, 1, false), (0, 0, true)] do
    unless (SQLite.Limits.check size overhead).isOk == accepted do
      throw (IO.userError "SQLite byte-limit boundary mismatch")
  unless PhysicalCodec.textByteLimit = SQLite.Text.resultLimit + 1 do
    throw (IO.userError "physical/scalar byte limits disagree")
  match SQLite.Text.zeroblob (.integer 1000000) with
  | .ok (.blob bytes) =>
      unless bytes.size = 1000000 && bytes.all (· == 0) do
        throw (IO.userError "million-byte zeroblob payload mismatch")
  | _ => throw (IO.userError "million-byte zeroblob was rejected")
  unless (SQLite.Text.zeroblob (.integer 1000000001)).toOption.isNone do
    throw (IO.userError "oversized zeroblob was accepted")

def expectSingletonLeafPacking : IO Unit := do
  let rec singles : RecursiveBPlusTree.Node Nat → Bool
    | .leaf entries => entries.length ≤ 1
    | .branch2 left _ right => singles left && singles right
    | .branch3 left _ middle _ right => singles left && singles middle && singles right
  for count in List.range 130 ++ [257, 511, 512, 1024] do
    let entries := (List.range count).map fun i => (i, i)
    let tree := SingletonPageTree.build entries
    unless tree.checkRootValid && singles tree && tree.toList == entries do
      fail s!"single-entry leaf packing failed at {count} entries"
  for width in [2001, 2044, 2048, 3000, 4080, 4096, 8000, 10000] do
    for count in [2, 3, 4, 5, 7, 8, 9, 17] do
      let inserts := (List.range count).map fun i =>
        s!"INSERT INTO t VALUES({i},zeroblob({width}));"
      let sql := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);" ++ String.join inserts
      let (state, _) ← match CoreSQL.execute Core.State.empty sql with
        | .ok result => pure result
        | .error message => fail message
      unless (CorePageCodec.encodeChecked state.database).isSome do
        fail s!"large local payload packing failed: width={width}, rows={count}"

def expectSQLiteOrderModifiers : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,'b'),(2,NULL),(3,'A'),(4,'a '),(5,'a');"
  let cases : List (String × List (List Value)) := [
    ("SELECT id FROM t ORDER BY v NULLS LAST;", [[.integer 3], [.integer 5], [.integer 4], [.integer 1], [.integer 2]]),
    ("SELECT id FROM t ORDER BY v DESC NULLS FIRST;", [[.integer 2], [.integer 1], [.integer 4], [.integer 5], [.integer 3]]),
    ("SELECT id FROM t ORDER BY v COLLATE NOCASE;", [[.integer 2], [.integer 3], [.integer 5], [.integer 4], [.integer 1]]),
    ("SELECT id FROM t ORDER BY v COLLATE RTRIM NULLS LAST;", [[.integer 3], [.integer 4], [.integer 5], [.integer 1], [.integer 2]]),
    ("SELECT id FROM t ORDER BY (v||'') COLLATE NOCASE DESC NULLS LAST LIMIT 2;", [[.integer 1], [.integer 4]]),
    ("SELECT 1 ORDER BY 1 COLLATE NOCASE NULLS LAST;", [[.integer 1]]),
    ("SELECT id FROM t ORDER BY v COLLATE missing COLLATE NOCASE LIMIT 2;", [[.integer 2], [.integer 3]]),
    ("SELECT id FROM t ORDER BY id DESC NULLS FIRST,abs(-9223372036854775808) LIMIT 1;", [[.integer 5]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"ORDER modifiers: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"ORDER modifiers mismatch: {sql}"
  for sql in ["SELECT id FROM t ORDER BY v COLLATE missing LIMIT 0;",
      "SELECT 1 ORDER BY 1 COLLATE missing LIMIT 0;", "SELECT id FROM t ORDER BY v NULLS;",
      "SELECT id FROM t ORDER BY v NULLS MIDDLE;", "SELECT id FROM t ORDER BY 0 AND v;",
      "SELECT id FROM t ORDER BY 0 AND abs(-9223372036854775808) COLLATE BINARY;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"ORDER modifiers omitted error: {sql}"
    | .error _ => pure ()

def expectSQLiteOrderExpressions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,w); INSERT INTO t VALUES(1,1,2),(2,-9223372036854775808,1),(3,3,0);"
  let cases : List (String × List (List Value)) := [
    ("SELECT id+1 AS k FROM t ORDER BY k DESC LIMIT 1;", [[.integer 4]]),
    ("SELECT id,v FROM t ORDER BY 2 LIMIT 1;", [[.integer 2, .integer (-9223372036854775808)]]),
    ("SELECT id AS v FROM t ORDER BY v COLLATE BINARY DESC LIMIT 1;", [[.integer 3]]),
    ("SELECT id AS v FROM t ORDER BY v;", [[.integer 1], [.integer 2], [.integer 3]]),
    ("SELECT id AS v FROM t ORDER BY v+0;", [[.integer 2], [.integer 1], [.integer 3]]),
    ("SELECT abs(v) FROM t ORDER BY -w LIMIT 1;", [[.integer 1]]),
    ("SELECT id FROM t ORDER BY id DESC,abs(v) LIMIT 1;", [[.integer 3]]),
    ("SELECT abs(v) FROM t ORDER BY 1 LIMIT 0;", []),
    ("SELECT 3 AS x,1 ORDER BY x+1;", [[.integer 3, .integer 1]]),
    ("SELECT 1 ORDER BY abs(-9223372036854775808);", [[.integer 1]]),
    ("SELECT abs(-9223372036854775808) ORDER BY 1 LIMIT 1 OFFSET 1;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"ORDER expression: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"ORDER expression mismatch: {sql}"
  for sql in ["SELECT abs(v) FROM t ORDER BY w LIMIT 1;", "SELECT id FROM t ORDER BY 0 LIMIT 0;",
      "SELECT id FROM t ORDER BY 2 LIMIT 0;", "SELECT id FROM t ORDER BY missing LIMIT 0;",
      "SELECT 1 ORDER BY unknown_function() LIMIT 0;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"ORDER expression omitted error: {sql}"
    | .error _ => pure ()

end SQLeanite.Tests
