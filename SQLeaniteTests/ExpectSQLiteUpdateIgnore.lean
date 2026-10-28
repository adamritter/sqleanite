import SQLeaniteTests.ExpectCoreMultiFreelist
import SQLeaniteTests.ExpectSQLiteAutoIncrement

namespace SQLeanite.Tests
open SQLeanite

def expectSQLiteUpdateIgnore : IO Unit := do
  for (input, expected) in [(1,0),(2,10),(3,16),(8,30),(10,33),(100,66),(200,76),(125829120,269)] do
    unless SQLite.PlannerCost.logEst input == expected do fail "SQLite planner LogEst mismatch"
  unless SQLite.PlannerCost.add 33 33 == 43 && SQLite.PlannerCost.add 100 0 == 100 do
    fail "SQLite planner LogEst addition mismatch"
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER);CREATE UNIQUE INDEX tu ON t(u);" ++
    "INSERT INTO t VALUES(1,'a',1),(2,'b',2),(3,'c',3);" ++
    "CREATE TABLE k(k TEXT PRIMARY KEY NOT NULL,v);INSERT INTO k VALUES('a',1),('b',2);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let cases : List (String × Nat × List (List Value)) := [
    ("UPDATE OR IGNORE t SET u=u+1;SELECT id,u FROM t ORDER BY id;", 1,
      [[.integer 1, .integer 1], [.integer 2, .integer 2], [.integer 3, .integer 4]]),
    ("UPDATE OR IGNORE t SET id=id-1;SELECT id,u FROM t ORDER BY id;", 3,
      [[.integer 0, .integer 1], [.integer 1, .integer 2], [.integer 2, .integer 3]]),
    ("UPDATE OR IGNORE t SET v=NULL;SELECT id,u FROM t ORDER BY id;", 0,
      [[.integer 1, .integer 1], [.integer 2, .integer 2], [.integer 3, .integer 3]]),
    ("UPDATE OR IGNORE k SET k='a';SELECT k,v FROM k ORDER BY k;", 1,
      [[.text "a", .integer 1], [.text "b", .integer 2]]),
    ("UPDATE k SET k=k||'x';SELECT k,v FROM k ORDER BY k;", 2,
      [[.text "ax", .integer 1], [.text "bx", .integer 2]])]
  for (sql, changes, expected) in cases do
    let (_, results) ← match CoreSQL.execute initial sql with
      | .ok result => pure result
      | .error message => fail s!"UPDATE OR IGNORE: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows && (results.map (·.changes)).sum == changes do
      fail s!"UPDATE OR IGNORE mismatch: {sql}"
  let orderedSql := "CREATE TABLE q(id INTEGER PRIMARY KEY,v,u);CREATE INDEX qv ON q(v);" ++
    "CREATE UNIQUE INDEX qu ON q(u);INSERT INTO q VALUES(1,'b',1),(2,'a',2),(3,'c',3);" ++
    "UPDATE OR IGNORE q SET u=100 WHERE v>='a' AND v<='c';SELECT id FROM q WHERE u=100;"
  let (_, ordered) ← match CoreSQL.execute Core.State.empty orderedSql with
    | .ok result => pure result
    | .error message => fail message
  let expected ← match SQLSurface.value (.integer 2) with
    | .ok value => pure value
    | .error message => fail message
  unless (ordered.getLast?).map (·.rows) == some [[expected]] do fail "UPDATE IGNORE lost index scan order"
  let createdOrderSql := "CREATE TABLE q(id INTEGER PRIMARY KEY,v,u INTEGER,w INTEGER);" ++
    "CREATE UNIQUE INDEX qu ON q(u);CREATE INDEX qw ON q(w);" ++
    "INSERT INTO q VALUES(1,'a',1,3),(2,'b',2,2),(3,'c',3,1);" ++
    "UPDATE OR IGNORE q SET u=100 WHERE u>0 AND w>0;SELECT id FROM q WHERE u=100;"
  let (_, createdOrder) ← match CoreSQL.execute Core.State.empty createdOrderSql with
    | .ok result => pure result
    | .error message => fail message
  let expected ← match SQLSurface.value (.integer 3) with
    | .ok value => pure value
    | .error message => fail message
  unless (createdOrder.getLast?).map (·.rows) == some [[expected]] do fail "CREATE INDEX lost planner creation order"
  for sql in ["UPDATE OR IGNORE t SET id=NULL;", "UPDATE OR IGNORE t SET id='bad',v=NULL;",
      "UPDATE OR IGNORE t SET v=NULL,u=abs(-9223372036854775808);",
      "UPDATE OR IGNORE t SET u=no_function(),u=1;"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"UPDATE OR IGNORE swallowed error: {sql}"

def expectSQLiteInsertIgnore : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER);CREATE UNIQUE INDEX tu ON t(u);" ++
    "INSERT INTO t VALUES(1,'a',1),(3,'c',3);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let sql := "INSERT OR IGNORE INTO t VALUES(1,'skip',9),(NULL,NULL,9),(NULL,'d',4),(5,'skip',4),(NULL,'e',5);"
  let (state, results) ← match CoreSQL.execute initial sql with
    | .ok result => pure result
    | .error message => fail s!"INSERT OR IGNORE: {message}"
  unless (results.map (·.changes)).sum == 2 do fail "INSERT OR IGNORE change count"
  let (_, selected) ← match CoreSQL.execute state "SELECT id,v FROM t ORDER BY id;" with
    | .ok result => pure result
    | .error message => fail message
  let expected : List (List Value) := [[.integer 1, .text "a"], [.integer 3, .text "c"],
    [.integer 4, .text "d"], [.integer 5, .text "e"]]
  let expected ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (selected.getLast?).map (·.rows) == some expected do fail "INSERT OR IGNORE row allocation"
  for sql in ["INSERT OR IGNORE INTO t VALUES('bad',NULL,9);",
      "INSERT OR IGNORE INTO t VALUES(1,abs(-9223372036854775808),1);",
      "INSERT OR IGNORE INTO t VALUES(1.5,'x',9);", "INSERT OR IGNORE INTO t VALUES(9,'x');",
      "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',no_function(),9);",
      "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',missing,9);",
      "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',0 AND no_function(),9);"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"INSERT OR IGNORE swallowed a non-constraint error: {sql}"
  let (copied, results) ← match CoreSQL.execute initial "INSERT OR IGNORE INTO t SELECT * FROM t;" with
    | .ok result => pure result
    | .error message => fail message
  unless (results.map (·.changes)).sum == 0 && copied.database.tables.length == initial.database.tables.length do
    fail "INSERT OR IGNORE SELECT duplicate rows"

def expectSQLiteDeleteReturning : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(3,'c'),(1,'a'),(2,'b');"
  let cases : List (String × List (List Value)) := [
    ("DELETE FROM t WHERE id<3 RETURNING id,v;", [[.integer 1, .text "a"], [.integer 2, .text "b"]]),
    ("DELETE FROM t AS x WHERE x.id=2 RETURNING *,t.id+1;", [[.integer 2, .text "b", .integer 3]]),
    ("DELETE FROM t WHERE 0 RETURNING abs(-9223372036854775808);", []),
    ("DELETE FROM t WHERE id=3 RETURNING 0 AND missing;", [[.integer 0]])]
  for (sql, expected) in cases do
    let (state, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"DELETE RETURNING: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    let some result := results.getLast? | fail "DELETE RETURNING result missing"
    unless result.rows == rows && result.changes == expected.length do fail s!"DELETE RETURNING mismatch: {sql}"
    let some table := state.database.findTable? "t" | fail "DELETE RETURNING removed the table"
    unless table.rows.length + expected.length == 3 do fail "DELETE RETURNING row count mismatch"
  for sql in ["DELETE FROM t RETURNING t.*;", "DELETE FROM t AS x RETURNING x.id;",
      "DELETE FROM t RETURNING count(*);", "DELETE FROM t RETURNING 0 AND count(*);",
      "DELETE FROM t RETURNING 0 AND no_function();", "DELETE FROM t WHERE 0 RETURNING missing;",
      "DELETE FROM t RETURNING CASE WHEN id=3 THEN abs(-9223372036854775808) ELSE id END;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"DELETE RETURNING error omitted: {sql}"

def expectSQLiteValuesQuery : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("VALUES(1),(2),(NULL);", [[.integer 1], [.integer 2], [.null]]),
    ("VALUES(sum(1),count(*));", [[.integer 1, .integer 1]]),
    ("VALUES(1),(2) UNION ALL SELECT 3 ORDER BY column1 DESC LIMIT 2;", [[.integer 3], [.integer 2]]),
    ("SELECT 1 UNION ALL VALUES(2),(3);", [[.integer 1], [.integer 2], [.integer 3]]),
    ("VALUES('a' COLLATE nocase),('b') UNION SELECT 'A';", [[.text "A"], [.text "b"]]),
    ("VALUES('a'),('b' COLLATE nocase) UNION SELECT 'A';", [[.text "A"], [.text "a"], [.text "b"]]),
    ("VALUES(CAST('a' AS TEXT)),('b' COLLATE nocase) UNION SELECT 'A';", [[.text "A"], [.text "b"]]),
    ("SELECT 'A' UNION VALUES(CAST('a' AS TEXT)),('b' COLLATE nocase);", [[.text "A"], [.text "a"], [.text "b"]]),
    ("VALUES(CAST(abs(-9223372036854775808) AS TEXT)),(2) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;", [[.integer 2]]),
    ("VALUES(abs(-9223372036854775808)) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;", [[.integer 3]]),
    ("VALUES(abs(-9223372036854775808)),(2) UNION ALL SELECT 3 LIMIT 0;", []),
    ("VALUES(1),(abs(-9223372036854775808)) UNION ALL SELECT 3 LIMIT 1;", [[.integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"VALUES query: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"VALUES query mismatch: {sql}"
  for sql in ["VALUES();", "VALUES(1),(2,3);", "VALUES(1) LIMIT -1;", "VALUES(1) ORDER BY 1;",
      "VALUES(sum(1)),(2);", "VALUES(1),(sum(2));", "VALUES(1) UNION ALL SELECT 2 ORDER BY column1;",
      "SELECT 1 UNION ALL VALUES(2) LIMIT 0;",
      "VALUES(CAST('a' AS TEXT)),('b' COLLATE nocase) UNION ALL SELECT 'A' ORDER BY column1;",
      "VALUES(1+2),(4) UNION ALL SELECT 5 ORDER BY 1+2;",
      "VALUES(abs(-9223372036854775808)),(2) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;",
      "VALUES(1),(abs(-9223372036854775808)) UNION ALL SELECT 3 ORDER BY 1 LIMIT 1;"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"VALUES error omitted: {sql}"
  let sql := "VALUES(1),(2);"
  let parsed : CoreTokenGrammar.CertifiedParse sql ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result
    | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "VALUES AST missing"
  let forged := { query with columns := #[{ expr := .literal (.integer 99), alias := some "column1", sourceSql := some "1" }] }
  if (CoreTokenGrammar.check parsed.tokens #[.select forged]).isOk then
    fail "VALUES checker trusted a forged first-row projection"

def expectSQLiteInsertSelect : IO Unit := do
  let setup := "CREATE TABLE src(id INTEGER PRIMARY KEY,v);INSERT INTO src VALUES(1,'3'),(2,'4');" ++
    "CREATE TABLE dst(id INTEGER PRIMARY KEY,v INTEGER);CREATE TABLE empty(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("INSERT INTO dst(v) SELECT v FROM src ORDER BY id DESC;SELECT id,v,typeof(v) FROM dst ORDER BY id;",
      [[.integer 1, .integer 4, .text "integer"], [.integer 2, .integer 3, .text "integer"]]),
    ("INSERT INTO src(v) SELECT v FROM src ORDER BY id DESC;SELECT id,v FROM src ORDER BY id;",
      [[.integer 1, .text "3"], [.integer 2, .text "4"], [.integer 3, .text "4"], [.integer 4, .text "3"]]),
    ("BEGIN;INSERT INTO dst(v) SELECT v FROM src;ROLLBACK;SELECT count(*) FROM dst;", [[.integer 0]]),
    ("INSERT INTO dst(v) SELECT v FROM empty;SELECT count(*) FROM dst;", [[.integer 0]]),
    ("INSERT INTO dst(v) SELECT 1 UNION ALL SELECT 2;SELECT sum(v) FROM dst;", [[.integer 3]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"INSERT SELECT: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"INSERT SELECT mismatch: {sql}"
  for sql in ["INSERT INTO dst SELECT v FROM empty;", "INSERT INTO dst(missing) SELECT v FROM empty;",
      "INSERT INTO dst(v) SELECT no_function(v) FROM empty;", "INSERT INTO dst(v) SELECT 1,2 WHERE 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"INSERT SELECT error omitted: {sql}"
  let parsed ← match CoreTokenGrammar.parseStatements "INSERT INTO dst SELECT id,v FROM src;" with
    | .ok parsed => pure parsed
    | .error message => fail message
  unless parsed.toList.any CoreFileEngine.statementWrites do fail "INSERT SELECT did not request persistence"

def expectSQLiteDrop : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE INDEX tv ON t(v);" ++
    "CREATE TABLE k(id TEXT PRIMARY KEY,v);INSERT INTO t VALUES(1,7),(2,8);" ++
    "INSERT INTO k VALUES('a',9);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail s!"DROP seed: {message}"
  let apply := fun sql => do
    match CoreSQL.execute initial sql with
    | .ok (state, _) => pure state
    | .error message => fail s!"DROP execution: {sql}: {message}"
  let dropped ← apply "DROP TABLE t;"
  unless (dropped.database.findTable? "t").isNone && (dropped.database.findTable? "k").isSome do
    fail "DROP TABLE changed the wrong tables"
  let withoutIndex ← apply "DROP INDEX tv;"
  let some kept := withoutIndex.database.findTable? "t" | fail "DROP INDEX removed its table"
  unless kept.indexes.isEmpty && kept.rows.length == 2 do fail "DROP INDEX lost rows or retained metadata"
  let rolledBack ← apply "BEGIN;DROP INDEX tv;DROP TABLE k;ROLLBACK;"
  unless rolledBack.database.contents == initial.database.contents do fail "DROP rollback lost schema or rows"
  let noops ← apply "DROP TABLE IF EXISTS absent;DROP INDEX IF EXISTS t;"
  unless noops.database.contents == initial.database.contents do fail "DROP IF EXISTS changed contents"
  for sql in ["DROP TABLE absent;", "DROP INDEX absent;", "DROP INDEX sqlite_autoindex_k_1;",
      "DROP INDEX IF EXISTS sqlite_autoindex_k_1;", "DROP TABLE IF EXISTS sqlite_schema;",
      "DROP TABLE IF EXISTS sqlite_temp_master;"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"DROP error omitted: {sql}"
  unless CoreFileEngine.statementWrites (.dropTable "t") &&
      CoreFileEngine.statementWrites (.dropIndex "tv") do fail "DROP did not request persistence"
  unless CoreSQL.schemaNoop initial (.dropTable "absent" true) &&
      CoreSQL.schemaNoop initial (.dropIndex "absent" true) do fail "DROP no-op requested persistence"

def expectSQLiteIndexSource : IO Unit := do
  let paths : CoreWALFileAdapter.Paths := {
    main := ".lake/build/sqleanite-index-source.db"
    wal := ".lake/build/sqleanite-index-source.db-wal" }
  CoreWALFileAdapter.create .system paths Core.Database.empty
  let result ← CoreWALFileEngine.execute .system paths
    "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'x');SAVEPOINT s;CREATE INDEX main.ix ON t(v) /*kept*/ ;SAVEPOINT s;DROP INDEX ix;CREATE INDEX \"ix\" ON \"t\"(v);ROLLBACK TO s;RELEASE s;RELEASE s;UPDATE t SET v=17;"
  if let .error message := result then fail message
  let observed ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString,
      "SELECT sql FROM sqlite_schema WHERE name='ix';SELECT v FROM t;PRAGMA integrity_check;"] }
  unless observed.exitCode == 0 && observed.stdout ==
      "CREATE INDEX ix ON t(v) /*kept*/ \n17\nok\n" do
    fail s!"index source changed across savepoints: {observed.stdout}{observed.stderr}"

def expectSQLiteSizedPages : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);CREATE INDEX tv ON t(v);INSERT INTO t VALUES(-129,'left'),(0,'middle'),(129,'right');CREATE TABLE empty(id INTEGER PRIMARY KEY);" with
    | .ok value => pure value
    | .error message => fail message
  for size in [512, 1024, 2048, 4096, 8192, 16384, 32768, 65536] do
    let candidate := CoreFile.databaseHeader ⟨0, by decide⟩
    let candidate := { candidate with headerPrefix := { candidate.headerPrefix with
      pageSizeField := ⟨(if size = 65536 then 1 else size) % 65536, Nat.mod_lt _ (by decide)⟩ } }
    let some usable := CoreFileAdapter.headerUsablePageSize? candidate | fail "test page geometry"
    let some pages := CoreSizedPageCodec.encode? usable state.database candidate | fail "sized image encoding"
    unless pages.all (fun page => page.size == size) do fail "sized page length changed"
    let source : CoreDecode.IOPageSource := {
      usable
      pageCount := pages.size
      readPage := fun page => pure ((pages[page - 1]?).map Array.toList) }
    let some decoded ← CoreDecode.decodeFromIOPageSource source | fail "sized image decoding"
    unless decoded.Equiv state.database do fail "sized image changed logical contents"
    let wal ← match SQLite.WALAppend.initialBytes CoreWALFileAdapter.header size with
      | .ok value => pure value
      | .error message => fail message
    let log ← match SQLite.WALAppend.read wal with
      | .ok (some value) => pure value
      | _ => fail "sized WAL header decoding"
    unless log.header.pageSize == size && wal.size == 32 do fail "WAL header changed geometry"
    let prepared ← match SQLite.WALAppend.prepare log pages with
      | .ok value => pure value
      | .error message => fail message
    let encoded := prepared.writes.foldl (fun acc write => acc ++ write.bytes) wal
    let recovered ← match SQLite.WALRead.recover encoded.toList with
      | .ok (some value) => pure value
      | _ => fail "sized WAL recovery"
    for i in [:pages.size] do
      unless recovered.readPage (fun _ => none) (i + 1) == some pages[i]!.toList do
        fail "sized WAL changed a page"

def expectSQLiteHeaderVersions : IO Unit := do
  let header := CoreFile.databaseHeader ⟨3, by decide⟩
  for read in ([0, 1, 2] : List UInt8) do
    for write in ([0, 1, 2, 3, 255] : List UInt8) do
      let candidate := { header with headerPrefix := { header.headerPrefix with
        readVersion := read
        writeVersion := write } }
      unless (SQLite.HeaderVersion.readError? candidate).isNone do
        fail "readable file version was rejected"
      unless (SQLite.HeaderVersion.writeError? candidate).isSome == (write.toNat > 2) do
        fail "unknown write version was not read-only"
  for read in ([3, 127, 255] : List UInt8) do
    let candidate := { header with headerPrefix := { header.headerPrefix with readVersion := read } }
    unless SQLite.HeaderVersion.readError? candidate == some "file is not a database" do
      fail "unknown read version was admitted"
    unless (SQLite.HeaderVersion.writeError? candidate).isSome do
      fail "unreadable file version remained writable"
  for value in [0, 1, 2, 3, 4, 5, 255, 256, 257, 260, 261, 4294967295] do
    let candidate := { header with schemaFormat := ⟨value % 2^32, Nat.mod_lt _ (by decide)⟩ }
    unless (SQLite.HeaderVersion.readError? candidate).isSome == (value % 256 > 4) do
      fail "schema format did not follow the pinned low-byte admission"

def expectSQLiteReservedPages : IO Unit := do
  let header := CoreFile.databaseHeader ⟨3, by decide⟩
  let cases : List (Nat × UInt8 × Nat) :=
    [(512, 0, 512), (512, 1, 511), (512, 32, 480),
      (1024, 255, 769), (4096, 255, 3841), (1, 255, 65281)]
  for (field, reserved, expected) in cases do
    let candidate := { header with headerPrefix := { header.headerPrefix with
      pageSizeField := ⟨field % 2^16, Nat.mod_lt _ (by decide)⟩
      reservedSpace := reserved } }
    let some usable := CoreFileAdapter.headerUsablePageSize? candidate |
      fail "reserved-tail geometry rejected"
    unless usable.val == expected do fail "reserved-tail geometry used physical page size"
  for (field, reserved) in [(512, (33 : UInt8)), (512, 255), (0, 0), (1023, 0)] do
    let candidate := { header with headerPrefix := { header.headerPrefix with
      pageSizeField := ⟨field % 2^16, Nat.mod_lt _ (by decide)⟩
      reservedSpace := reserved } }
    unless (CoreFileAdapter.headerUsablePageSize? candidate).isNone do
      fail "invalid physical or usable page size admitted"

def expectSQLiteHeaderSize : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,7);" with
    | .ok value => pure value
    | .error message => fail message
  let some image := CorePageCodec.encodeChecked state.database | fail "header-size image encoder failed"
  let some (header, rest) := FileFormat.decodeDatabaseHeader image.fileBytes | fail "header-size header missing"
  let unset := { header with databaseSizePages := ⟨0, by decide⟩ }
  let stale := { header with
    databaseSizePages := ⟨999, by decide⟩
    versionValidFor := ⟨0, by decide⟩ }
  let cases : List (FileFormat.DatabaseHeader × List UInt8) :=
    [(header, []), (unset, []), (stale, []), (header, [1,2,3]), (header, List.replicate 4096 0)]
  for (candidate, tail) in cases do
    let input := FileFormat.encodeDatabaseHeader candidate ++ rest ++ tail
    let some decoded := CoreFileAdapter.physicalImage? input | fail "compatible header size rejected"
    unless decoded.pageCount == image.pageCount do fail "header size selected the wrong logical image"
    for index in [:image.pageCount] do
      unless (decoded.read index).bytes == ((input.drop (index * 4096)).take 4096).toArray do
        fail "header-size decode changed a page"
  let tooLarge := { header with databaseSizePages := ⟨999, by decide⟩ }
  unless (SQLite.DatabaseSize.pageCount? tooLarge image.fileBytes.length 4096).isNone do
    fail "current size beyond EOF accepted"
  unless SQLite.DatabaseSize.filePages 4097 4096 == 2 do fail "file page count was not rounded up"
  unless SQLite.DatabaseSize.pageBytes (ByteArray.mk #[1,2,3]) 4 1 = some [1,2,3,0] do
    fail "partial final page was not zero-filled"
  unless (SQLite.DatabaseSize.pageBytes (ByteArray.mk #[1,2,3]) 4 2).isNone do
    fail "page starting beyond EOF was accepted"

def expectSQLiteSchemaPages : IO Unit := do
  let first : CoreFile.CatalogEntry := {
    kind := "table", name := "a", table := "a", rootPage := 2, sql := "CREATE TABLE a(id INTEGER PRIMARY KEY,v)" }
  let second : CoreFile.CatalogEntry := {
    kind := "table", name := "b", table := "b", rootPage := 3, sql := "CREATE TABLE b(id INTEGER PRIMARY KEY,v)" }
  let some leftCell := CoreFile.catalogCell? 1 first | fail "schema cell encoder failed"
  let some rightCell := CoreFile.catalogCell? 2 second | fail "schema cell encoder failed"
  let some leftPage := CoreFile.tableLeafPage? [leftCell] | fail "schema leaf encoder failed"
  let some rightPage := CoreFile.tableLeafPage? [rightCell] | fail "schema leaf encoder failed"
  let header := fun count => FileFormat.encodeDatabaseHeader
    (CoreFile.databaseHeader ⟨count % 2^32, Nat.mod_lt _ (by decide)⟩)
  let root := fun left right =>
    let cell := FileFormat.encodeUnsignedFixed 4 left ++ [1]
    let offset := 4096 - cell.length
    let treeHeader := [5, 0, 0] ++ FileFormat.encodeUnsignedFixed 2 1 ++
      FileFormat.encodeUnsignedFixed 2 offset ++ [0] ++ FileFormat.encodeUnsignedFixed 4 right ++
      FileFormat.encodeUnsignedFixed 2 offset
    header 3 ++ treeHeader ++ List.replicate (offset - 100 - treeHeader.length) 0 ++ cell
  let readCatalog := fun pages => do
    let source : CoreDecode.IOPageSource := {
      pageCount := pages.length
      readPage := fun page => pure (CoreDecode.page? pages page) }
    CoreDecode.catalogIOFrom source
  let result ← readCatalog [root 2 3, leftPage.bytes, rightPage.bytes]
  unless result = some [CoreDecode.CatalogEntry.ofEncoded first, CoreDecode.CatalogEntry.ofEncoded second] do
    fail "schema traversal lost branch order or entries"
  for (left, right) in [(1,3), (2,1), (2,2), (0,3), (2,4)] do
    unless (← readCatalog [root left right, leftPage.bytes, rightPage.bytes]).isNone do
      fail "schema traversal accepted a cycle, duplicate or invalid page"
  let large := { first with sql := first.sql ++ String.ofList (List.replicate 15000 ' ') }
  let some raw := CoreFile.catalogCell? 1 large | fail "large schema cell encoder failed"
  let some (_, afterSize) := FileFormat.decodeVarint raw | fail "schema payload size missing"
  let some (_, payload) := FileFormat.decodeVarint afterSize | fail "schema rowid missing"
  let plan : CoreOverflow.CellPlan := {
    kind := .table, cellPrefix := raw.take (raw.length - payload.length), payload }
  let some resolved := CoreOverflow.resolvePlans 2 [plan] | fail "schema overflow planning failed"
  let some body := CoreFile.leafBody? 13 100 resolved.cells | fail "schema overflow leaf failed"
  let page := header (1 + resolved.pages.length) ++ body.bytes
  let remaining := resolved.pages.map CoreFile.Page.bytes
  unless (← readCatalog (page :: remaining)) = some [CoreDecode.CatalogEntry.ofEncoded large] do
    fail "schema overflow traversal changed the SQL text"
  match remaining with
  | firstOverflow :: rest =>
      let cyclic := FileFormat.encodeUnsignedFixed 4 2 ++ firstOverflow.drop 4
      unless (← readCatalog (page :: cyclic :: rest)).isNone do
        fail "schema overflow traversal accepted a cycle"
  | [] => fail "schema overflow fixture stayed inline"

def expectSQLiteFormat : IO Unit := do
  let setup := "CREATE TABLE e(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT typeof(format()),hex(format());", [[.text "null", .text ""]]),
    ("SELECT typeof(format('')),hex(format(''));", [[.text "null", .text ""]]),
    ("SELECT typeof(format('%n')),hex(format('%n'));", [[.text "text", .text ""]]),
    ("SELECT typeof(format('%n%d|%s',12,'x')),hex(format('%n%d|%s',12,'x'));", [[.text "text", .text "31327C78"]]),
    ("SELECT typeof(format('%q|%Q|%w',NULL,NULL,NULL)),hex(format('%q|%Q|%w',NULL,NULL,NULL));", [[.text "text", .text "284E554C4C297C4E554C4C7C284E554C4C29"]]),
    ("SELECT typeof(format('%#Q',CAST(X'010A1B5C27' AS TEXT))),hex(format('%#Q',CAST(X'010A1B5C27' AS TEXT)));", [[.text "text", .text "756E6973747228275C75303030315C75303030615C75303031625C5C27272729"]]),
    ("SELECT typeof(format('%#q','a\\b')),hex(format('%#q','a\\b'));", [[.text "text", .text "615C5C62"]]),
    ("SELECT typeof(format('%#!.2Q','árvíz')),hex(format('%#!.2Q','árvíz'));", [[.text "text", .text "27C3A17227"]]),
    ("SELECT typeof(format('%!.1s',X'C0808080')),hex(format('%!.1s',X'C0808080'));", [[.text "text", .text "C0808080"]]),
    ("SELECT typeof(format('%5.3c',X'F09F9880')),hex(format('%5.3c',X'F09F9880'));", [[.text "text", .text "2020F09F9880F09F9880F09F9880"]]),
    ("SELECT typeof(format('%-5.3c',X'80')),hex(format('%-5.3c',X'80'));", [[.text "text", .text "808080202020"]]),
    ("SELECT typeof(format('%c|%c',NULL,42)),hex(format('%c|%c',NULL,42));", [[.text "text", .text "007C34"]]),
    ("SELECT typeof(format('hello%')),hex(format('hello%'));", [[.text "text", .text "68656C6C6F25"]]),
    ("SELECT typeof(format('before%Yafter',12)),hex(format('before%Yafter',12));", [[.text "text", .text "6265666F7265"]]),
    ("SELECT typeof(format('%Y')),hex(format('%Y'));", [[.text "null", .text ""]]),
    ("SELECT typeof(format('%08d|%#08x|%u|%r',-12,255,-1,112)),hex(format('%08d|%#08x|%u|%r',-12,255,-1,112));", [[.text "text", .text "2D303030303031327C307830303030303066667C31383434363734343037333730393535313631357C3131327468"]]),
    ("SELECT typeof(format('%+ d|% +d|%-05d',3,3,3)),hex(format('%+ d|% +d|%-05d',3,3,3));", [[.text "text", .text "20337C2B337C3030303033"]]),
    ("SELECT typeof(format('%*.*f',-12,3,12.3455)),hex(format('%*.*f',-12,3,12.3455));", [[.text "text", .text "31322E333435202020202020"]]),
    ("SELECT typeof(format('%!.17g|%.17g',49.47,49.47)),hex(format('%!.17g|%.17g',49.47,49.47));", [[.text "text", .text "34392E34377C34392E3437"]]),
    ("SELECT typeof(format('%!g|%#g|%,.2f',100,100,123456.789)),hex(format('%!g|%#g|%,.2f',100,100,123456.789));", [[.text "text", .text "3130302E307C3130302E3030307C3132332C3435362E3739"]]),
    ("SELECT typeof(format('%#.0f|%+.0f|%.0f',-0.1,-0.1,-0.1)),hex(format('%#.0f|%+.0f|%.0f',-0.1,-0.1,-0.1));", [[.text "text", .text "302E7C2D307C2D30"]]),
    ("SELECT typeof(format('%e|%!e|%g|%#g',0.00001,0.00001,1e30,1e30)),hex(format('%e|%!e|%g|%#g',0.00001,0.00001,1e30,1e30));", [[.text "text", .text "312E303030303030652D30357C312E30652D30357C31652B33307C312E3030303030652B3330"]]),
    ("SELECT typeof(format('%0g|%+g',1e999,1e999)),hex(format('%0g|%+g',1e999,1e999));", [[.text "text", .text "39652B3939397C2B496E66"]]),
    ("SELECT typeof(format('%*.*s|%d',-2147483648,-2147483648,'abc',7)),hex(format('%*.*s|%d',-2147483648,-2147483648,'abc',7));", [[.text "text", .text "6162637C37"]]),
    ("SELECT typeof(format('%2147483648d|%.2147483648f',12,12.75)),hex(format('%2147483648d|%.2147483648f',12,12.75));", [[.text "text", .text "31327C3133"]]),
    ("SELECT typeof(format(X'2564002573',42,'tail')),hex(format(X'2564002573',42,'tail'));", [[.text "text", .text "3432"]]),
    ("SELECT typeof(printf('%.0o|%.0x|%.0d',0,0,0)),hex(printf('%.0o|%.0x|%.0d',0,0,0));", [[.text "text", .text "307C307C30"]]),
    ("SELECT typeof(format('%s|%d|%f')),hex(format('%s|%d|%f'));", [[.text "text", .text "7C307C302E303030303030"]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"format functions: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"format function mismatch: {sql}"
  for sql in ["SELECT format('%2000000000s','a');", "SELECT format('%.2000000000d',1);",
      "SELECT format('%2000000000c','a');", "SELECT format('%2000000000f',1);",
      "SELECT format('%s',missing) FROM e LIMIT 0;", "SELECT format('%s',abs(-9223372036854775808));"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"format function error omitted: {sql}"

end SQLeanite.Tests
