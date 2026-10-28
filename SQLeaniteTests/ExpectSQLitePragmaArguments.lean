import SQLeaniteTests.ExpectSQLiteAutoIncrement

namespace SQLeanite.Tests
open SQLeanite

def expectSQLitePragmaArguments : IO Unit := do
  let definitions := [("01","zeroone"),("1","one"),("0x1","hex"),("1.0","floating"),
    ("-1","negative"),("CAST","casted"),("current_date","clock"),("true","truth")]
  let setup := String.join (definitions.map fun (name,column) =>
    "CREATE TABLE " ++ CoreFile.quoteIdentifier name ++ "(" ++ CoreFile.quoteIdentifier column ++ ");")
  let (state, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail s!"PRAGMA argument setup: {message}"
  let cases := [("01","zeroone"),("1","one"),("+1","one"),("0x1","hex"),
    ("1.0","floating"),("-1","negative"),("CAST","casted"),
    ("current_date","clock"),("true","truth"),("+/*sign*/01","zeroone")]
  for (argument,column) in cases do
    for schema in ["", "main.", "\"MAIN\"."] do
      let sql := "PRAGMA " ++ schema ++ "table_info(" ++ argument ++ ");"
      let (next, results) ← match CoreSQL.execute state sql with
        | .ok result => pure result
        | .error message => fail s!"PRAGMA atom {sql}: {message}"
      let expected : List (List Value) := [[.integer 0,.text column,.text "",.integer 0,.null,.integer 0]]
      let rows ← match expected.mapM (List.mapM SQLSurface.value) with
        | .ok rows => pure rows
        | .error message => fail message
      unless (results.getLast?).map (·.rows) == some rows && next.database.Equiv state.database do
        fail s!"PRAGMA atom lost spelling or changed state: {sql}"
  for sql in ["PRAGMA temp.table_info('1');", "PRAGMA main.table_info(sqlite_temp_schema);",
      "PRAGMA \"main.table_info\"('1');", "PRAGMA unknown_custom(1);",
      "PRAGMA main.unknown_custom=1;"] do
    let (_, results) ← match CoreSQL.execute state sql with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [] do fail s!"PRAGMA scope or no-op mismatch: {sql}"
  for sql in ["PRAGMA temp.table_info(sqlite_schema);", "PRAGMA table_info(sqlite_temp_master);"] do
    let (_, results) ← match CoreSQL.execute state sql with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows.length) == some 5 do fail "temp catalog metadata missing"
  for sql in ["PRAGMA missing.table_info('1');", "PRAGMA missing.unknown_custom;",
      "PRAGMA table_info(1_0);", "PRAGMA table_info(1.0_0);", "PRAGMA table_info(- -1);",
      "PRAGMA table_info(+true);", "PRAGMA table_info((1));", "PRAGMA table_info(NULL);",
      "PRAGMA table_info(JOIN);", "PRAGMA table_info(NOTHING);"] do
    if (CoreSQL.execute state sql).isOk then fail s!"invalid PRAGMA atom accepted: {sql}"
  let parsed ← match CoreTokenGrammar.parseCertified "PRAGMA main.table_info(01);" with
    | .ok parsed => pure parsed
    | .error message => fail message
  let atom : Expr := .literal (.integer 1) (some "01")
  if (CoreTokenGrammar.check parsed.tokens #[.pragma "table_info" (some atom) (some "temp")]).isOk then
    fail "PRAGMA certificate accepted a different schema"
  if (CoreTokenGrammar.check parsed.tokens
      #[.pragma "table_info" (some (.literal (.integer 1) (some "1"))) (some "main")]).isOk then
    fail "PRAGMA certificate discarded numeric name spelling"

def expectSQLiteApplicationHeaderPragmas : IO Unit := do
  let cases : List (String × List Int) := [
    ("PRAGMA user_version=1;PRAGMA user_version;", [1]),
    ("PRAGMA user_version=-1;PRAGMA user_version;", [(-1)]),
    ("PRAGMA user_version=2147483647;PRAGMA user_version;", [2147483647]),
    ("PRAGMA user_version=2147483648;PRAGMA user_version;", [0]),
    ("PRAGMA user_version=-2147483648;PRAGMA user_version;", [(-2147483648)]),
    ("PRAGMA user_version=-2147483649;PRAGMA user_version;", [0]),
    ("PRAGMA user_version=4294967295;PRAGMA user_version;", [0]),
    ("PRAGMA user_version=0x7fffffff;PRAGMA user_version;", [2147483647]),
    ("PRAGMA user_version=0x80000000;PRAGMA user_version;", [0]),
    ("PRAGMA user_version=+0x12;PRAGMA user_version;", [18]),
    ("PRAGMA user_version=-0x12;PRAGMA user_version;", [0]),
    ("PRAGMA user_version=' 12';PRAGMA user_version;", [0]),
    ("PRAGMA user_version='12junk';PRAGMA user_version;", [12]),
    ("PRAGMA user_version='0x12junk';PRAGMA user_version;", [18]),
    ("PRAGMA user_version='123.45';PRAGMA user_version;", [123]),
    ("PRAGMA user_version=12.5;PRAGMA user_version;", [12]),
    ("PRAGMA user_version=1e2;PRAGMA user_version;", [1]),
    ("PRAGMA user_version='on';PRAGMA user_version;", [0]),
    ("PRAGMA user_version=true;PRAGMA user_version;", [0]),
    ("PRAGMA user_version=ON;PRAGMA user_version;", [0]),
    ("PRAGMA user_version='0000000000000000000000012';PRAGMA user_version;", [12]),
    ("PRAGMA user_version='-0000000000002147483648';PRAGMA user_version;", [(-2147483648)]),
    ("PRAGMA application_id=1;PRAGMA application_id;", [1]),
    ("PRAGMA application_id=-1;PRAGMA application_id;", [(-1)]),
    ("PRAGMA application_id=2147483647;PRAGMA application_id;", [2147483647]),
    ("PRAGMA application_id=2147483648;PRAGMA application_id;", [0]),
    ("PRAGMA application_id=-2147483648;PRAGMA application_id;", [(-2147483648)]),
    ("PRAGMA application_id=-2147483649;PRAGMA application_id;", [0]),
    ("PRAGMA application_id=4294967295;PRAGMA application_id;", [0]),
    ("PRAGMA application_id=0x7fffffff;PRAGMA application_id;", [2147483647]),
    ("PRAGMA application_id=0x80000000;PRAGMA application_id;", [0]),
    ("PRAGMA application_id=+0x12;PRAGMA application_id;", [18]),
    ("PRAGMA application_id=-0x12;PRAGMA application_id;", [0]),
    ("PRAGMA application_id=' 12';PRAGMA application_id;", [0]),
    ("PRAGMA application_id='12junk';PRAGMA application_id;", [12]),
    ("PRAGMA application_id='0x12junk';PRAGMA application_id;", [18]),
    ("PRAGMA application_id='123.45';PRAGMA application_id;", [123]),
    ("PRAGMA application_id=12.5;PRAGMA application_id;", [12]),
    ("PRAGMA application_id=1e2;PRAGMA application_id;", [1]),
    ("PRAGMA application_id='on';PRAGMA application_id;", [0]),
    ("PRAGMA application_id=true;PRAGMA application_id;", [0]),
    ("PRAGMA application_id=ON;PRAGMA application_id;", [0]),
    ("PRAGMA application_id='0000000000000000000000012';PRAGMA application_id;", [12]),
    ("PRAGMA application_id='-0000000000002147483648';PRAGMA application_id;", [(-2147483648)]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,k);INSERT INTO t VALUES(1,123);PRAGMA user_version=8;PRAGMA application_id=9;SELECT 1;BEGIN;PRAGMA user_version=-1;PRAGMA application_id=-2147483648;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;ROLLBACK;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;", [1,(-1),(-2147483648),0,0,1,8,9,0,0,1]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,k);INSERT INTO t VALUES(1,123);PRAGMA user_version=8;PRAGMA application_id=9;SELECT 1;BEGIN;PRAGMA user_version=2147483647;PRAGMA temp.user_version=12;COMMIT;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;", [1,2147483647,9,12,0,1]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,k);INSERT INTO t VALUES(1,123);PRAGMA user_version=8;PRAGMA application_id=9;SELECT 1;SAVEPOINT a;PRAGMA user_version=3;PRAGMA temp.application_id=-8;SAVEPOINT b;PRAGMA user_version=4;PRAGMA temp.application_id=6;ROLLBACK TO a;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;RELEASE a;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;", [1,8,9,0,0,1,8,9,0,0,1]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,k);INSERT INTO t VALUES(1,123);PRAGMA user_version=8;PRAGMA application_id=9;SELECT 1;BEGIN;SAVEPOINT a;PRAGMA user_version=3;SAVEPOINT b;PRAGMA application_id=4;ROLLBACK TO b;RELEASE b;RELEASE a;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;COMMIT;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;", [1,3,9,0,0,1,3,9,0,0,1]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,k);INSERT INTO t VALUES(1,123);PRAGMA user_version=8;PRAGMA application_id=9;SELECT 1;SAVEPOINT same;PRAGMA user_version=10;SAVEPOINT SAME;PRAGMA application_id=11;ROLLBACK TO same;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;RELEASE same;ROLLBACK TO same;RELEASE same;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;", [1,10,9,0,0,1,8,9,0,0,1]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,k);INSERT INTO t VALUES(1,123);PRAGMA user_version=8;PRAGMA application_id=9;SELECT 1;PRAGMA temp.user_version=-1;PRAGMA temp.application_id=22;PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;", [1,8,9,(-1),22,1]),
    ("CREATE TABLE t(id INTEGER PRIMARY KEY,k);INSERT INTO t VALUES(1,123);PRAGMA user_version=8;PRAGMA application_id=9;SELECT 1;PRAGMA \"MAIN\".user_version(0x7fffffff);PRAGMA \"TEMP\".application_id(-2147483648);PRAGMA user_version;PRAGMA application_id;PRAGMA temp.user_version;PRAGMA temp.application_id;SELECT count(*) FROM t;", [1,2147483647,9,0,(-2147483648),1])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"application header PRAGMA {sql}: {message}"
    let wanted ← match expected.mapM (fun value => SQLSurface.value (.integer value)) with
      | .ok values => pure (values.map (fun value => [value]))
      | .error message => fail message
    unless results.flatMap (·.rows) == wanted do fail s!"application header values differ: {sql}"

def expectSQLiteApplicationHeaderFiles : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,k);INSERT INTO t VALUES(1,123);PRAGMA user_version=-1;PRAGMA application_id=2147483647;"
  let cancel := "SAVEPOINT a;PRAGMA user_version=4;SAVEPOINT b;PRAGMA application_id=5;ROLLBACK TO a;RELEASE a;"
  let publish := "BEGIN;PRAGMA user_version=-2147483648;PRAGMA application_id=-123;INSERT INTO t VALUES(2,456);COMMIT;"
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-application-headers.db"
    journal := ".lake/build/sqleanite-application-headers.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  let connection ← CoreFileEngine.create .system paths
  if !(← CoreFileEngine.execute connection setup).isOk then fail "header file setup"
  let original ← IO.FS.readBinFile paths.main
  if !(← CoreFileEngine.execute connection cancel).isOk then fail "header file savepoint rollback"
  unless (← IO.FS.readBinFile paths.main) == original do fail "rolled-back headers changed main bytes"
  if !(← CoreFileEngine.execute connection publish).isOk then fail "header file transaction commit"
  let reopened ← CoreFileEngine.reopen .system paths
  let state ← CoreFileEngine.snapshot reopened
  unless state.headers.main.userVersion.val == 2147483648 &&
      state.headers.main.applicationId.val == 4294967173 do fail "reopened header values differ"
  let wal : CoreWALFileAdapter.Paths := {
    main := ".lake/build/sqleanite-application-headers-wal.db"
    wal := ".lake/build/sqleanite-application-headers-wal.db-wal" }
  if ← wal.wal.pathExists then IO.FS.removeFile wal.wal
  if ← wal.main.pathExists then IO.FS.removeFile wal.main
  CoreWALFileAdapter.create .system wal Core.Database.empty
  if !(← CoreWALFileEngine.execute .system wal setup).isOk then fail "header WAL setup"
  let beforeMain ← IO.FS.readBinFile wal.main
  let beforeWAL ← IO.FS.readBinFile wal.wal
  if !(← CoreWALFileEngine.execute .system wal cancel).isOk then fail "header WAL savepoint rollback"
  unless (← IO.FS.readBinFile wal.main) == beforeMain && (← IO.FS.readBinFile wal.wal) == beforeWAL do
    fail "rolled-back headers changed main/WAL bytes"
  if !(← CoreWALFileEngine.execute .system wal publish).isOk then fail "header WAL transaction commit"
  let (_, metadata) ← CoreWALFileAdapter.reopenWithMetadata wal
  unless metadata == state.headers.main do fail "WAL overlay header values differ"
  unless (← IO.FS.readBinFile wal.main) == beforeMain do fail "WAL metadata write changed main before checkpoint"
  CoreWALFileEngine.checkpoint .system wal
  let header ← CoreFileAdapter.readHeader wal.main
  unless CoreMultiFreelist.HeaderMetadata.fromHeader header == metadata do fail "checkpoint lost header metadata"

def expectSQLiteSchemaPragma : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY NOT NULL,v TEXT);CREATE INDEX Iv ON t(v);CREATE UNIQUE INDEX Ii ON t(id);CREATE TABLE Tags(Key TEXT PRIMARY KEY,Owner int);INSERT INTO t VALUES(1,'one');" with
    | .ok result => pure result
    | .error message => fail message
  let check := fun (state : Core.State) (sql : String) (expected : List (List Value)) => do
    let (next, results) ← match CoreSQL.execute state sql with
      | .ok result => pure result
      | .error message => fail s!"schema PRAGMA {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do
      fail s!"schema PRAGMA {sql} returned different metadata"
    unless next.database.Equiv state.database do fail "schema PRAGMA mutated table/index state"
  check state "PRAGMA TaBLe_InFo(t);"
    [[.integer 0,.text "id",.text "INTEGER",.integer 1,.null,.integer 1],
      [.integer 1,.text "v",.text "TEXT",.integer 0,.null,.integer 0]]
  check state "PRAGMA table_xinfo='TAGS';"
    [[.integer 0,.text "Key",.text "TEXT",.integer 0,.null,.integer 1,.integer 0],
      [.integer 1,.text "Owner",.text "INT",.integer 0,.null,.integer 0,.integer 0]]
  check state "PRAGMA index_list(\"T\");"
    [[.integer 0,.text "Ii",.integer 1,.text "c",.integer 0],
      [.integer 1,.text "Iv",.integer 0,.text "c",.integer 0]]
  check state "PRAGMA index_list(Tags);"
    [[.integer 0,.text "sqlite_autoindex_Tags_1",.integer 1,.text "pk",.integer 0]]
  check state "PRAGMA index_info(iV);" [[.integer 0,.integer 1,.text "v"]]
  check state "PRAGMA index_xinfo='IV';"
    [[.integer 0,.integer 1,.text "v",.integer 0,.text "BINARY",.integer 1],
      [.integer 1,.integer (-1),.null,.integer 0,.text "BINARY",.integer 0]]
  for name in ["table_info","table_xinfo","index_list","index_info","index_xinfo"] do
    check state ("PRAGMA " ++ name ++ ";") []
    check state ("PRAGMA " ++ name ++ "('missing');") []
  let (changed, _) ← match CoreSQL.execute state
      "DROP INDEX Iv;ALTER TABLE t ADD NewCol REAL;CREATE INDEX NewIndex ON t(NewCol);ALTER TABLE t RENAME COLUMN NewCol TO Final;" with
    | .ok result => pure result
    | .error message => fail message
  check changed "PRAGMA index_info(NewIndex);" [[.integer 0,.integer 2,.text "Final"]]
  check changed "PRAGMA index_info(Iv);" []
  let some image := CoreFile.encode changed.database | fail "PRAGMA encode failed"
  let some restored := CoreDecode.decode image.fileBytes | fail "PRAGMA reopen failed"
  check { database := restored } "PRAGMA index_info(NewIndex);"
    [[.integer 0,.integer 2,.text "Final"]]
  let parsed ← match CoreTokenGrammar.parseCertified "PRAGMA table_info(t);" with
    | .ok parsed => pure parsed
    | .error message => fail message
  if (CoreTokenGrammar.check parsed.tokens #[.pragma "index_list" (some (.column none "t"))]).isOk then
    fail "PRAGMA token replay accepted a different operation"
  if (CoreTokenGrammar.check parsed.tokens #[.pragma "table_info" (some (.column none "Tags"))]).isOk then
    fail "PRAGMA token replay accepted a different target"
  for sql in ["PRAGMA table_info='t');", "PRAGMA table_info('t';",
      "PRAGMA table_info(t+1);", "PRAGMA table_info('t','Tags');",
      "PRAGMA table_info(('t'));", "PRAGMA table_info=(t);",
      "PRAGMA table_info(select);", "PRAGMA table_info(where);"] do
    if (CoreSQL.execute state sql).isOk then fail s!"PRAGMA admitted invalid syntax: {sql}"

def expectSQLiteIndexSchema : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY ASC,v REAL);CREATE INDEX Ix ON t(v ASC);INSERT INTO t VALUES(1,1),(2,1.5),(3,NULL);" with
    | .ok result => pure result
    | .error message => fail s!"ascending index setup: {message}"
  let some image := CoreFile.encode state.database | fail "index schema encode failed"
  let pages := image.pages.map (·.bytes)
  let some catalog := CoreDecode.decodeCatalogForOpen pages.head! | fail "index catalog missing"
  let some entry := catalog.find? (fun entry => entry.kind == "index") | fail "index entry missing"
  let source := CoreDecode.PageSource.ofList pages
  let ioSource : CoreDecode.IOPageSource := {
    pageCount := pages.length
    readPage := fun number => pure (CoreDecode.page? pages number) }
  let database := state.database.withoutIndexes
  for sql in ["CREATE INDEX Ix ON t(v)", "CREATE INDEX Ix ON t(v ASC)",
      "CREATE INDEX Ix /* ; */ ON t(v);DELETE FROM t;",
      "CREATE INDEX Ix ON t(v);broken \"", "CREATE INDEX IX ON T(V)"] do
    let changed := { entry with sql := some sql }
    let some pureLoaded := CoreDecode.applyIndexFrom source database changed |
      fail s!"pure schema admission rejected {sql}"
    let some ioLoaded ← CoreDecode.applyIndexIOFrom ioSource database changed |
      fail s!"IO schema admission rejected {sql}"
    unless pureLoaded.Equiv state.database && ioLoaded.Equiv state.database do
      fail "catalog parsing changed table rows or index metadata"
  for sql in ["UPDATE t SET v=9;", "DELETE FROM t;", "DROP TABLE t;",
      "CREATE TABLE Ix(x)", "CREATE INDEX Other ON t(v)",
      "CREATE INDEX Ix ON missing(v)", "CREATE INDEX Ix ON t(missing)",
      " CREATE INDEX Ix ON t(v)", "/*prefix*/CREATE INDEX Ix ON t(v)",
      "CREATE INDEX Ix ON t(v DESC)", "CREATE INDEX Ix ON t(v) WHERE v IS NOT NULL",
      "CREATE INDEX Ix ON t(v+1)"] do
    let changed := { entry with sql := some sql }
    unless (CoreDecode.applyIndexFrom source database changed).isNone &&
        (← CoreDecode.applyIndexIOFrom ioSource database changed).isNone do
      fail s!"catalog accepted an unsupported or mismatched description: {sql}"
  let some table := database.findTable? "t" | fail "index source missing"
  let some (_, index) := CoreDecode.indexMetadata database entry | fail "index metadata missing"
  let expected := CoreDecode.expectedIndexEntries table index
  let some physicalInteger := (SQLSurface.value (.integer 1)).toOption | fail "integer conversion"
  let compact := expected.map fun entry =>
    if entry.rowid.value == 1 then { entry with value := physicalInteger } else entry
  unless (CoreDecode.checkedIndex table index compact).isSome do
    fail "integral REAL index serial type was rejected"
  let some wrongType := (SQLSurface.value (.text "1")).toOption | fail "text conversion"
  let damaged := expected.map fun entry =>
    if entry.rowid.value == 1 then { entry with value := wrongType } else entry
  unless (CoreDecode.checkedIndex table index damaged).isNone &&
      (CoreDecode.checkedIndex table index expected.reverse).isNone &&
      (CoreDecode.checkedIndex table index expected.tail!).isNone do
    fail "index content validation changed types, ignored order, or missed an entry"
  let first := "CREATE INDEX \"semi;colon\" ON t(\"v\");"
  unless CoreSchemaSQL.firstStatement (first ++ "broken \"") == some first do
    fail "schema first-statement boundary split a quoted identifier"
  let parsedSchema := CoreDecode.parseTableSchema
    "CREATE TABLE t(id INTEGER PRIMARY KEY ASC,v REAL);DELETE FROM t;"
  unless parsedSchema.isSome do fail "table metadata did not stop after its first statement"
  let foreignSql := "CREATE TABLE t(id INTEGER,v INTEGER,FOREIGN KEY(v) REFERENCES parent(id))"
  unless (CoreDecode.parseTableSchema foreignSql).isSome do
    fail "table metadata rejected a supported foreign key"
  let (foreignState, _) ← match CoreSourceSQL.execute Core.State.empty foreignSql with
    | .ok result => pure result | .error message => fail message
  let some foreignTable := foreignState.database.findTable? "t" | fail "foreign-key metadata table is missing"
  let foreignKeys ← match CoreForeignKeyData.keys foreignTable with
    | .ok result => pure result | .error message => fail message
  unless foreignKeys == [(1, { table := "parent", column := some "id" })] do
    fail "table metadata did not preserve the foreign-key child position and parent target"
  for sql in ["CREATE INDEX i ON t(v DESC);", "CREATE TABLE d(id INTEGER PRIMARY KEY DESC);"] do
    if (CoreSQL.execute state sql).isOk then fail "unsupported descending metadata was discarded"

def expectSQLiteSchemaDropColumn : IO Unit := do
  for definition in ["A INTEGER,B TEXT,C INTEGER PRIMARY KEY",
      "A INTEGER,B TEXT PRIMARY KEY,C INTEGER", "A INTEGER,B TEXT,C INTEGER"] do
    let sql := s!"CREATE TABLE t({definition});CREATE INDEX Ci ON t(C);" ++
      "INSERT INTO t(A,B,C,rowid) VALUES(101,'one',10,17),(202,'two',20,91);"
    let (state, _) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail message
    let some before := state.database.findTable? "t" | fail "DROP COLUMN source missing"
    let (next, results) ← match CoreSQL.execute state
        "ALTER TABLE T DROP COLUMN a;SELECT B,oid FROM t WHERE C IN (10,17) ORDER BY oid;" with
      | .ok result => pure result
      | .error message => fail s!"DROP COLUMN: {message}"
    let some after := next.database.findTable? "t" | fail "DROP COLUMN table missing"
    unless after.schema.catalogColumns.map (·.name) == ["B","C"] do fail "DROP COLUMN removed wrong metadata"
    unless after.rows.map (·.rowid) == before.rows.map (·.rowid) do fail "DROP COLUMN changed rowids"
    unless (after.indexes.find? (fun index => index.name == "Ci")).map (·.column) == some 1 do
      fail "DROP COLUMN did not shift the existing index to C's new position"
    let expected : List (List Value) := [[.text "one",.integer 17]]
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail "DROP COLUMN changed indexed query results"
    let some image := CoreFile.encode next.database | fail "DROP COLUMN encode failed"
    let some reopened := CoreDecode.decode image.fileBytes | fail "DROP COLUMN reopen failed"
    let some restored := reopened.findTable? "t" | fail "DROP COLUMN table lost on reopen"
    unless decide (restored.schema = after.schema) && decide (restored.rows = after.rows) do
      fail "DROP COLUMN metadata/data changed on reopen"
    for sql in ["ALTER TABLE t DROP C;", "ALTER TABLE t DROP missing;", "ALTER TABLE t DROP rowid;"] do
      if (CoreSQL.execute next sql).isOk then fail s!"DROP COLUMN constraint omitted: {sql}"
    if definition == "A INTEGER,B TEXT PRIMARY KEY,C INTEGER" then
      if (CoreSQL.execute next "ALTER TABLE t DROP B;").isOk then fail "DROP removed the TEXT primary key"
    let (rolled, _) ← match CoreSQL.execute state "BEGIN;ALTER TABLE t DROP A;ROLLBACK;" with
      | .ok result => pure result
      | .error message => fail message
    let some rolledTable := rolled.database.findTable? "t" | fail "DROP COLUMN rollback lost table"
    unless decide (rolledTable.schema = before.schema) do fail "DROP COLUMN rollback kept changed schema"
  for sql in ["CREATE TABLE one(v);ALTER TABLE one DROP v;",
      "CREATE TABLE one(k INTEGER PRIMARY KEY,v);ALTER TABLE one DROP k;"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail "DROP removed last or primary-key column"
  let (_, results) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE shadow(rowid TEXT,v);INSERT INTO shadow(rowid,v,oid) VALUES('r',5,27);ALTER TABLE shadow DROP rowid;SELECT rowid,v FROM shadow;" with
    | .ok result => pure result
    | .error message => fail message
  let expected : List (List Value) := [[.integer 27,.integer 5]]
  let rows ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (results.getLast?).map (·.rows) == some rows do fail "DROP did not restore the implicit rowid alias"
  let parsed ← match CoreTokenGrammar.parseCertified "ALTER TABLE t DROP COLUMN B;" with
    | .ok parsed => pure parsed
    | .error message => fail message
  if (CoreTokenGrammar.check parsed.tokens #[.alterDropColumn "t" "A"]).isOk then
    fail "DROP checker accepted a different target column"

def expectSQLiteSchemaAdd : IO Unit := do
  for key in ["INTEGER PRIMARY KEY","INTEGER","TEXT PRIMARY KEY"] do
    let sql := s!"CREATE TABLE t(Id {key},V TEXT);CREATE INDEX Vi ON t(V);" ++
      "INSERT INTO t(Id,V,rowid) VALUES(1,'one',17),(2,NULL,91);"
    let (state, _) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail message
    let some before := state.database.findTable? "t" | fail "ADD source missing"
    let (next, _) ← match CoreSQL.execute state
        "ALTER TABLE T ADD COLUMN Added TEXT;ALTER TABLE t ADD Another INTEGER;" with
      | .ok result => pure result
      | .error message => fail s!"ADD COLUMN: {message}"
    let some after := next.database.findTable? "t" | fail "ADD target missing"
    unless after.schema.catalogColumns.map (·.name) == ["Id","V","Added","Another"] do
      fail "ADD misplaced a visible column or exposed the internal rowid"
    unless after.rows.map (·.rowid) == before.rows.map (·.rowid) &&
        decide (after.indexes = before.indexes) do fail "ADD changed rowids or existing index positions"
    for (old, current) in before.rows.zip after.rows do
      let fields := CoreRecord.rowRecordFields before.schema old
      unless decide (CoreRecord.decodeRowFields after.schema old.rowid fields = some current) do
        fail "older record did not acquire NULLs for omitted added columns"
    let some image := CoreFile.encode next.database | fail "ADD encode failed"
    let some reopened := CoreDecode.decode image.fileBytes | fail "ADD reopen failed"
    let some restored := reopened.findTable? "t" | fail "ADD table missing after reopen"
    unless decide (restored.schema = after.schema) && decide (restored.rows = after.rows) do
      fail "ADD metadata or values changed after reopen"
    let (_, results) ← match CoreSQL.execute { database := reopened }
        "UPDATE t SET Added=3,Another='4';SELECT typeof(Added),Added,typeof(Another),Another FROM t ORDER BY oid;" with
      | .ok result => pure result
      | .error message => fail message
    let expected : List (List Value) := List.replicate 2 [.text "text",.text "3",.text "integer",.integer 4]
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail "added column affinity changed"
    for sql in ["ALTER TABLE t ADD Required TEXT NOT NULL;", "ALTER TABLE t ADD ID;",
        "ALTER TABLE t ADD NewKey INTEGER PRIMARY KEY;", "ALTER TABLE t ADD UniqueValue UNIQUE;"] do
      if (CoreSQL.execute state sql).isOk then fail s!"ADD constraint error omitted: {sql}"
    let (rolled, _) ← match CoreSQL.execute state "BEGIN;ALTER TABLE t ADD Rolled;ROLLBACK;" with
      | .ok result => pure result
      | .error message => fail message
    let some rolledTable := rolled.database.findTable? "t" | fail "ADD rollback lost table"
    unless decide (rolledTable.schema = before.schema) do fail "ADD rollback kept new column"
  unless (CoreSQL.execute Core.State.empty
      "CREATE TABLE e(Id INTEGER PRIMARY KEY);ALTER TABLE e ADD Required TEXT NOT NULL;INSERT INTO e VALUES(1,'ok');").isOk do
    fail "empty-table ADD NOT NULL rejected"
  let parsed ← match CoreTokenGrammar.parseCertified "ALTER TABLE t ADD NewName TEXT;" with
    | .ok parsed => pure parsed
    | .error message => fail message
  if (CoreTokenGrammar.check parsed.tokens #[.alterAddColumn "t" { name := "newname", declaredType := "TEXT" }]).isOk then
    fail "ADD checker changed the declared column spelling"

def expectSQLiteEmptyIndex : IO Unit := do
  let setup := "CREATE TABLE Users(Id INTEGER PRIMARY KEY,Label TEXT);INSERT INTO users VALUES(1,'one'),(2,'two');" ++
    "CREATE UNIQUE INDEX \"\" ON users(Label);"
  let (state, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail s!"empty index name: {message}"
  let some stored := state.database.findTable? "Users" | fail "empty index table missing"
  unless stored.indexes.map (·.name) == [""] do fail "empty index name changed"
  let some image := CoreFile.encode state.database | fail "empty index encode failed"
  let some reopened := CoreDecode.decode image.fileBytes | fail "empty index reopen failed"
  let some restored := reopened.findTable? "Users" | fail "empty index table lost on reopen"
  unless decide (restored.indexes = stored.indexes) do fail "empty index metadata changed"
  let (renamed, _) ← match CoreSQL.execute { database := reopened }
      "ALTER TABLE users RENAME TO People;ALTER TABLE people RENAME Label TO Caption;" with
    | .ok result => pure result
    | .error message => fail message
  let some people := renamed.database.findTable? "People" | fail "empty-index table rename failed"
  unless people.indexes.map (·.name) == [""] do fail "table/column rename renamed explicit empty index"
  for sql in ["CREATE INDEX \"\" ON users(Id);", "CREATE TABLE \"\"(v);",
      "ALTER TABLE users RENAME TO \"\";", "INSERT INTO users VALUES(3,'one');"] do
    if (CoreSQL.execute state sql).isOk then fail s!"empty index conflict omitted: {sql}"
  let (skipped, _) ← match CoreSQL.execute state "CREATE INDEX IF NOT EXISTS \"\" ON users(missing);" with
    | .ok result => pure result
    | .error message => fail message
  unless (CoreNames.index? ((skipped.database.findTable? "Users").getD stored) "").isSome do
    fail "empty index IF NOT EXISTS lost existing index"
  let (dropped, _) ← match CoreSQL.execute state "DROP INDEX \"\";CREATE TABLE \"\"(v);" with
    | .ok result => pure result
    | .error message => fail message
  let some users := dropped.database.findTable? "Users" | fail "DROP empty index dropped its table"
  unless users.indexes.isEmpty && (dropped.database.findTable? "").isSome do
    fail "empty index name was not released"

end SQLeanite.Tests
