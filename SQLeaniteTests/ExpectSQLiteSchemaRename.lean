import SQLeaniteTests.ExpectSQLiteAutoIncrement

namespace SQLeanite.Tests
open SQLeanite

def expectSQLiteSchemaRename : IO Unit := do
  let quote (name : String) := String.ofList (CanonicalSchemaSQL.quoteChars name)
  let setup := "CREATE TABLE Users(Id INTEGER PRIMARY KEY,Label TEXT,Val INTEGER);" ++
    "CREATE INDEX LabelIndex ON Users(Label);CREATE TABLE Tags(KeY TEXT PRIMARY KEY,Owner INTEGER);" ++
    "INSERT INTO USERS VALUES(1,'one',10),(2,'two',20);INSERT INTO TAGS VALUES('a',1),(NULL,2);"
  let (state, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  for table in ["Users","Tags"] do
    let some original := state.database.findTable? table | fail "rename source missing"
    for name in ["People","","Dotted.Name","Quo\"Ted","Ä"] do
      let sql := s!"ALTER TABLE {table.toLower} RENAME TO {quote name};SELECT * FROM {quote name} ORDER BY oid;"
      let (next, _) ← match CoreSQL.execute state sql with
        | .ok result => pure result
        | .error message => fail s!"table rename: {sql}: {message}"
      let some renamed := next.database.findTable? name | fail "renamed table missing"
      unless decide (renamed.rows = original.rows) do fail "table rename changed rows or rowids"
      unless (next.database.findTable? table).isNone do fail "old table name survived"
      unless renamed.indexes.map (·.name) == (if table == "Users" then ["LabelIndex"] else ["sqlite_autoindex_" ++ name ++ "_1"]) do
        fail "table rename changed wrong index names"
      let some image := CoreFile.encode next.database | fail "renamed table encode failed"
      let some reopened := CoreDecode.decode image.fileBytes | fail "renamed table reopen failed"
      let some restored := reopened.findTable? name | fail "renamed table missing on reopen"
      unless decide (restored.schema = renamed.schema) && decide (restored.rows = renamed.rows) do
        fail "renamed table metadata/data changed after reopen"
    for old in original.schema.catalogColumns.map (·.name) do
      for name in [old.toLower,"Caption","","Dotted.Name","rowid"] do
        let sql := s!"ALTER TABLE {table.toLower} RENAME COLUMN {quote old} TO {quote name};SELECT * FROM {quote table};"
        let (next, _) ← match CoreSQL.execute state sql with
          | .ok result => pure result
          | .error message => fail s!"column rename: {sql}: {message}"
        let some renamed := next.database.findTable? table | fail "renamed column table missing"
        unless decide (renamed.rows = original.rows) && decide (renamed.indexes = original.indexes) do
          fail "column rename changed rows, rowids or index identities"
  for sql in ["ALTER TABLE USERS RENAME TO users;", "ALTER TABLE users RENAME TO Tags;",
      "ALTER TABLE users RENAME TO LabelIndex;", "ALTER TABLE users RENAME TO SQLiTE_new;",
      "ALTER TABLE users RENAME COLUMN Label TO ID;", "ALTER TABLE users RENAME rowid TO rid;"] do
    if (CoreSQL.execute state sql).isOk then fail s!"rename conflict omitted: {sql}"
  let (rolled, _) ← match CoreSQL.execute state "BEGIN;ALTER TABLE users RENAME TO TempName;ROLLBACK;" with
    | .ok result => pure result
    | .error message => fail message
  unless (rolled.database.findTable? "Users").isSome && (rolled.database.findTable? "TempName").isNone do
    fail "ROLLBACK retained a table rename"
  for (sql, forged) in [
      ("ALTER TABLE users RENAME TO NewName;", #[Statement.alterRenameTable "users" "newname"]),
      ("ALTER TABLE users RENAME Label TO NewName;", #[Statement.alterRenameColumn "users" "Label" "newname"]),
      ("CREATE TABLE Mixed(ID INTEGER PRIMARY KEY);", #[Statement.createTable "mixed" #[{ name := "ID", declaredType := "INTEGER", primaryKey := true }]]),
      ("CREATE INDEX Mixed ON users(Label);", #[Statement.createIndex "mixed" "users" #[.column none "Label"]])] do
    let tokens ← match lex sql with
      | .ok tokens => pure tokens
      | .error message => fail message
    if (CoreTokenGrammar.check tokens forged).isOk then fail "grammar changed declared-name spelling"
  -- A quoted period is one name; a real qualifier remains outside this AST's
  -- certified surface and must not accidentally address that literal name.
  let (dotted, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE \"main.t\"(v);INSERT INTO \"main.t\" VALUES(7);" with
    | .ok result => pure result
    | .error message => fail message
  if (CoreSQL.execute dotted "SELECT * FROM main.t;").isOk then
    fail "schema qualifier was confused with a quoted period"

def expectSQLiteSchemaCase : IO Unit := do
  let setup := "CREATE TABLE Users(Id INTEGER PRIMARY KEY,Label TEXT,Val INTEGER);" ++
    "CREATE INDEX LabelIndex ON uSeRs(lAbEl);" ++
    "CREATE TABLE Tags(KeY TEXT PRIMARY KEY,Owner INTEGER);" ++
    "INSERT INTO USERS VALUES(1,'one',10),(2,'two',20);" ++
    "INSERT INTO tAgS VALUES('a',1),('b',2);"
  let (state, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail s!"case-preserving schema: {message}"
  let some users := state.database.findTable? "Users" | fail "table spelling changed"
  unless users.schema.catalogColumns.map (·.name) == ["Id","Label","Val"] &&
      users.indexes.map (·.name) == ["LabelIndex"] do fail "column/index spelling changed"
  unless (CoreNames.table? state.database "uSeRs").map (·.schema.name) == some "Users" do
    fail "SQL table binding did not retain original name"
  let some image := CoreFile.encode state.database | fail "mixed-case schema encode failed"
  let some reopened := CoreDecode.decode image.fileBytes | fail "mixed-case schema reopen failed"
  let some restored := reopened.findTable? "Users" | fail "mixed-case table lost after reopen"
  unless decide (restored.schema = users.schema) && restored.indexes.map (·.name) == ["LabelIndex"] do
    fail "mixed-case metadata changed after reopen"
  for sql in ["SELECT U.iD,U.LaBeL FROM UsErS U WHERE u.ID>0 ORDER BY U.iD;",
      "SELECT USERS.* FROM users;", "SELECT LABEL,count(*) FROM USERS GROUP BY label;",
      "SELECT u.ID,t.KEY FROM USERS u JOIN TAGS t ON u.ID=t.OWNER ORDER BY u.ID;",
      "UPDATE users SET label=upper(LABEL) WHERE id=1 RETURNING USERS.Id,Label;",
      "INSERT INTO users(ID,LaBeL,VAL) VALUES(3,'three',30) RETURNING users.ID,LABEL;",
      "INSERT OR REPLACE INTO tags(KEY,OWNER) VALUES('a',2) RETURNING ROWID,Key;",
      "DELETE FROM uSeRs WHERE id=1 RETURNING ID,Label;",
      "DROP INDEX labelINDEX;", "DROP TABLE tAgS;",
      "CREATE TABLE IF NOT EXISTS USERS(ignored);",
      "CREATE INDEX IF NOT EXISTS labelINDEX ON USERS(missing);"] do
    unless (CoreSQL.execute { database := reopened } sql).isOk do
      fail s!"case-insensitive binding rejected: {sql}"
  for sql in ["CREATE TABLE USERS(other);", "CREATE TABLE labelindex(other);",
      "CREATE INDEX USERS ON users(Id);", "CREATE INDEX LABELINDEX ON users(Id);",
      "CREATE TABLE Bad(ID,id);", "DROP INDEX SQLITE_AUTOINDEX_TAGS_1;"] do
    if (CoreSQL.execute { database := reopened } sql).isOk then
      fail s!"case-insensitive schema conflict omitted: {sql}"
  let (_, results) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE Ä(Ä,ä);CREATE TABLE ä(v);INSERT INTO Ä VALUES(1,2);INSERT INTO ä VALUES(3);SELECT Ä,ä FROM Ä;SELECT v FROM ä;" with
    | .ok result => pure result
    | .error message => fail s!"non-ASCII names were folded: {message}"
  let expected : List (List Value) := [[.integer 3]]
  let rows ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (results.getLast?).map (·.rows) == some rows do fail "non-ASCII tables were merged"

def expectSQLiteIntegerNotNullMetadata : IO Unit := do
  for declared in [false,true] do
    for tableKey in [false,true] do
      for position in [0,1,2] do
        let keyColumn := "k INTEGER" ++ (if declared then " NOT NULL" else "") ++
          (if tableKey then "" else " PRIMARY KEY")
        let columns := match position with
          | 0 => [keyColumn,"v TEXT NOT NULL","w"]
          | 1 => ["v TEXT NOT NULL",keyColumn,"w"]
          | _ => ["v TEXT NOT NULL","w",keyColumn]
        let sql := "CREATE TABLE t(" ++ String.intercalate "," columns ++
          (if tableKey then ",PRIMARY KEY(k DESC)" else "") ++ ");" ++
          "INSERT INTO t(k,v,w) VALUES(NULL,'a',1),(NULL,'b',2);SELECT rowid,k FROM t ORDER BY rowid;"
        let (state, results) ← match CoreSQL.execute Core.State.empty sql with
          | .ok result => pure result
          | .error message => fail s!"INTEGER NOT NULL metadata: {message}"
        let some table := state.database.findTable? "t" | fail "INTEGER key table missing"
        let some key := table.schema.columns[table.schema.primaryKey]? | fail "INTEGER key column missing"
        unless key.notNull && key.integerPrimaryNotNull == declared do
          fail "INTEGER key confused internal non-NULL with declared NOT NULL"
        let some image := CoreFile.encode state.database | fail "INTEGER NOT NULL encode failed"
        let some reopened := CoreDecode.decode image.fileBytes | fail "INTEGER NOT NULL reopen failed"
        let some restored := reopened.findTable? "t" | fail "INTEGER NOT NULL table lost"
        unless decide (restored.schema = table.schema) do fail "INTEGER NOT NULL schema round-trip mismatch"
        let expected : List (List Value) := [[.integer 1,.integer 1],[.integer 2,.integer 2]]
        let rows ← match expected.mapM (List.mapM SQLSurface.value) with
          | .ok rows => pure rows
          | .error message => fail message
        unless (results.getLast?).map (·.rows) == some rows do fail "explicit INTEGER NOT NULL changed rowid allocation"
        if (CoreSQL.execute { database := reopened } "UPDATE t SET k=NULL;").isOk then
          fail "INTEGER key accepted a NULL rowid update"

def expectSQLiteInsertInputEvaluation : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL);INSERT INTO t VALUES(1,'one'),(2,'two');"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  for sql in ["INSERT INTO t(v,v) VALUES('kept',abs(-9223372036854775808));",
      "INSERT INTO t(id,id,v) VALUES(abs(-9223372036854775808),10,'kept');",
      "INSERT INTO t(v,v) VALUES('first',0 AND abs(-9223372036854775808)),('second',0);",
      "INSERT INTO t(v,v) SELECT 'kept',abs(-9223372036854775808) WHERE 0;"] do
    unless (CoreSQL.execute initial sql).isOk do fail s!"INSERT discarded-input rule rejected: {sql}"
  for policy in ["", " OR ABORT", " OR IGNORE", " OR REPLACE"] do
    for tail in ["", " RETURNING id,v"] do
      for values in ["('kept',abs(-9223372036854775808)),('second',1)",
          "('first',1),('kept',abs(-9223372036854775808))"] do
        let sql := s!"INSERT{policy} INTO t(v,v) VALUES{values}{tail};"
        if (CoreSQL.execute initial sql).isOk then fail s!"multi-VALUES discarded a source error: {sql}"
      let sql := s!"INSERT{policy} INTO t(id,id,v) VALUES(abs(-9223372036854775808),1,'one'),(10,11,'two'){tail};"
      if (CoreSQL.execute initial sql).isOk then fail "multi-VALUES skipped a discarded rowid source error"
  for sql in ["INSERT INTO t(v,v) VALUES('kept',no_function());",
      "INSERT INTO t(v,v) VALUES('first',0),('kept',no_function());",
      "INSERT INTO t(v,v) SELECT 'kept',abs(-9223372036854775808);"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"INSERT input error swallowed: {sql}"
  let (_, results) ← match CoreSQL.execute initial
      "INSERT INTO t(v,v) VALUES(CAST(X'80FF' AS TEXT),X'00'),(CAST(X'610062' AS TEXT),NULL) RETURNING id,hex(v);" with
    | .ok result => pure result
    | .error message => fail message
  let expected : List (List Value) := [[.integer 3,.text "80FF"],[.integer 4,.text "610062"]]
  let rows ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (results.getLast?).map (·.rows) == some rows do fail "materialized INSERT changed raw TEXT bytes"

def expectSQLiteTablePrimary : IO Unit := do
  for typ in ["INTEGER","TEXT"] do
    let keys := ["PRIMARY KEY(k)", "CONSTRAINT pk PRIMARY KEY(k ASC)",
      "PRIMARY KEY(k COLLATE BINARY ASC) ON CONFLICT ABORT"] ++
      (if typ == "INTEGER" then ["PRIMARY KEY(k DESC)", "PRIMARY KEY(k COLLATE unknown_collation DESC)"] else [])
    for key in keys do
      let sql := s!"CREATE TABLE t(v,k {typ},{key});" ++
        "INSERT INTO t(v,k) VALUES('a',NULL),('b',NULL);SELECT rowid,k,v FROM t ORDER BY rowid;"
      let (state, results) ← match CoreSQL.execute Core.State.empty sql with
        | .ok result => pure result
        | .error message => fail s!"table primary key: {message}"
      let expected : List (List Value) :=
        [[.integer 1,if typ == "INTEGER" then .integer 1 else .null,.text "a"],
         [.integer 2,if typ == "INTEGER" then .integer 2 else .null,.text "b"]]
      let rows ← match expected.mapM (List.mapM SQLSurface.value) with
        | .ok rows => pure rows
        | .error message => fail message
      unless (results.getLast?).map (·.rows) == some rows do fail s!"table key mismatch: {key}"
      let some image := CoreFile.encode state.database | fail "table key encode failed"
      let some reopened := CoreDecode.decode image.fileBytes | fail "table key reopen failed"
      let some table := reopened.findTable? "t" | fail "table key disappeared"
      unless table.schema.declaredPrimaryKey == 1 && table.rows.length == 2 do
        fail "table key changed column position on reopen"
  for sql in ["CREATE TABLE t(k TEXT,v,PRIMARY KEY(missing));",
      "CREATE TABLE t(k INTEGER PRIMARY KEY,v,PRIMARY KEY(k));",
      "CREATE TABLE t(k TEXT,v,PRIMARY KEY(k),PRIMARY KEY(v));",
      "CREATE TABLE t(k TEXT,PRIMARY KEY(k),v);",
      "CREATE TABLE t(k TEXT,v,PRIMARY KEY(k ASC DESC));"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"invalid table key admitted: {sql}"
  let setup := "CREATE TABLE t(k INTEGER,v,PRIMARY KEY(k));INSERT INTO t VALUES(1,'one'),(2,'two');"
  for (statement, expected) in [
      ("INSERT INTO t(rowid,k,v) VALUES(-10,NULL,'new') RETURNING k;", 3),
      ("INSERT INTO t(k,rowid,v) VALUES(NULL,-10,'new') RETURNING k;", -10),
      ("INSERT INTO t(k,k,v) VALUES(11,12,'new') RETURNING k;", 12),
      ("INSERT INTO t(rowid,k,v) VALUES(abs(-9223372036854775808),12,'new') RETURNING k;", 12)] do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ statement) with
      | .ok result => pure result
      | .error message => fail s!"INSERT rowid alias: {message}"
    let value ← match SQLSurface.value (.integer expected) with
      | .ok value => pure value
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [[value]] do fail "INSERT rowid alias did not use last value"
  -- These valid SQLite features remain outside Core; their parsed metadata
  -- must not be dropped and silently interpreted as ascending BINARY/ABORT.
  for sql in ["CREATE TABLE t(k TEXT,v,PRIMARY KEY(k DESC));",
      "CREATE TABLE t(k TEXT,v,PRIMARY KEY(k COLLATE nocase));",
      "CREATE TABLE t(k TEXT,v,PRIMARY KEY(k) ON CONFLICT FAIL);"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail "unsupported table-key semantics silently discarded"
    if (CoreDecode.parseTableSchema sql).isSome then fail "foreign table-key semantics silently discarded"
  let parsed ← match CoreTokenGrammar.parseCertified
      "CREATE TABLE t(k TEXT,v,CONSTRAINT pk PRIMARY KEY(k COLLATE binary));" with
    | .ok parsed => pure parsed
    | .error message => fail message
  let some (Statement.createTable name columns constraints ifNotExists) := parsed.statements[0]? | fail "missing table-key AST"
  let some constraint := constraints[0]? | fail "missing table-key constraint"
  for forged in [{ constraint with columns := #["v"] },
      { constraint with collations := #[some "nocase"] },
      { constraint with descending := #[true] }, { constraint with conflict := .ignore }] do
    if (CoreTokenGrammar.check parsed.tokens #[.createTable name columns #[forged] ifNotExists]).isOk then
      fail "table-key token certificate accepted changed semantics"

def expectSQLiteNullableTextPrimary : IO Unit := do
  let setup := "CREATE TABLE k(k TEXT PRIMARY KEY,v);" ++
    "INSERT INTO k VALUES('a','one'),('b','two'),(NULL,'null1'),(NULL,'null2');" ++
    "CREATE TABLE required(k TEXT PRIMARY KEY NOT NULL,v);INSERT INTO required VALUES('a',1);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let cases : List (String × List (List Value)) := [
    ("INSERT INTO k VALUES(NULL,'n3'),(NULL,'n4') RETURNING rowid,k;",
      [[.integer 5,.null],[.integer 6,.null]]),
    ("INSERT OR REPLACE INTO k VALUES('a','new');SELECT rowid,k FROM k ORDER BY rowid;",
      [[.integer 2,.text "b"],[.integer 3,.null],[.integer 4,.null],[.integer 5,.text "a"]]),
    ("INSERT OR REPLACE INTO k SELECT 'a','new';SELECT rowid,k FROM k ORDER BY rowid;",
      [[.integer 2,.text "b"],[.integer 3,.null],[.integer 4,.null],[.integer 5,.text "a"]]),
    ("UPDATE k SET k=NULL RETURNING rowid,k;",
      [[.integer 1,.null],[.integer 2,.null],[.integer 3,.null],[.integer 4,.null]]),
    ("UPDATE k SET rowid=rowid-10 WHERE k IS NULL RETURNING rowid,k;",
      [[.integer (-7),.null],[.integer (-6),.null]]),
    ("SELECT rowid FROM k WHERE k=NULL;", []),
    ("SELECT rowid FROM k WHERE k IS NULL ORDER BY rowid;", [[.integer 3],[.integer 4]]),
    ("INSERT INTO k VALUES(123,'number'),(X'313233','blob') RETURNING typeof(k),hex(k);",
      [[.text "text",.text "313233"],[.text "blob",.text "313233"]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute initial sql with
      | .ok result => pure result
      | .error message => fail s!"nullable TEXT key: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do
      fail s!"nullable TEXT key mismatch: {sql}"
  let image ← match CoreFile.encode initial.database with
    | some image => pure image
    | none => fail "nullable TEXT key could not be encoded"
  let reopened ← match CoreDecode.decode image.fileBytes with
    | some database => pure database
    | none => fail "nullable TEXT key could not be reopened"
  for (name, notNull) in [("k",false),("required",true)] do
    let some table := reopened.findTable? name | fail "TEXT key round-trip lost table"
    unless table.schema.catalogColumns.head?.map (·.notNull) == some notNull do
      fail "TEXT key round-trip changed explicit nullability"
  for sql in ["INSERT INTO required VALUES(NULL,2);", "UPDATE required SET k=NULL;",
      "INSERT INTO k VALUES('a','duplicate');"] do
    if (CoreSQL.execute { database := reopened } sql).isOk then
      fail s!"TEXT key round-trip lost constraint: {sql}"

  let path : System.FilePath := ".lake/build/sqleanite-null-key-foreign.db"
  if ← path.pathExists then IO.FS.removeFile path
  let created ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[path.toString, "-batch", "-bail",
      "PRAGMA page_size=4096;CREATE TABLE k(k TEXT PRIMARY KEY,v);" ++
      "INSERT INTO k VALUES('a',1),('b',2),(NULL,3);"] }
  unless created.exitCode == 0 do fail s!"foreign NULL-key fixture: {created.stderr}"
  let bytes ← IO.FS.readBinFile path
  unless (CoreDecode.decode bytes.data.toList).isSome do
    fail "first pointer at content start hid a backwards foreign index pointer"
  let reopened ← CoreFileAdapter.reopen {
    main := path, journal := ".lake/build/sqleanite-null-key-foreign.db-journal" }
  unless (reopened.findTable? "k").map (fun table => table.rows.length) == some 3 do
    fail "IO decoder lost a NULL-key row in a foreign index layout"

def expectSQLiteUpdateTuples : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER);CREATE UNIQUE INDEX tu ON t(u);" ++
    "INSERT INTO t VALUES(1,'a',1),(2,'b',2),(3,'c',3);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let cases : List (String × List (List Value)) := [
    ("UPDATE t SET (v,u)=(u,v) RETURNING *;",
      [[.integer 1,.text "1",.text "a"],[.integer 2,.text "2",.text "b"],[.integer 3,.text "3",.text "c"]]),
    ("UPDATE t SET (v,u)=((('x',9))) WHERE id=1 RETURNING *;", [[.integer 1,.text "x",.integer 9]]),
    ("UPDATE t SET (u,u)=(abs(-9223372036854775808),9) WHERE id=1 RETURNING *;", [[.integer 1,.text "a",.integer 9]]),
    ("UPDATE t SET u=abs(-9223372036854775808),(u,v)=(9,'x') WHERE id=1 RETURNING *;", [[.integer 1,.text "x",.integer 9]]),
    ("UPDATE OR REPLACE t SET (id,v)=(id+1,v||'x') RETURNING id,v;",
      [[.integer 2,.text "ax"],[.integer 3,.text "axx"],[.integer 4,.text "axxx"]]),
    ("UPDATE t SET (u)=9 WHERE id=1 RETURNING u;", [[.integer 9]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute initial sql with
      | .ok result => pure result
      | .error message => fail s!"UPDATE tuple: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"UPDATE tuple mismatch: {sql}"
  for sql in ["UPDATE t SET (v,u)=(1) WHERE 0;", "UPDATE t SET (u)=(1,2) WHERE 0;",
      "UPDATE t SET (v,u)=(1,2,3) WHERE 0;", "UPDATE t SET ()=() WHERE 0;",
      "UPDATE t SET (u,u)=(no_function(),9) WHERE 0;",
      "UPDATE t SET (missing,u)=(1,2) WHERE 0;"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"UPDATE tuple swallowed error: {sql}"
  for count in [2000,2001] do
    let sql := "UPDATE t SET " ++ String.intercalate "," (List.replicate count "u=1") ++ " WHERE 0;"
    unless (CoreSQL.execute initial sql).isOk == (count == 2000) do fail "UPDATE assignment limit mismatch"
  let sql := "UPDATE t SET (v,u)=(u,v) RETURNING *;"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed
    | .error message => fail message
  let some (Statement.update table alias _ condition conflict returning) := parsed.statements[0]? | fail "missing tuple UPDATE AST"
  let forged : Array Statement := #[.update table alias
    #[("v", .literal (.integer 99)), ("u", .column none "v")] condition conflict returning]
  if (CoreTokenGrammar.check parsed.tokens forged).isOk then fail "tuple grammar accepted changed RHS"

def expectSQLiteUpdateReturning : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER);CREATE UNIQUE INDEX tu ON t(u);" ++
    "CREATE INDEX tv ON t(v);INSERT INTO t VALUES(1,'b',1),(2,'a',2),(3,'c',3);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let cases : List (String × Nat × List (List Value)) := [
    ("UPDATE OR IGNORE t SET u=100 WHERE v>='a' RETURNING id,v,u;", 1,
      [[.integer 1,.text "b",.integer 100]]),
    ("UPDATE OR REPLACE t SET id=id+1,v=v||'x' RETURNING id,v,u;", 3,
      [[.integer 2,.text "bx",.integer 1],[.integer 3,.text "bxx",.integer 1],[.integer 4,.text "bxxx",.integer 1]]),
    ("UPDATE t SET v=v||'x',u=u+10 RETURNING t.id,t.v,t.u;", 3,
      [[.integer 1,.text "bx",.integer 11],[.integer 2,.text "ax",.integer 12],[.integer 3,.text "cx",.integer 13]]),
    ("UPDATE OR IGNORE t SET v=NULL RETURNING abs(-9223372036854775808);", 0, []),
    ("UPDATE t AS x SET v=x.v||'x' WHERE x.id=1 RETURNING t.id,t.v;", 1, [[.integer 1,.text "bx"]]),
    ("UPDATE OR IGNORE t SET u=u+1 RETURNING id,v,u;", 1, [[.integer 3,.text "c",.integer 4]]),
    ("UPDATE t SET v=v WHERE 0 RETURNING abs(-9223372036854775808);", 0, [])]
  for (sql, changes, expected) in cases do
    let (_, results) ← match CoreSQL.execute initial sql with
      | .ok result => pure result
      | .error message => fail s!"UPDATE RETURNING: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows && (results.map (·.changes)).sum == changes do
      fail s!"UPDATE RETURNING mismatch: {sql}"
  for sql in ["UPDATE t AS x SET v='x' RETURNING x.id;",
      "UPDATE OR IGNORE t SET v=NULL RETURNING missing;",
      "UPDATE t SET v='x' WHERE 0 RETURNING no_function();",
      "UPDATE t SET v='x' RETURNING t.*;", "UPDATE t SET v='x' RETURNING sum(id);",
      "UPDATE t SET v='x' RETURNING 0 AND no_function();",
      "UPDATE t SET v='x' RETURNING CASE WHEN id=3 THEN abs(-9223372036854775808) ELSE id END;"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"UPDATE RETURNING swallowed error: {sql}"
  let sql := "UPDATE t SET v='x' RETURNING id;"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed
    | .error message => fail message
  let some (Statement.update table alias assignments condition conflict _) := parsed.statements[0]? | fail "missing UPDATE AST"
  let forged : Array Statement := #[.update table alias assignments condition conflict #[{ expr := .literal (.integer 99) }]]
  if (CoreTokenGrammar.check parsed.tokens forged).isOk then fail "UPDATE RETURNING accepted forged output expression"

def expectSQLiteInsertReturning : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER);CREATE UNIQUE INDEX tu ON t(u);" ++
    "INSERT INTO t VALUES(1,'a',1),(2,'b',2);CREATE TABLE implicit(v,w);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let cases : List (String × Nat × List (List Value)) := [
    ("INSERT OR IGNORE INTO t VALUES(1,'skip',9),(NULL,'keep',9),(NULL,'skip',9),(NULL,'last',10) RETURNING *;", 2,
      [[.integer 3,.text "keep",.integer 9],[.integer 4,.text "last",.integer 10]]),
    ("INSERT OR REPLACE INTO t VALUES(9,'first',9),(9,'second',10) RETURNING *;", 2,
      [[.integer 9,.text "first",.integer 9],[.integer 9,.text "second",.integer 10]]),
    ("INSERT INTO implicit DEFAULT VALUES RETURNING *,rowid;", 1, [[.null,.null,.integer 1]]),
    ("INSERT INTO t AS x(v,u) VALUES('x',9) RETURNING t.id,t.v;", 1, [[.integer 3,.text "x"]]),
    ("INSERT INTO implicit SELECT v,u FROM t ORDER BY id DESC RETURNING *,rowid;", 2,
      [[.text "b",.integer 2,.integer 1],[.text "a",.integer 1,.integer 2]]),
    ("INSERT OR IGNORE INTO t VALUES(1,'skip',9) RETURNING abs(-9223372036854775808);", 0, []),
    ("INSERT INTO t(v,u) SELECT v,u FROM t WHERE 0 RETURNING abs(-9223372036854775808);", 0, [])]
  for (sql, changes, expected) in cases do
    let (_, results) ← match CoreSQL.execute initial sql with
      | .ok result => pure result
      | .error message => fail s!"INSERT RETURNING: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows && (results.map (·.changes)).sum == changes do
      fail s!"INSERT RETURNING mismatch: {sql}"
  for sql in ["INSERT INTO t AS x(v,u) VALUES('x',9) RETURNING x.id;",
      "INSERT OR IGNORE INTO t VALUES(1,'skip',9) RETURNING missing;",
      "INSERT INTO t(v,u) SELECT v,u FROM t WHERE 0 RETURNING no_function();",
      "INSERT INTO t VALUES(9,'x',9) RETURNING t.*;",
      "INSERT INTO t VALUES(9,'x',9) RETURNING sum(id);",
      "INSERT INTO t VALUES(9,'x',9) RETURNING 0 AND no_function();",
      "INSERT INTO t VALUES(9,'x',9),(10,'y',10) RETURNING CASE WHEN id=10 THEN abs(-9223372036854775808) ELSE id END;"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"INSERT RETURNING swallowed error: {sql}"
  let sql := "INSERT INTO t VALUES(9,'x',9) RETURNING id;"
  let parsed ← match CoreTokenGrammar.parseCertified sql with
    | .ok parsed => pure parsed
    | .error message => fail message
  let some (Statement.insert table columns rows conflict _) := parsed.statements[0]? | fail "missing INSERT AST"
  let forged : Array Statement := #[.insert table columns rows conflict #[{ expr := .literal (.integer 99) }]]
  if (CoreTokenGrammar.check parsed.tokens forged).isOk then fail "INSERT RETURNING accepted forged output expression"

def expectSQLiteUpdateReplace : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER);CREATE UNIQUE INDEX tu ON t(u);" ++
    "INSERT INTO t VALUES(1,'a',1),(2,'b',2),(3,'c',3);" ++
    "CREATE TABLE k(k TEXT PRIMARY KEY NOT NULL,v);INSERT INTO k VALUES('a',1),('b',2);"
  let (initial, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail message
  let cases : List (String × Nat × List (List Value)) := [
    ("UPDATE OR REPLACE t SET id=id+1,v=v||'x';SELECT id,v,u FROM t ORDER BY id;", 3,
      [[.integer 4, .text "axxx", .integer 1]]),
    ("UPDATE OR REPLACE t SET id=id+1,v=v||'x' WHERE id<3;SELECT id,v,u FROM t ORDER BY id;", 2,
      [[.integer 3, .text "axx", .integer 1]]),
    ("UPDATE OR REPLACE t SET u=3,v=CASE WHEN id=3 THEN NULL ELSE v END;SELECT id,v,u FROM t ORDER BY id;", 2,
      [[.integer 2, .text "b", .integer 3]]),
    ("UPDATE OR REPLACE t SET u=3,v=CASE WHEN id=3 THEN abs(-9223372036854775808) ELSE v END;SELECT id,v,u FROM t ORDER BY id;", 2,
      [[.integer 2, .text "b", .integer 3]]),
    ("UPDATE OR REPLACE k SET k='a',v=v+1;SELECT k,v FROM k ORDER BY k;", 2,
      [[.text "a", .integer 3]])]
  for (sql, changes, expected) in cases do
    let (_, results) ← match CoreSQL.execute initial sql with
      | .ok result => pure result
      | .error message => fail s!"UPDATE OR REPLACE: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows && (results.map (·.changes)).sum == changes do
      fail s!"UPDATE OR REPLACE mismatch: {sql}"
  for sql in ["UPDATE OR REPLACE t SET id=NULL;", "UPDATE OR REPLACE t SET v=NULL;",
      "UPDATE OR REPLACE t SET v=no_function(),v='ok' WHERE 0;",
      "UPDATE OR REPLACE t SET u=1 WHERE CASE WHEN id=3 THEN abs(-9223372036854775808) ELSE 1 END;"] do
    if (CoreSQL.execute initial sql).isOk then fail s!"UPDATE OR REPLACE swallowed error: {sql}"

end SQLeanite.Tests
