import SQLeaniteTests.ExpectSQLiteQuotedNames

namespace SQLeanite.Tests
open SQLeanite

def expectSQLiteAutoIncrement : IO Unit := do
  let sql := "CREATE TABLE t(id INTEGER PRIMARY KEY AUTOINCREMENT,v TEXT NOT NULL);" ++
    "INSERT OR IGNORE INTO t(v) VALUES(NULL);INSERT INTO t(v) VALUES('first');DELETE FROM t;" ++
    "BEGIN;INSERT INTO t(v) VALUES('rolled back');ROLLBACK;INSERT INTO t(v) VALUES('committed');" ++
    "SELECT id,v FROM t;"
  let (state, output) ← match CoreSQL.execute Core.State.empty sql with
    | .ok result => pure result
    | .error message => fail s!"AUTOINCREMENT ignored/deleted/rolled-back rows: {message}"
  let expected ← match [Value.integer 3, .text "committed"].mapM SQLSurface.value with
    | .ok row => pure row
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some [expected] do fail "AUTOINCREMENT reused a committed or ignored rowid"
  let (_, sequenceOutput) ← match CoreSQL.execute state "SELECT seq FROM sqlite_sequence WHERE name='t';" with
    | .ok result => pure result
    | .error message => fail message
  let sequence ← match SQLSurface.value (.integer 3) with
    | .ok value => pure value
    | .error message => fail message
  unless (sequenceOutput.getLast?).map (·.rows) == some [[sequence]] do fail "AUTOINCREMENT sequence did not roll back"
  let some image := CoreFile.encode state.database | fail "AUTOINCREMENT encode failed"
  let some decoded := CoreDecode.decode image.fileBytes | fail "AUTOINCREMENT decode failed"
  unless decoded.Equiv state.database do fail "AUTOINCREMENT metadata or sequence changed during persistence"
  let (state, output) ← match CoreSQL.execute state
      "CREATE TABLE e(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO e(v) SELECT seq FROM sqlite_sequence WHERE name='e';SELECT count(*) FROM e;" with
    | .ok result => pure result
    | .error message => fail s!"empty AUTOINCREMENT SELECT: {message}"
  let zero ← match SQLSurface.value (.integer 0) with
    | .ok value => pure value
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some [[zero]] do fail "sequence write leaked into the INSERT source"
  let (state, _) ← match CoreSQL.execute state
      "INSERT INTO e(id,v) VALUES(9223372036854775807,'maximum');DELETE FROM e;" with
    | .ok result => pure result
    | .error message => fail message
  if (CoreSQL.execute state "INSERT INTO e(v) VALUES('overflow');").isOk then
    fail "AUTOINCREMENT reused a rowid after INT64_MAX"
  for sql in ["DROP TABLE sqlite_sequence;", "CREATE INDEX s ON sqlite_sequence(name);", "ALTER TABLE sqlite_sequence ADD extra;",
      "ALTER TABLE sqlite_sequence RENAME TO seq;"] do
    if (CoreSQL.execute state sql).isOk then fail "sqlite_sequence schema was modified"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE TABLE good(id INTEGER PRIMARY KEY AUTOINCREMENT);" with
    | .ok result => pure result
    | .error message => fail message
  let tokens ← match lex "CREATE TABLE good(id INTEGER PRIMARY KEY);" with
    | .ok result => pure result
    | .error message => fail message
  if (CoreTokenGrammar.check tokens parsed.statements).isOk then fail "token replay forged AUTOINCREMENT"

def expectSQLiteIndexedPrimaryTypes : IO Unit := do
  for typ in ["INT", "REAL", "NUMERIC", "BLOB", "", "\"\"", "\"INTEGER\" extra"] do
    let sql := s!"CREATE TABLE t(a {typ} PRIMARY KEY,b);" ++
      "INSERT INTO t(rowid,a,b) VALUES(2,1,'value'),(1,NULL,'null-one'),(3,NULL,'null-two');" ++
      "INSERT OR IGNORE INTO t(rowid,a,b) VALUES(4,1.0,'duplicate');SELECT rowid FROM t ORDER BY rowid;"
    let (state, output) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"indexed primary type {typ}: {message}"
    let expected ← match [[Value.integer 1],[.integer 2],[.integer 3]].mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"NULL namespace or INTEGER/REAL equality changed: {typ}"
    let some image := CoreFile.encode state.database | fail "indexed primary encode failed"
    let some decoded := CoreDecode.decode image.fileBytes | fail "indexed primary decode failed"
    unless decoded.Equiv state.database do fail s!"indexed primary persistence changed: {typ}"
  let sql := "CREATE TABLE t(a BLOB PRIMARY KEY,b);" ++
    "INSERT INTO t VALUES(-9223372036854775808,'minimum'),(0,'zero'),(9007199254740993,'large');" ++
    "INSERT OR IGNORE INTO t VALUES(-9223372036854775808.0,'duplicate minimum'),(-0.0,'duplicate zero'),(9007199254740992.0,'distinct');" ++
    "SELECT b FROM t ORDER BY rowid;"
  let (_, output) ← match CoreSQL.execute Core.State.empty sql with
    | .ok result => pure result
    | .error message => fail s!"numeric primary boundaries: {message}"
  let expected ← match [[Value.text "minimum"],[.text "zero"],[.text "large"],[.text "distinct"]].mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some expected do fail "numeric primary precision boundary changed"

def expectSQLiteColumnTypes : IO Unit := do
  for typ in ["TEXT 123", "BLOB notnull", "(12)", "TEXT(1+2)", "TEXT(1,2,3)",
      "TEXT(2) EXTRA", "RIGHT", "INDEXED", "TEXT(1_000)", "x'AB'"] do
    if (CoreSQL.execute Core.State.empty s!"CREATE TABLE bad(a {typ});").isOk then
      fail s!"illegal column type accepted: {typ}"
  for (source, expected) in [
      ("INTEGER /*c*/ GENERATED ALWAYS", "INTEGER /*c*/"),
      ("GENERATED ALWAYS", ""), ("INTgeneratedalways", "INT"),
      ("text always always", "text always"), ("\"text\" extra", "text"),
      ("\"integer\"(3)", "integer"), ("\"TEXT\"", "TEXT"),
      ("ıNTEGER", "ıNTEGER")] do
    unless SQLite.ColumnType.name source == expected do fail s!"type metadata mismatch: {source}"
  for typeName in ["", "text", "integer", "any", "INT", "custom \"type\""] do
    for notNull in [false, true] do
      let column := Core.Column.typed "column" typeName notNull
      unless CanonicalSchemaSQL.parseBaseColumn (CanonicalSchemaSQL.baseColumnChars column ++ [')']) ==
          some (column, [')']) do fail s!"typed-column persistence failed: {typeName}"
  let sql := "CREATE TABLE t(a,b \"\",c \"text\" extra,id INTEGER /*alias*/ PRIMARY KEY);" ++
    "INSERT INTO t(a,b,c) VALUES('007','007','007');" ++
    "SELECT typeof(a),typeof(b),typeof(c),id FROM t;"
  let (state, output) ← match CoreSQL.execute Core.State.empty sql with
    | .ok result => pure result
    | .error message => fail s!"column types: {message}"
  let expected ← match [Value.text "text", .text "integer", .text "text", .integer 1].mapM SQLSurface.value with
    | .ok row => pure row
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some [expected] do
    fail "absent/empty/custom type affinity or commented rowid alias changed"
  let some image := CoreFile.encode state.database | fail "column type encode failed"
  let some decoded := CoreDecode.decode image.fileBytes | fail "column type decode failed"
  unless decoded.Equiv state.database do fail "column types changed during persistence"
  let certified ← match CoreTokenGrammar.parseCertified "CREATE TABLE good(a text);" with
    | .ok result => pure result
    | .error message => fail message
  for source in ["CREATE TABLE good(a TEXT);", "CREATE TABLE good(a text extra);",
      "CREATE TABLE good(a text(1+2));"] do
    let tokens ← match lex source with
      | .ok tokens => pure tokens
      | .error message => fail message
    if (CoreTokenGrammar.check tokens certified.statements).isOk then
      fail "token replay accepted a forged type spelling or span"

def expectSQLiteNamedConstraints : IO Unit := do
  let sql := "CREATE TABLE t(id INTEGER CONSTRAINT key PRIMARY KEY ON CONFLICT IGNORE,a TEXT CONSTRAINT \"Null name\" NOT NULL ON CONFLICT IGNORE CONSTRAINT d DEFAULT 'value');INSERT INTO t DEFAULT VALUES;INSERT INTO t VALUES(1,'duplicate'),(2,NULL);SELECT * FROM t;"
  let (state, output) ← match CoreSQL.execute Core.State.empty sql with
    | .ok result => pure result
    | .error message => fail s!"named column constraints: {message}"
  let expected ← match [Value.integer 1, .text "value"].mapM SQLSurface.value with
    | .ok row => pure row
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some [expected] do fail "constraint names changed key, NULL or default behavior"
  let (state, _) ← match CoreSQL.execute state
      "CREATE TABLE r(id INTEGER,v,CONSTRAINT first,CONSTRAINT second PRIMARY KEY(id) ON CONFLICT REPLACE CONSTRAINT tail);INSERT INTO r VALUES(1,'first'),(1,'second');CREATE TABLE n(a,CONSTRAINT first CONSTRAINT second,CONSTRAINT final);INSERT INTO n DEFAULT VALUES;" with
    | .ok result => pure result
    | .error message => fail s!"standalone/repeated table constraint names: {message}"
  let some image := CoreFile.encode state.database | fail "named constraint encode failed"
  let some decoded := CoreDecode.decode image.fileBytes | fail "named constraint decode failed"
  unless decoded.Equiv state.database do fail "named constraints changed during persistence"
  for tail in ["CONSTRAINT NOT DEFAULT 7", "CONSTRAINT NULL NOT NULL", "CONSTRAINT NOTHING", "CONSTRAINT 0"] do
    if (CoreSQL.execute Core.State.empty s!"CREATE TABLE bad(a {tail});").isOk then fail "invalid constraint name accepted"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE TABLE good(a CONSTRAINT name NOT NULL);" with
    | .ok parsed => pure parsed
    | .error message => fail message
  let tokens ← match lex "CREATE TABLE good(a CONSTRAINT SELECT NOT NULL);" with
    | .ok tokens => pure tokens
    | .error message => fail message
  if (CoreTokenGrammar.check tokens parsed.statements).isOk then fail "token replay accepted a reserved constraint name"
  let key ← match CoreTokenGrammar.parseCertified "CREATE TABLE good(a INTEGER,PRIMARY KEY(a));" with
    | .ok parsed => pure parsed
    | .error message => fail message
  let namesOnly ← match lex "CREATE TABLE good(a INTEGER,CONSTRAINT ignored);" with
    | .ok tokens => pure tokens
    | .error message => fail message
  if (CoreTokenGrammar.check namesOnly key.statements).isOk then fail "a standalone name forged an actual key"

def expectSQLiteBlobAdjacency : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty "CREATE TABLE t(x INTEGER);INSERT INTO t VALUES(7);" with
    | .ok result => pure result
    | .error message => fail message
  for gap in [" ", "/*gap*/", "\n", "--gap\n"] do
    let (_, output) ← match CoreSQL.execute state s!"SELECT x{gap}'80ff' FROM t;" with
      | .ok result => pure result
      | .error message => fail s!"blob prefix was confused with a column alias: {message}"
    let expected ← match SQLSurface.value (.integer 7) with
      | .ok value => pure value
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some [[expected]] do fail "separated X token became a blob"
    if (CoreSQL.execute state s!"CREATE TABLE bad(a DEFAULT x{gap}'80ff');").isOk then
      fail "separated blob prefix entered persisted SQL"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE TABLE good(a DEFAULT X'80ff');" with
    | .ok parsed => pure parsed
    | .error message => fail message
  for leading in ["X ", "X/*gap*/", "'X'", "\"X\""] do
    let tokens ← match lex ("CREATE TABLE good(a DEFAULT " ++ leading ++ "'80ff');") with
      | .ok tokens => pure tokens
      | .error message => fail message
    if (CoreTokenGrammar.check tokens parsed.statements).isOk then
      fail "token replay accepted a forged blob prefix or boundary"

def expectSQLiteColumnDefaults : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY DEFAULT 99,a TEXT NOT NULL ON CONFLICT REPLACE DEFAULT (upper('default')),b INTEGER DEFAULT '0042');INSERT INTO t DEFAULT VALUES;INSERT OR REPLACE INTO t(id,a) VALUES(7,NULL);UPDATE t SET a=NULL WHERE id=1 RETURNING id,a,b;"
  let (state, output) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail s!"column defaults: {message}"
  let expected : List (List Value) := [[.integer 1,.text "DEFAULT",.integer 42]]
  let rows ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some rows do fail "DEFAULT allocation, affinity or UPDATE RETURNING mismatch"
  let some image := CoreFile.encode state.database | fail "DEFAULT encode failed"
  let some decoded := CoreDecode.decode image.fileBytes | fail "DEFAULT decode failed"
  unless decoded.Equiv state.database do fail "DEFAULT source changed during codec roundtrip"
  let (late, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE late(a DEFAULT (abs(-9223372036854775808)));INSERT INTO late(a) VALUES(7);" with
    | .ok result => pure result
    | .error message => fail s!"DEFAULT evaluated before use: {message}"
  if (CoreSQL.execute late "INSERT INTO late DEFAULT VALUES;").isOk then fail "DEFAULT runtime overflow omitted"
  for default in ["(not_a_function(1))", "(abs())", "(sum(1))", "(count(*))", "(-0x8000000000000000)"] do
    let (declared, _) ← match CoreSQL.execute Core.State.empty s!"CREATE TABLE delayed(a DEFAULT {default});" with
      | .ok result => pure result
      | .error message => fail s!"DEFAULT prepare error was raised during CREATE: {message}"
    if (CoreSQL.execute declared "INSERT INTO delayed DEFAULT VALUES;").isOk then
      fail "DEFAULT prepare error omitted during INSERT"
  for default in ["(0 AND other)", "(other IN ())", "(1 OR not_a_function(1))", "(FALSE AND not_a_function(1))"] do
    if !(CoreSQL.execute Core.State.empty s!"CREATE TABLE folded(a DEFAULT {default});INSERT INTO folded DEFAULT VALUES;").isOk then
      fail "DEFAULT constant folding did not follow SQLite's preparation stage"

  for default in ["(not_a_function(1))", "(abs(-9223372036854775808))"] do
    let (declared, _) ← match CoreSQL.execute Core.State.empty s!"CREATE TABLE emptySource(a NOT NULL ON CONFLICT REPLACE DEFAULT {default},b);" with
      | .ok result => pure result
      | .error message => fail message
    if (CoreSQL.execute declared "INSERT INTO emptySource(b) SELECT 1 WHERE 0;").isOk then
      fail "empty SELECT skipped omitted DEFAULT initialization"
    let updated := CoreSQL.execute declared "UPDATE OR REPLACE emptySource SET a=7;"
    unless updated.isOk == (default != "(not_a_function(1))") do
      fail "REPLACE DEFAULT preparation executed or skipped the wrong error stage"
    if !(CoreSQL.execute declared "UPDATE OR REPLACE emptySource SET b=7;").isOk then
      fail "UPDATE prepared the DEFAULT of an unchanged column"
  for sql in ["CREATE TABLE x(a DEFAULT (other));", "CREATE TABLE x(a DEFAULT abs(1));",
      "CREATE TABLE x(a DEFAULT +TRUE);", "CREATE TABLE x(a DEFAULT ?);"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"invalid DEFAULT accepted: {sql}"
  let (skipped, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE s(a NOT NULL ON CONFLICT REPLACE DEFAULT NULL,b NOT NULL ON CONFLICT IGNORE);INSERT INTO s VALUES(NULL,NULL);" with
    | .ok result => pure result
    | .error message => fail s!"REPLACE second pass ran before IGNORE: {message}"
  let some table := skipped.database.findTable? "s" | fail "DEFAULT skip table missing"
  unless table.rows.isEmpty do fail "DEFAULT NULL row was not ignored"
  let (old, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE old(a);INSERT INTO old VALUES(7);ALTER TABLE old ADD b TEXT DEFAULT 'old';" with
    | .ok result => pure result
    | .error message => fail message
  let some table := old.database.findTable? "old" | fail "old-record table missing"
  let some row := table.rows.head? | fail "old-record row missing"
  let fields := (CoreRecord.rowRecordFields table.schema row).take 1
  unless CoreRecord.decodeRowFields table.schema row.rowid fields == some row do
    fail "pre-ALTER record failed to supply its literal default"
  for default in ["( 'quote''*/--' /* trailing */ )", "+ /*middle*/ 1", "X'80FF00'", "foo", "x"] do
    let sql := s!"CREATE TABLE q(k TEXT PRIMARY KEY ON CONFLICT REPLACE NOT NULL ON CONFLICT IGNORE DEFAULT {default},n DEFAULT 1 DEFAULT 'last');"
    let (value, _) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"DEFAULT source spelling: {message}"
    let some encoded := CoreFile.encode value.database | fail "DEFAULT spelling encode failed"
    let some reopened := CoreDecode.decode encoded.fileBytes | fail "DEFAULT spelling decode failed"
    unless reopened.Equiv value.database do fail "DEFAULT framing changed source or constraint policies"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE TABLE x(a DEFAULT 7);" with
    | .ok parsed => pure parsed
    | .error message => fail message
  match parsed.statements.toList with
  | [.createTable name columns constraints flag] =>
      for forged in [columns.map (fun column => { column with defaultSql := some "8" }),
          columns.map (fun column => { column with defaultValue := some (.literal (.integer 8)) })] do
        if (CoreTokenGrammar.check parsed.tokens #[.createTable name forged constraints flag]).isOk then
          fail "token replay accepted a forged DEFAULT"
  | _ => fail "unexpected DEFAULT AST"
  if (ColumnDefault.fromSource "7);DROP TABLE t;--").isSome then fail "DEFAULT certificate accepted injected SQL"

def expectSQLiteSchemaPrimaryConflict : IO Unit := do
  let (ignored, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY ON CONFLICT IGNORE,a TEXT NOT NULL ON CONFLICT IGNORE);CREATE UNIQUE INDEX u ON t(a);INSERT INTO t VALUES(1,'a'),(2,'b');INSERT INTO t VALUES(1,'b'),(3,NULL);" with
    | .ok result => pure result
    | .error message => fail s!"primary IGNORE setup: {message}"
  let some table := ignored.database.findTable? "t" | fail "primary-policy table missing"
  unless table.rows.map (fun row => row.rowid.value) == [1,2] do fail "rowid IGNORE did not precede unique/NULL constraints"
  for sql in ["INSERT OR ABORT INTO t VALUES(1,'c');", "INSERT INTO t VALUES(3,'b');"] do
    if (CoreSQL.execute ignored sql).isOk then fail s!"primary IGNORE suppressed another constraint: {sql}"
  let (replaced, output) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE r(id INTEGER PRIMARY KEY ON CONFLICT REPLACE,a TEXT);INSERT INTO r VALUES(1,'a'),(2,'b');UPDATE r SET id=id+1 RETURNING id,a;" with
    | .ok result => pure result
    | .error message => fail s!"primary REPLACE pending rowids: {message}"
  let some table := replaced.database.findTable? "r" | fail "replacement table missing"
  unless table.rows.map (fun row => row.rowid.value) == [3] do fail "REPLACE update did not re-seek pending rowids"
  let expected : List (List Value) := [[.integer 2,.text "a"],[.integer 3,.text "a"]]
  let rows ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some rows do fail "REPLACE returning used an overwritten row's stale value"
  let (textKey, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE k(id TEXT,a TEXT NOT NULL ON CONFLICT REPLACE,PRIMARY KEY(id) ON CONFLICT REPLACE);INSERT INTO k VALUES('a','old'),('b','kept');INSERT INTO k VALUES('a','new');" with
    | .ok result => pure result
    | .error message => fail s!"table-level TEXT key REPLACE: {message}"
  let some table := textKey.database.findTable? "k" | fail "text replacement table missing"
  unless table.rows.map (fun row => row.rowid.value) == [2,3] do fail "TEXT REPLACE failed to allocate before deleting"
  for sql in [
      "CREATE TABLE x(id TEXT PRIMARY KEY ON CONFLICT IGNORE,a);CREATE UNIQUE INDEX u ON x(a);INSERT INTO x VALUES('a',1),('b',2);INSERT INTO x VALUES('a',2);",
      "CREATE TABLE x(id INTEGER PRIMARY KEY ON CONFLICT REPLACE,a);CREATE UNIQUE INDEX u ON x(a);INSERT INTO x VALUES(1,1);INSERT INTO x VALUES(1,1);",
      "CREATE TABLE x(id INTEGER PRIMARY KEY ON CONFLICT FAIL);",
      "CREATE TABLE x(id TEXT,PRIMARY KEY(id) ON CONFLICT ROLLBACK);"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"primary policy accepted an aborting or unsupported case: {sql}"
  for kind in ["INTEGER", "TEXT"] do
    for policy in ["IGNORE", "REPLACE"] do
      for nullPolicy in ["IGNORE", "REPLACE"] do
        let sql := s!"CREATE TABLE \"quoted.key\"(\"Key\" {kind} PRIMARY KEY ON CONFLICT {policy} NOT NULL ON CONFLICT {nullPolicy},n);INSERT INTO \"quoted.key\" VALUES(1,'x');"
        let (state, _) ← match CoreSQL.execute Core.State.empty sql with
          | .ok result => pure result
          | .error message => fail message
        let some image := CoreFile.encode state.database | fail "primary policy encode failed"
        let some decoded := CoreDecode.decode image.fileBytes | fail "primary policy decode failed"
        unless decoded.Equiv state.database do fail "primary/NULL policies changed during codec roundtrip"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE TABLE t(id INTEGER PRIMARY KEY);" with
    | .ok parsed => pure parsed
    | .error message => fail message
  match parsed.statements.toList with
  | [.createTable name columns constraints flag] =>
      let forged := columns.map fun column => { column with conflict := .ignore }
      if (CoreTokenGrammar.check parsed.tokens #[.createTable name forged constraints flag]).isOk then
        fail "token replay accepted an invented PRIMARY KEY conflict policy"
  | _ => fail "unexpected primary policy AST"

def expectSQLiteSchemaNullConflict : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,a TEXT NOT NULL ON CONFLICT IGNORE,b INT NOT NULL);INSERT INTO t VALUES(1,'one',1),(2,NULL,2),(3,'three',3);"
  let (state, _) ← match CoreSQL.execute Core.State.empty setup with
    | .ok result => pure result
    | .error message => fail s!"schema NULL policy setup: {message}"
  let some table := state.database.findTable? "t" | fail "NULL-policy table missing"
  unless table.rows.map (fun row => row.rowid.value) == [1,3] do fail "schema IGNORE inserted a NULL row"
  let (same, results) ← match CoreSQL.execute state
      "INSERT INTO t VALUES(4,NULL,NULL) RETURNING *;UPDATE t SET a=NULL,b=NULL RETURNING *;" with
    | .ok result => pure result
    | .error message => fail s!"early IGNORE must precede later ABORT: {message}"
  unless same.database.Equiv state.database && results.all (fun result => result.rows.isEmpty && result.changes == 0) do
    fail "schema IGNORE changed rows or emitted RETURNING output"
  for sql in ["INSERT OR ABORT INTO t VALUES(4,NULL,4);", "INSERT OR REPLACE INTO t VALUES(1,NULL,4);",
      "UPDATE OR ABORT t SET a=NULL;", "UPDATE OR REPLACE t SET a=NULL;",
      "UPDATE t SET rowid=NULL,a=NULL;", "INSERT INTO t(rowid,a,b) VALUES('bad',NULL,1);"] do
    if (CoreSQL.execute state sql).isOk then fail s!"NULL policy suppressed a required error: {sql}"
  let (updated, _) ← match CoreSQL.execute state
      "UPDATE t SET a=CASE WHEN id=1 THEN NULL ELSE 'changed' END,b=b+10;" with
    | .ok result => pure result
    | .error message => fail message
  let (_, selected) ← match CoreSQL.execute updated "SELECT id,a,b FROM t ORDER BY id;" with
    | .ok result => pure result
    | .error message => fail message
  let expected : List (List Value) := [[.integer 1,.text "one",.integer 1],[.integer 3,.text "changed",.integer 13]]
  let rows ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (selected.getLast?).map (·.rows) == some rows do fail "schema IGNORE update changed a skipped row"
  let (more, _) ← match CoreSQL.execute updated
      "CREATE TABLE r(id INTEGER PRIMARY KEY NOT NULL ON CONFLICT IGNORE,a NOT NULL ON CONFLICT REPLACE);INSERT INTO r VALUES(NULL,1);CREATE TABLE added(id INTEGER PRIMARY KEY);ALTER TABLE added ADD a NOT NULL ON CONFLICT IGNORE;INSERT INTO added VALUES(1,NULL),(2,'ok');" with
    | .ok result => pure result
    | .error message => fail s!"NULL policy metadata: {message}"
  let some image := CoreFile.encode more.database | fail "NULL policy encode failed"
  let some reopened := CoreDecode.decode image.fileBytes | fail "NULL policy reopen failed"
  unless reopened.Equiv more.database do fail "NULL policies changed during codec roundtrip"
  let (again, _) ← match CoreSQL.execute { more with database := reopened }
      "INSERT INTO t VALUES(99,NULL,1);" with
    | .ok result => pure result
    | .error message => fail message
  unless again.database.Equiv reopened do fail "reopened schema lost IGNORE behavior"
  for sql in ["CREATE TABLE x(a NOT NULL,b NOT NULL ON CONFLICT IGNORE);INSERT INTO x VALUES(NULL,NULL);",
      "CREATE TABLE x(a NOT NULL ON CONFLICT REPLACE);INSERT INTO x VALUES(NULL);",
      "CREATE TABLE x(a NOT NULL ON CONFLICT IGNORE NOT NULL);INSERT INTO x VALUES(NULL);",
      "CREATE TABLE x(a INTEGER PRIMARY KEY ON CONFLICT FAIL);",
      "CREATE TABLE x(a NOT NULL ON CONFLICT FAIL);"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"accepted unsupported or aborting constraint: {sql}"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE TABLE x(a NOT NULL);" with
    | .ok parsed => pure parsed
    | .error message => fail message
  match parsed.statements.toList with
  | [.createTable name columns constraints flag] =>
      let forged := columns.map fun column => { column with notNullConflict := .ignore }
      if (CoreTokenGrammar.check parsed.tokens #[.createTable name forged constraints flag]).isOk then
        fail "token replay accepted an invented NOT NULL conflict policy"
  | _ => fail "unexpected NULL-policy test AST"

def expectSQLiteCreateTableAs : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE source(Id INTEGER PRIMARY KEY,Label TEXT NOT NULL,Val REAL);CREATE INDEX LabelIndex ON source(Label);INSERT INTO source VALUES(3,'three',3.5),(17,'seventeen',17.5);CREATE TABLE Copy AS SELECT * FROM source ORDER BY Id DESC;" with
    | .ok result => pure result
    | .error message => fail s!"CTAS setup: {message}"
  let some copy := state.database.findTable? "Copy" | fail "CTAS table missing"
  unless copy.schema.catalogColumns.map (·.name) == ["Id","Label","Val"] &&
      copy.schema.catalogColumns.map (·.declaredType) == ["INT","TEXT","REAL"] do
    fail "CTAS names or affinity-derived declared types differ"
  unless copy.schema.catalogColumns.all (fun column => !column.notNull &&
      !column.integerPrimaryKey && !column.textPrimaryKey) && copy.indexes.isEmpty do
    fail "CTAS inherited source constraints or indexes"
  unless copy.rows.map (fun row => row.rowid.value) == [1,2] do fail "CTAS did not allocate consecutive fresh rowids"
  let (_, selected) ← match CoreSQL.execute state "SELECT rowid,Id FROM Copy ORDER BY rowid;" with
    | .ok result => pure result
    | .error message => fail message
  let expected : List (List Value) := [[.integer 1,.integer 17],[.integer 2,.integer 3]]
  let rows ← match expected.mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (selected.getLast?).map (·.rows) == some rows do fail "CTAS rowids lost SELECT order"
  let (more, _) ← match CoreSQL.execute state
      "CREATE TABLE Dup AS SELECT Id AS A,Val AS a,Label AS \"a:1\" FROM source ORDER BY Id;CREATE TABLE Exprs AS SELECT 'a''b',1 /*inside*/ + 2,true,likely(1);CREATE TABLE Vals AS VALUES(1,2),(3,4);" with
    | .ok result => pure result
    | .error message => fail s!"CTAS derived columns: {message}"
  let some duplicates := more.database.findTable? "Dup" | fail "CTAS duplicate-name table missing"
  unless duplicates.schema.catalogColumns.map (·.name) == ["A","a:1","a:2"] do
    fail "CTAS duplicate-name suffixes differ"
  let some expressions := more.database.findTable? "Exprs" | fail "CTAS expression table missing"
  unless expressions.schema.catalogColumns.map (·.name) ==
      ["'a''b'","1 /*inside*/ + 2","column3","likely(1)"] do
    fail "CTAS lost quoted text, comments or boolean column naming"
  let some values := more.database.findTable? "Vals" | fail "CTAS VALUES table missing"
  unless values.schema.catalogColumns.map (·.name) == ["column1","column2"] &&
      values.rows.length == 2 do fail "CTAS VALUES metadata or rows differ"
  let (unchanged, _) ← match CoreSQL.execute state
      "CREATE TABLE IF NOT EXISTS copy AS SELECT abs(-9223372036854775808) FROM missing;" with
    | .ok result => pure result
    | .error message => fail s!"CTAS IF NOT EXISTS evaluated source: {message}"
  unless unchanged.database.Equiv state.database do fail "CTAS IF NOT EXISTS changed the database"
  let (rolled, _) ← match CoreSQL.execute state
      "BEGIN;CREATE TABLE Rolled AS SELECT * FROM source;ROLLBACK;" with
    | .ok result => pure result
    | .error message => fail message
  unless rolled.database.Equiv state.database do fail "CTAS rollback changed the database"
  let (more, _) ← match CoreSQL.execute more "CREATE TABLE Unclosed AS SELECT 1/*notclosed" with
    | .ok result => pure result
    | .error message => fail s!"SQLite permits a nonempty block comment ending at EOF: {message}"
  let some commentTable := more.database.findTable? "Unclosed" | fail "CTAS EOF-comment table missing"
  unless commentTable.schema.catalogColumns.map (·.name) == ["1/*notclosed"] do
    fail "CTAS lost a block comment ending at EOF"
  if (CoreSQL.execute more "SELECT 1/*").isOk then fail "two-byte slash-star must not become a comment"
  let some image := CoreFile.encode more.database | fail "CTAS encode failed"
  let some reopened := CoreDecode.decode image.fileBytes | fail "CTAS reopen failed"
  unless reopened.Equiv more.database do fail "CTAS metadata/data changed on reopen"
  let parsed ← match CoreTokenGrammar.parseCertified "CREATE TABLE CheckSource AS SELECT 1 /*kept*/ + 2;" with
    | .ok parsed => pure parsed
    | .error message => fail message
  match parsed.statements.toList with
  | [.createTableAs name query ifNotExists] =>
      let forged := { query with columns := query.columns.map fun column => { column with sourceSql := some "forged" } }
      if (CoreTokenGrammar.check parsed.tokens #[.createTableAs name forged ifNotExists]).isOk then
        fail "CTAS accepted forged source text as a stored column name"
  | _ => fail "CTAS parser returned a different statement shape"

end SQLeanite.Tests
