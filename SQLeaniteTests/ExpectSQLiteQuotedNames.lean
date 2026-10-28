import SQLeanite.CoreWALFileEngine
import SQLeaniteTests.ExpectPageSizeConversionFailures

namespace SQLeanite.Tests
open SQLeanite

def expectSQLiteQuotedNames : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,\"select\" TEXT,v); INSERT INTO t VALUES(1,'a',3),(2,'b',4); CREATE TABLE empty(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT \"select\",[v],`id` FROM t ORDER BY \"id\";",
      [[.text "a", .integer 3, .integer 1], [.text "b", .integer 4, .integer 2]]),
    ("SELECT sum(\"v\"),count([id]) FROM t;", [[.integer 7, .integer 2]]),
    ("SELECT [v],sum(\"v\") FROM t GROUP BY `v`;", [[.integer 3, .integer 3], [.integer 4, .integer 4]]),
    ("SELECT x.[v] FROM t AS x WHERE x.id=1;", [[.integer 3]]),
    ("SELECT 0 AND \"missing\";", [[.integer 0]]),
    ("SELECT 0 AND missing.v FROM empty;", []),
    ("UPDATE t AS x SET v=x.[v]+1 WHERE x.id=1; SELECT v FROM t WHERE id=1;", [[.integer 4]]),
    ("DELETE FROM t WHERE [v]=3; SELECT id FROM t;", [[.integer 2]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"quoted names: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"quoted names mismatch: {sql}"
  for sql in ["SELECT t.id FROM t AS x LIMIT 0;", "SELECT missing.id FROM t WHERE id=1;",
      "SELECT id FROM t WHERE missing.v=3;", "SELECT id FROM t ORDER BY missing.v;",
      "SELECT \"missing\" FROM empty LIMIT 0;", "SELECT missing.* FROM empty;",
      "SELECT count(missing.v) FROM empty;", "UPDATE empty SET v=1 WHERE missing.id=2;",
      "UPDATE t AS x SET v=t.v;", "DELETE FROM empty WHERE missing.v=1;",
      "SELECT lean_dqs('v') FROM t LIMIT 0;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"name binding omitted error: {sql}"
    | .error _ => pure ()

def expectSQLiteWhereAliases : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,x INTEGER);INSERT INTO t VALUES(1,1,0),(2,3,1),(3,NULL,0);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,v);CREATE INDEX t_v ON t(v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT v+1 AS k FROM t WHERE k>2;", [[.integer 4]]),
    ("SELECT v AS x FROM t WHERE x=0 ORDER BY id;", [[.integer 1], [.null]]),
    ("SELECT v AS k FROM t WHERE k IS NULL;", [[.null]]),
    ("SELECT v AS k FROM t AS s WHERE k=1 ORDER BY s.id;", [[.integer 1]]),
    ("SELECT v AS true FROM t WHERE true;", [[.integer 1], [.integer 3]]),
    ("SELECT v AS false FROM t WHERE false;", [[.integer 1], [.integer 3]]),
    ("SELECT v AS k FROM t WHERE 0 AND k>0;", []),
    ("SELECT count(*) AS k FROM t WHERE 0 AND k>0;", [[.integer 0]]),
    ("SELECT count(*) AS k WHERE 0 AND k>0;", [[.integer 0]]),
    ("SELECT 1 AS k WHERE k=1;", [[.integer 1]]),
    ("SELECT 0 AS true WHERE true;", []),
    ("SELECT TRUE AS true WHERE true;", [[.integer 1]]),
    ("SELECT 0 AS true WHERE true IS TRUE;", [[.integer 0]]),
    ("SELECT id AS k,id+1 AS k FROM t WHERE k=1;", [[.integer 1, .integer 2]]),
    ("SELECT sum(v) FROM t WHERE x=0 HAVING sum(v)=1;", [[.integer 1]]),
    ("SELECT v AS k,count(*) FROM t WHERE k>1 GROUP BY k;", [[.integer 3, .integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"WHERE alias: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"WHERE alias mismatch: {sql}"
  for sql in ["SELECT v AS k FROM t WHERE t.k=1;", "SELECT v AS k FROM e WHERE missing LIMIT 0;",
      "SELECT count(*) AS k FROM t WHERE k>0;", "SELECT count(*) AS k WHERE k>0;",
      "SELECT v AS k,k AS y FROM t WHERE y>0;", "SELECT 1 AS k WHERE 0 AND no_function(k);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"WHERE alias error omitted: {sql}"

def expectSQLiteAggregateInternalOrder : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,s);INSERT INTO t VALUES(1,'A','x'),(2,'a','y'),(3,1,'z'),(4,1.0,'q'),(5,NULL,NULL);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,v,s);" ++
    "CREATE TABLE o(id INTEGER PRIMARY KEY,v);INSERT INTO o VALUES(1,9223372036854775807),(2,1),(3,-1);"
  let cases : List (String × List (List Value)) := [
    ("SELECT group_concat(v ORDER BY id DESC),string_agg(v,s ORDER BY id DESC) FROM t;",
      [[.text "1.0,1,a,A", .text "1.0z1yaxA"]]),
    ("SELECT group_concat(DISTINCT v ORDER BY v),group_concat(DISTINCT v ORDER BY id DESC) FROM t;",
      [[.text "1.0,A,a", .text "1,a,A"]]),
    ("SELECT group_concat(DISTINCT v COLLATE NOCASE ORDER BY v COLLATE NOCASE) FROM t;", [[.text "1.0,a"]]),
    ("SELECT group_concat(v ORDER BY 1) FROM t;", [[.text "A,a,1,1.0"]]),
    ("SELECT count(ORDER BY missing),count(ALL ORDER BY no_function(1)) FROM t;", [[.integer 5, .integer 5]]),
    ("SELECT count(ORDER BY missing);", [[.integer 1]]),
    ("SELECT char(ORDER BY missing);", [[.text ""]]),
    ("SELECT min(v ORDER BY abs(-9223372036854775808)) FROM t;", [[.integer 1]]),
    ("SELECT min(v ORDER BY id COLLATE missing),max(v ORDER BY v='a' COLLATE missing) FROM t;",
      [[.integer 1, .text "a"]]),
    ("SELECT min(v ORDER BY json(v)),max(v ORDER BY sqrt(v)) FROM t;", [[.integer 1, .text "a"]]),
    ("SELECT min(v ORDER BY v MATCH 'x') FROM t;", [[.integer 1]]),
    ("SELECT min(v ORDER BY 0x10000000000000000),min(v ORDER BY -0x8000000000000000) FROM t;",
      [[.integer 1, .integer 1]]),
    ("SELECT id,min(v ORDER BY id),max(v),min(v ORDER BY id ASC NULLS FIRST) FROM o;",
      [[.integer 1, .integer (-1), .integer 9223372036854775807, .integer (-1)]]),
    ("SELECT sum(v ORDER BY id DESC) FROM o;", [[.integer 9223372036854775807]]),
    ("SELECT sum(v ORDER BY id) FILTER(WHERE id>1) FROM o;", [[.integer 0]]),
    ("SELECT group_concat(v ORDER BY abs(-9223372036854775808)) FILTER(WHERE 0) FROM t;", [[.null]]),
    ("SELECT count(v ORDER BY abs(-9223372036854775808)) FROM e;", [[.integer 0]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate internal ORDER BY: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"aggregate internal ORDER BY mismatch: {sql}"
  for sql in ["SELECT sum(v ORDER BY id) FROM o;", "SELECT count(v ORDER BY abs(-9223372036854775808)) FROM t;",
      "SELECT min(v ORDER BY missing) FROM e LIMIT 0;", "SELECT min(v ORDER BY no_function(id)) FROM t LIMIT 0;",
      "SELECT min(v ORDER BY json(v,v)) FROM e;", "SELECT min(v ORDER BY min(v)) FROM t;",
      "SELECT min(v ORDER BY likelihood(v,0)) FROM e;", "SELECT abs(v ORDER BY id) FROM e;",
      "SELECT min(v ORDER BY likelihood(v,0x00000000000000000)) FROM e;",
      "SELECT count(* ORDER BY id) FROM t;", "SELECT count(DISTINCT ORDER BY id) FROM t;",
      "SELECT __sqlean_aggregate_order(group_concat(v),id) FROM t;",
      "SELECT group_concat(v ORDER BY __sqlean_order_desc(id)) FROM t;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"aggregate internal ORDER BY error omitted: {sql}"

def expectSQLiteAggregateFilter : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,g,v);INSERT INTO t VALUES(1,0,3),(2,0,1),(3,1,9),(4,1,1),(5,1,NULL);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,g,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT count(*) FILTER(WHERE id>2),count(v) FILTER(WHERE id>2),sum(v) FILTER(WHERE id>2) FROM t;",
      [[.integer 3, .integer 2, .integer 10]]),
    ("SELECT group_concat(v) FILTER(WHERE id>2),group_concat(DISTINCT v) FILTER(WHERE v<4) FROM t;",
      [[.text "9,1", .text "3,1"]]),
    ("SELECT sum(abs(-9223372036854775808)) FILTER(WHERE 0),total(v) FILTER(WHERE 0) FROM t;",
      [[.null, .real 0.0]]),
    ("SELECT group_concat(v,abs(-9223372036854775808)) FILTER(WHERE NULL) FROM t;", [[.null]]),
    ("SELECT id,min(v) FILTER(WHERE 0) FROM t;", [[.integer 1, .null]]),
    ("SELECT id,min(v) FILTER(WHERE id>2) FROM t;", [[.integer 4, .integer 1]]),
    ("SELECT id,min(v),max(v) FILTER(WHERE 0) FROM t;", [[.integer 2, .integer 1, .null]]),
    ("SELECT g,id,min(v),max(v) FILTER(WHERE 0) FROM t GROUP BY g ORDER BY g;",
      [[.integer 0, .integer 1, .integer 1, .null], [.integer 1, .integer 3, .integer 1, .null]]),
    ("SELECT id,min(v) FILTER(WHERE id<3),min(v) FILTER(WHERE id=3) FROM t;",
      [[.integer 3, .integer 1, .integer 9]]),
    ("SELECT count(*) FILTER(WHERE 0),sum(1) FILTER(WHERE 1);", [[.integer 0, .integer 1]]),
    ("SELECT count(*) FILTER(WHERE 1),min(v) FILTER(WHERE 1) FROM e;", [[.integer 0, .null]]),
    ("SELECT sum(v) FILTER(WHERE id>2) AS x FROM t HAVING x=10;", [[.integer 10]]),
    ("SELECT count(*) FROM t ORDER BY sum(abs(-9223372036854775808)) FILTER(WHERE 0);", [[.integer 5]]),
    ("SELECT count(*) FILTER(WHERE 0 AND missing) FROM t;", [[.integer 0]]),
    ("SELECT count(*) FILTER(WHERE 0 AND 0x10000000000000000) FROM t;", [[.integer 0]]),
    ("SELECT count(*) FILTER(WHERE 'a' COLLATE missing)=0 FROM t;", [[.integer 1]]),
    ("SELECT abs(-9223372036854775808)+count(*) FILTER(WHERE 0) FROM t LIMIT 1 OFFSET 1;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate FILTER: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"aggregate FILTER mismatch: {sql}"
  for sql in ["SELECT count(*) FILTER(WHERE likely(NULL AND abs(-9223372036854775808))) FROM t;",
      "SELECT count(*) FILTER(WHERE (NULL AND abs(-9223372036854775808)) COLLATE binary) FROM t;",
      "SELECT count(*) FROM t HAVING likely(NULL AND abs(-9223372036854775808));",
      "SELECT count(*) FROM t HAVING (NULL AND abs(-9223372036854775808)) COLLATE binary;",
      "SELECT count(*) FILTER(WHERE missing) FROM e LIMIT 0;",
      "SELECT count(*) FILTER(WHERE 0 AND no_function(1)) FROM e LIMIT 0;",
      "SELECT count(*) FILTER(WHERE sum(v)>0) FROM e;", "SELECT abs(v) FILTER(WHERE 1) FROM e;",
      "SELECT sum(v) FILTER(WHERE 1) FILTER(WHERE 1) FROM e;",
      "SELECT __sqlean_aggregate_filter(count(*),1) FROM t;",
      "SELECT '__sqlean_aggregate_filter'(count(*),1) FROM t;",
      "SELECT sum(abs(-9223372036854775808)) FILTER(WHERE 1) FROM t LIMIT 1 OFFSET 1;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"aggregate FILTER error omitted: {sql}"

def expectSQLiteProbability : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,'1'),(2,'2'),(3,NULL);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,v TEXT);"
  let cases : List (String × List (List Value)) := [
    ("SELECT likely(NULL),unlikely(1.25),likelihood('x',0.5);", [[.null, .real 1.25, .text "x"]]),
    ("SELECT id,likely(v)=1,unlikely(v) IN (1,2) FROM t ORDER BY id;",
      [[.integer 1, .integer 0, .integer 0], [.integer 2, .integer 0, .integer 0], [.integer 3, .null, .null]]),
    ("SELECT likely(CAST(1 AS TEXT))=1,unlikely(CAST(1 AS INTEGER))='1';", [[.integer 0, .integer 0]]),
    ("SELECT likely(CAST(1 AS TEXT))='1',unlikely(CAST(1 AS INTEGER))=1;", [[.integer 1, .integer 1]]),
    ("SELECT likelihood(7,0.0),likelihood(8,1.0),likelihood(9,(.5));", [[.integer 7, .integer 8, .integer 9]]),
    ("SELECT likely(count(*)) AS x FROM t HAVING x>0;", [[.integer 3]]),
    ("SELECT v,count(*) FROM t GROUP BY likely(1);", [[.text "1", .integer 3]]),
    ("SELECT likely(0 AND abs(-9223372036854775808));", [[.integer 0]]),
    ("SELECT unlikely(1 OR abs(-9223372036854775808));", [[.integer 1]]),
    ("SELECT 1 WHERE likely(NULL AND abs(-9223372036854775808));", []),
    ("SELECT 1 WHERE (NULL AND abs(-9223372036854775808)) COLLATE binary;", []),
    ("SELECT 1 WHERE likely(1 OR abs(-9223372036854775808));", [[.integer 1]]),
    ("SELECT likely(abs(-9223372036854775808)) FROM e;", []),
    ("SELECT likely(abs(-9223372036854775808)) LIMIT 0;", []),
    ("SELECT likely(abs(-9223372036854775808)) LIMIT 1 OFFSET 1;", []),
    ("SELECT likelihood(DISTINCT 7,0.5);", [[.integer 7]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"probability hint: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"probability hint mismatch: {sql}"
  for sql in ["SELECT likely(0) AND abs(-9223372036854775808);",
      "SELECT likely(1) OR abs(-9223372036854775808);",
      "SELECT 1 WHERE NOT likely(NULL AND abs(-9223372036854775808));",
      "SELECT likelihood(1,0) LIMIT 0;", "SELECT likelihood(v,+0.5) FROM e;",
      "SELECT likelihood(v,-0.0) FROM e;", "SELECT likelihood(v,0.5 COLLATE binary) FROM e;",
      "SELECT likelihood(v,0.5+0.0) FROM e;", "SELECT 0 AND likelihood(1,0);",
      "SELECT 1 OR likelihood(1,0);", "SELECT likely();", "SELECT unlikely(1,2);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"probability hint error omitted: {sql}"

def expectSQLiteTransactionNames : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'old');"
  let cases : List (String × List (List Value)) := [
    ("BEGIN DEFERRED TRANSACTION first;INSERT INTO t VALUES(2,'new');END TRANSACTION different;SELECT id,v FROM t ORDER BY id;",
      [[.integer 1,.text "old"],[.integer 2,.text "new"]]),
    ("BEGIN TRANSACTION 'first';UPDATE t SET v='pending';ROLLBACK TRANSACTION 'different';SELECT id,v FROM t;",
      [[.integer 1,.text "old"]]),
    ("BEGIN DEFERRED;SAVEPOINT s;UPDATE t SET v='pending';ROLLBACK TRANSACTION 'ignored' TO SAVEPOINT s;RELEASE s;COMMIT TRANSACTION extra;SELECT id,v FROM t;",
      [[.integer 1,.text "old"]])]
  for (sql, expected) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"transaction name: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some rows do fail "transaction name changed effects"
  for name in ["offset","window","left","indexed","''","\"to\"","\"select\""] do
    if !(CoreSQL.execute Core.State.empty s!"BEGIN DEFERRED TRANSACTION {name};COMMIT TRANSACTION 'other';").isOk then
      fail s!"legal transaction name rejected: {name}"
  let parsed ← match CoreTokenGrammar.parseCertified "BEGIN DEFERRED TRANSACTION named;COMMIT TRANSACTION other;" with
    | .ok result => pure result
    | .error message => fail message
  for sql in ["BEGIN IMMEDIATE TRANSACTION named;COMMIT TRANSACTION other;",
      "BEGIN EXCLUSIVE TRANSACTION named;COMMIT TRANSACTION other;",
      "BEGIN DEFERRED TRANSACTION select;COMMIT TRANSACTION other;"] do
    let tokens ← match lex sql with
      | .ok result => pure result
      | .error message => fail message
    if (CoreTokenGrammar.check tokens parsed.statements).isOk then fail "token replay changed transaction mode or name grammar"

def expectSQLiteScriptOutput : IO Unit := do
  let sqlite := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
  let sqlPath : System.FilePath := ".lake/build/sqleanite-script-output.sql"
  IO.FS.writeFile sqlPath "SELECT 'before';BEGIN;INSERT INTO t VALUES(2,'pending');SELECT id,v FROM t ORDER BY id;SELECT 1 +;"
  for (mode, label) in [("--verified-file", "file"), ("--verified-wal-file", "wal")] do
    let path := s!".lake/build/sqleanite-script-output-{label}.db"
    for suffix in ["-journal", "-wal", ""] do
      let target : System.FilePath := path ++ suffix
      if ← target.pathExists then IO.FS.removeFile target
    let created ← IO.Process.output { cmd := sqlite, args := #["-batch", "-bail", path,
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'old');"] }
    unless created.exitCode == 0 do fail s!"script output setup: {created.stderr}"
    let result ← IO.Process.output { cmd := ".lake/build/bin/sqleanite", args := #[mode, path, sqlPath.toString] }
    unless result.exitCode != 0 && result.stdout == "before\n1|old\n2|pending\n" do
      fail s!"completed statement output lost before error ({label}): {result.stdout}; {result.stderr}"
    let observed ← IO.Process.output { cmd := sqlite, args := #["-batch", "-bail", path,
      "PRAGMA integrity_check;SELECT id,v FROM t ORDER BY id;"] }
    unless observed.exitCode == 0 && observed.stdout == "ok\n1|old\n" do
      fail "streaming a transaction result published uncommitted rows"

def expectSQLiteCastTypeGrammar : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("SELECT CAST('007.5' AS UNSIGNED BIG INT),CAST('007.5' AS FLOATING POINT),CAST('007.5' AS DECIMAL(-10,+2));",
      [[.integer 7,.integer 7,.real 7.5]]),
    ("SELECT typeof(CAST('007.5' AS )),CAST('007.5' AS \"\"),CAST('junk' AS '');",
      [[.text "real",.real 7.5,.integer 0]]),
    ("SELECT CAST('007.5' AS TEXT /* INT */ extra),CAST('007.5' AS TEXT /* INT */),typeof(CAST('007.5' AS \"blob\" INT));",
      [[.integer 7,.text "007.5",.text "blob"]]),
    ("SELECT CAST('007.5' AS 'text' extra),CAST('007.5' AS [integer](5)),CAST('007.5' AS `text`(12));",
      [[.text "007.5",.integer 7,.text "007.5"]]),
    ("CREATE TABLE t(v DEFAULT (CAST('007.5' AS DOUBLE PRECISION)));INSERT INTO t DEFAULT VALUES;SELECT v,typeof(v) FROM t;",
      [[.real 7.5,.text "real"]]),
    ("CREATE TABLE t AS SELECT CAST('007.5' AS DECIMAL(10,2)) AS v;PRAGMA table_info(t);",
      [[.integer 0,.text "v",.text "NUM",.integer 0,.null,.integer 0]])]
  for (sql, expected) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"CAST type grammar: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some rows do fail s!"CAST type result: {sql}"
  for typ in ["TEXT(1+2)","TEXT(1,2,3)","TEXT(1_000)","TEXT()","TEXT(2) EXTRA","RIGHT","INDEXED","x'AB'"] do
    if (CoreSQL.execute Core.State.empty s!"SELECT CAST(1 AS {typ});").isOk then fail s!"invalid CAST type admitted: {typ}"
  for (admitted, forged) in [
      ("INSERT INTO t VALUES(CAST(1 AS TEXT(8)));", "INSERT INTO t VALUES(CAST(1 AS BLOB(8)));"),
      ("INSERT INTO t VALUES(CAST(1 AS TEXT /* INT */ extra));", "INSERT INTO t VALUES(CAST(1 AS TEXT /* BLOB */ extra));"),
      ("INSERT INTO t VALUES(CAST(1 AS TEXT(8)));", "INSERT INTO t VALUES(CAST(1 AS TEXT(1+2)));")] do
    let parsed ← match CoreTokenGrammar.parseCertified admitted with
      | .ok result => pure result
      | .error message => fail message
    let tokens ← match lex forged with
      | .ok result => pure result
      | .error message => fail message
    if (CoreTokenGrammar.check tokens parsed.statements).isOk then fail "token replay changed CAST type semantics"

def expectSQLiteIdentifierGrammar : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE \"select\"(\"from\" INTEGER PRIMARY KEY,v);INSERT INTO \"select\" VALUES(7,'kept');" with
    | .ok result => pure result
    | .error message => fail s!"quoted keyword declaration: {message}"
  let expected ← match SQLSurface.value (.integer 7) with
    | .ok value => pure value
    | .error message => fail message
  for sql in ["SELECT \"where\".\"from\" FROM \"select\" \"where\";",
      "SELECT left.\"from\" FROM \"select\" AS left;",
      "SELECT offset.\"from\" FROM \"select\" offset;",
      "SELECT 'where'.'from' FROM \"select\" 'where';"] do
    let (_, output) ← match CoreSQL.execute state sql with
      | .ok result => pure result
      | .error message => fail s!"SQLite identifier or alias rejected: {message}"
    unless (output.getLast?).map (·.rows) == some [[expected]] do fail "identifier alias resolved to wrong column"
  for sql in ["CREATE TABLE select(id INTEGER PRIMARY KEY);", "CREATE TABLE t(select INTEGER PRIMARY KEY);",
      "CREATE INDEX select ON \"select\"(v);", "SELECT 1 AS select;", "SELECT 1 join;", "SELECT 1 indexed;",
      "SELECT 1 regexp;", "SELECT length('a') regexp;",
      "SELECT current_date.\"from\" FROM \"select\" AS current_date;",
      "SELECT raise.\"from\" FROM \"select\" AS raise;"] do
    if (CoreSQL.execute state sql).isOk then fail s!"reserved keyword accepted as a name: {sql}"
  for sql in ["SELECT 1 DESC;", "SELECT 1 OFFSET;", "SELECT 1 AS left;",
      "SELECT length('a') filter;", "SELECT length('a') over;",
      "SELECT length('a') over /* comment */ FROM \"select\";",
      "SELECT sum(\"from\") FILTER (WHERE v='kept') FROM \"select\";"] do
    if !(CoreSQL.execute state sql).isOk then fail s!"fallback identifier rejected: {sql}"
  for (admitted, forged) in [
      ("CREATE TABLE \"select\"(id INTEGER PRIMARY KEY);", "CREATE TABLE select(id INTEGER PRIMARY KEY);"),
      ("SELECT 1 AS \"Alias\";", "SELECT 1 AS \"alias\";")] do
    let parsed ← match CoreTokenGrammar.parseCertified admitted with
      | .ok result => pure result
      | .error message => fail message
    let tokens ← match lex forged with
      | .ok result => pure result
      | .error message => fail message
    if (CoreTokenGrammar.check tokens parsed.statements).isOk then fail "token replay changed a declared identifier"

def expectSQLiteScriptPrefix : IO Unit := do
  for sql in ["SELECT 'a;b';SELECT 2;", "SELECT 'a'';b';-- ; comment\nSELECT 3;",
      "SELECT [a;b];/* ; comment */ SELECT `c;d`;", "SELECT 'unfinished;"] do
    unless String.join (SQLite.Script.split sql) == sql do fail "script splitting changed original source"
  unless (SQLite.Script.split "SELECT 'a'';b';SELECT 2;").length == 3 do fail "quoted semicolon split an SQL statement"
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-script-prefix.db"
    journal := ".lake/build/sqleanite-script-prefix.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  let connection ← CoreFileEngine.create .system paths
  if (← CoreFileEngine.execute connection
      "CREATE TABLE t(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO t(v) VALUES('kept');SELECT 1 +;").isOk then
    fail "script syntax error was ignored"
  if (← CoreFileEngine.execute connection "INSERT INTO t(v) VALUES('second');SELECT 'unfinished").isOk then
    fail "script lexical error was ignored"
  let sqlite := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
  let inspect := fun path => IO.Process.output {
    cmd := sqlite
    args := #[path, "-batch", "-bail", "PRAGMA integrity_check;SELECT id,v FROM t ORDER BY id;SELECT seq FROM sqlite_sequence WHERE name='t';"] }
  let c ← inspect paths.main.toString
  unless c.exitCode == 0 && c.stdout == "ok\n1|kept\n2|second\n2\n" do
    fail "completed script prefix was not persisted before a later error"
  if (← CoreFileEngine.execute connection "BEGIN;INSERT INTO t(v) VALUES('pending');SELECT 1 +;").isOk then
    fail "transaction script syntax error was ignored"
  let state ← CoreFileEngine.snapshot connection
  unless state.transactionSnapshot.isSome do fail "later syntax error discarded the live transaction"
  let c ← inspect paths.main.toString
  unless c.exitCode == 0 && c.stdout == "ok\n1|kept\n2|second\n2\n" do fail "syntax error published an open transaction"
  match ← CoreFileEngine.execute connection "ROLLBACK;" with
  | .ok _ => pure ()
  | .error message => fail s!"script prefix rollback: {message}"
  let wal : CoreWALFileAdapter.Paths := {
    main := ".lake/build/sqleanite-script-prefix-wal.db"
    wal := ".lake/build/sqleanite-script-prefix-wal.db-wal" }
  if ← wal.wal.pathExists then IO.FS.removeFile wal.wal
  if ← wal.main.pathExists then IO.FS.removeFile wal.main
  CoreWALFileAdapter.create .system wal Core.Database.empty
  if (← CoreWALFileEngine.execute .system wal
      "CREATE TABLE t(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO t(v) VALUES('kept');SELECT 'unfinished").isOk then
    fail "WAL script lexical error was ignored"
  let c ← inspect wal.main.toString
  unless c.exitCode == 0 && c.stdout == "ok\n1|kept\n1\n" do fail "WAL script lost its committed prefix"

def expectSQLiteReadTransaction : IO Unit := do
  let (state, _) ← match CoreSQL.execute Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'old');" with
    | .ok result => pure result
    | .error message => fail message
  let marked := CoreSavepoint.push state "s"
  if CoreFileEngine.requiresPersistence marked .commit || CoreFileEngine.requiresPersistence marked (.release "s") then
    fail "read-only transaction requested file publication"
  let (changed, _) ← match CoreSQL.execute marked "INSERT INTO t VALUES(2,'new');" with
    | .ok result => pure result
    | .error message => fail message
  unless CoreFileEngine.requiresPersistence changed .commit && CoreFileEngine.requiresPersistence changed (.release "s") do
    fail "changed transaction skipped file publication"
  let (restored, _) ← match CoreSQL.execute changed "ROLLBACK TO s;" with
    | .ok result => pure result
    | .error message => fail message
  if CoreFileEngine.requiresPersistence restored (.release "s") then fail "restored transaction requested unnecessary publication"
  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-read-transaction.db"
    journal := ".lake/build/sqleanite-read-transaction.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  let connection ← CoreFileEngine.create .system paths
  match ← CoreFileEngine.execute connection "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'old');" with
  | .error message => fail message
  | .ok _ => pure ()
  let before ← IO.FS.readBinFile paths.main
  for sql in ["BEGIN;SELECT * FROM t;COMMIT;", "SAVEPOINT s;SELECT * FROM t;RELEASE s;",
      "SAVEPOINT s;INSERT INTO t VALUES(2,'rolled back');ROLLBACK TO s;RELEASE s;"] do
    match ← CoreFileEngine.execute connection sql with
    | .error message => fail s!"read transaction: {message}"
    | .ok _ => pure ()
    unless (← IO.FS.readBinFile paths.main) == before do fail "read/restored transaction changed file bytes"

def expectSQLiteSavepoint : IO Unit := do
  let sql := "CREATE TABLE t(id INTEGER PRIMARY KEY AUTOINCREMENT,v);" ++
    "SAVEPOINT outer;INSERT INTO t(v) VALUES('kept');SAVEPOINT inner;" ++
    "INSERT INTO t(v) VALUES('discard');ROLLBACK TRANSACTION TO SAVEPOINT inner;" ++
    "INSERT INTO t(v) VALUES('second');RELEASE SAVEPOINT outer;SELECT id,v FROM t ORDER BY id;"
  let (state, output) ← match CoreSQL.execute Core.State.empty sql with
    | .ok result => pure result
    | .error message => fail s!"SAVEPOINT nested rollback and release: {message}"
  let expected ← match [[Value.integer 1, .text "kept"], [.integer 2, .text "second"]].mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some expected do fail "SAVEPOINT restored wrong rows or sequence history"
  unless state.transactionSnapshot.isNone && state.savepoints.isEmpty do fail "outer RELEASE left transaction active"
  let (next, _) ← match CoreSQL.execute state
      "BEGIN;SAVEPOINT s;INSERT INTO t(v) VALUES('pending');RELEASE s;ROLLBACK;" with
    | .ok result => pure result
    | .error message => fail s!"SAVEPOINT inside BEGIN: {message}"
  unless next.database.Equiv state.database do fail "inner RELEASE committed the enclosing BEGIN"
  let (next, _) ← match CoreSQL.execute state
      "SAVEPOINT s;CREATE TABLE gone(id INTEGER PRIMARY KEY);ROLLBACK TO s;RELEASE s;" with
    | .ok result => pure result
    | .error message => fail message
  unless next.database.Equiv state.database do fail "ROLLBACK TO failed to restore schema"
  for sql in ["SAVEPOINT s;COMMIT;RELEASE s;", "SAVEPOINT s;ROLLBACK;RELEASE s;",
      "ROLLBACK TO missing;", "RELEASE missing;", "SAVEPOINT s;BEGIN;",
      "SAVEPOINT select;", "SAVEPOINT transaction;", "SAVEPOINT join;"] do
    if (CoreSQL.execute state sql).isOk then fail s!"SAVEPOINT expected error missing: {sql}"
  let parsed ← match CoreTokenGrammar.parseCertified "SAVEPOINT real;" with
    | .ok result => pure result
    | .error message => fail message
  let tokens ← match lex "SAVEPOINT forged;" with
    | .ok result => pure result
    | .error message => fail message
  if (CoreTokenGrammar.check tokens parsed.statements).isOk then fail "token replay forged SAVEPOINT name"

  let paths : CoreFileAdapter.Paths := {
    main := ".lake/build/sqleanite-savepoint-live.db"
    journal := ".lake/build/sqleanite-savepoint-live.db-journal" }
  if ← paths.journal.pathExists then IO.FS.removeFile paths.journal
  if ← paths.main.pathExists then IO.FS.removeFile paths.main
  let connection ← CoreFileEngine.create .system paths
  let execute := fun sql => do
    match ← CoreFileEngine.execute connection sql with
    | .ok _ => pure ()
    | .error message => fail s!"SAVEPOINT live connection: {message}"
  execute "CREATE TABLE t(id INTEGER PRIMARY KEY AUTOINCREMENT,v);"
  let before ← IO.FS.readBinFile paths.main
  execute "SAVEPOINT outer;INSERT INTO t(v) VALUES('pending');SAVEPOINT inner;INSERT INTO t(v) VALUES('also pending');RELEASE inner;"
  unless (← IO.FS.readBinFile paths.main) == before do fail "inner RELEASE published uncommitted data"
  if (← CoreFileEngine.execute connection "ROLLBACK TO missing;").isOk then fail "missing SAVEPOINT was accepted"
  execute "ROLLBACK TO outer;INSERT INTO t(v) VALUES('committed');RELEASE outer;"
  let c ← IO.Process.output {
    cmd := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
    args := #[paths.main.toString, "-batch", "-bail", "SELECT id,v FROM t;SELECT seq FROM sqlite_sequence WHERE name='t';"] }
  unless c.exitCode == 0 && c.stdout == "1|committed\n1\n" do fail "outer RELEASE did not publish rows and sequence to C"
  let committed ← IO.FS.readBinFile paths.main
  execute "BEGIN;SAVEPOINT inner;INSERT INTO t(v) VALUES('pending');RELEASE inner;"
  unless (← IO.FS.readBinFile paths.main) == committed do fail "RELEASE within BEGIN published early"
  execute "ROLLBACK;"
  unless (← IO.FS.readBinFile paths.main) == committed do fail "ROLLBACK changed committed file bytes"

end SQLeanite.Tests
