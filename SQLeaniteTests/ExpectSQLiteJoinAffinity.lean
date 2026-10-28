import SQLeaniteTests.ExpectSQLiteJoinProjectionWrappers
import SQLeaniteTests.ExpectSQLiteMath

namespace SQLeanite.Tests
open SQLeanite

def expectSQLiteJoinAffinity : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k TEXT);INSERT INTO l VALUES(1,1),(2,2),(3,NULL),(4,'bad');INSERT INTO r VALUES(1,'01'),(2,'2'),(3,NULL),(4,'bad'),(5,'2x');"
  let cases : List (String × List (List Value)) := [
    ("SELECT a.id,b.id FROM l a JOIN r b ON a.k=b.k ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1],[.integer 2,.integer 2],[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a JOIN r b ON b.k=a.k ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1],[.integer 2,.integer 2],[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.k=b.k ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1],[.integer 2,.integer 2],[.integer 3,.null],[.integer 4,.integer 4]]),
    ("SELECT a.k,b.k FROM l a JOIN r b ON a.id=b.id WHERE a.k=b.k ORDER BY a.id,b.id;",
      [[.integer 1,.text "01"],[.integer 2,.text "2"],[.text "bad",.text "bad"]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"join affinity: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"join affinity rows: {sql}"

def expectSQLiteJoinSyntax : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,v);CREATE TABLE r(id INTEGER PRIMARY KEY,v);CREATE TABLE e(id INTEGER PRIMARY KEY,v);INSERT INTO l VALUES(1,'a'),(2,'b');INSERT INTO r VALUES(2,'x');"
  let cases : List (String × List (List Value)) := [
    ("JOIN r AS b", [[.integer 1,.integer 2],[.integer 2,.integer 2]]),
    ("INNER JOIN r AS b", [[.integer 1,.integer 2],[.integer 2,.integer 2]]),
    ("CROSS JOIN r AS b", [[.integer 1,.integer 2],[.integer 2,.integer 2]]),
    (", r AS b", [[.integer 1,.integer 2],[.integer 2,.integer 2]]),
    (", r AS b ON a.id=b.id", [[.integer 2,.integer 2]]),
    ("CROSS INNER CROSS JOIN r AS b ON a.id=b.id", [[.integer 2,.integer 2]]),
    ("LEFT OUTER LEFT JOIN r AS b ON a.id=b.id", [[.integer 1,.null],[.integer 2,.integer 2]]),
    ("OUTER LEFT JOIN e AS b", [[.integer 1,.null],[.integer 2,.null]]),
    ("LEFT LEFT LEFT JOIN r AS b", [[.integer 1,.integer 2],[.integer 2,.integer 2]]),
    ("INNER CROSS JOIN e AS b", [])]
  for (source, values) in cases do
    let sql := s!"SELECT a.id,b.id FROM l AS a {source} ORDER BY a.id,b.id;"
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"join syntax: {source}: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"join syntax rows: {source}"
  for source in ["OUTER", "LEFT INNER", "CROSS LEFT", "INNER OUTER", "LEFT LEFT LEFT LEFT"] do
    if (CoreSQL.execute Core.State.empty
        (setup ++ s!"SELECT a.id,b.id FROM l AS a {source} JOIN r AS b;")).isOk then
      fail s!"invalid join type accepted: {source}"
  let sql := "SELECT a.id,b.id FROM l AS a CROSS JOIN r AS b;"
  let parsed : CoreTokenGrammar.CertifiedParse sql ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result
    | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "JOIN AST missing"
  let some right := query.sources[1]? | fail "JOIN right source missing"
  for forged in [{ right with crossJoin := false }, { right with leftJoin := true },
      { right with joinOn := some (.literal (.integer 1)) }] do
    if (CoreTokenGrammar.check parsed.tokens
        #[.select { query with sources := query.sources.set! 1 forged }]).isOk then
      fail "JOIN token replay changed type or fabricated ON"

def expectSQLiteEmptyWritePublication : IO Unit := do
  let sqlite := (← IO.getEnv "SQLITE3_BIN").getD "/usr/bin/sqlite3"
  let input : System.FilePath := ".lake/build/sqleanite-empty-write.sql"
  for mode in ["--verified-file", "--verified-wal-file"] do
    let path : System.FilePath := s!".lake/build/sqleanite-empty-write{mode}.db"
    let wal : System.FilePath := path.toString ++ "-wal"
    for file in [wal, path] do
      if ← file.pathExists then IO.FS.removeFile file
    let created ← IO.Process.output { cmd := sqlite, args := #[path.toString,
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'old');CREATE TABLE a(id INTEGER PRIMARY KEY AUTOINCREMENT,v);" ] }
    unless created.exitCode == 0 do fail created.stderr
    let before ← IO.FS.readBinFile path
    IO.FS.writeFile input "INSERT INTO t SELECT 2,'new' LIMIT 0;UPDATE t SET v='new' WHERE id<0;DELETE FROM t WHERE id<0;"
    let result ← IO.Process.output { cmd := ".lake/build/bin/sqleanite", args := #[mode,path.toString,input.toString] }
    unless result.exitCode == 0 do fail result.stderr
    unless (← IO.FS.readBinFile path) == before && !(← wal.pathExists) do
      fail "zero-row DML changed main or WAL bytes"
    IO.FS.writeFile input "INSERT INTO a(v) SELECT 'new' LIMIT 0;"
    let result ← IO.Process.output { cmd := ".lake/build/bin/sqleanite", args := #[mode,path.toString,input.toString] }
    unless result.exitCode == 0 do fail result.stderr
    let observed ← IO.Process.output { cmd := sqlite, args := #[path.toString,
      "PRAGMA integrity_check;SELECT name,seq FROM sqlite_sequence;SELECT id,v FROM t;" ] }
    unless observed.exitCode == 0 && observed.stdout == "ok\na|0\n1|old\n" do
      fail "zero-row AUTOINCREMENT statement lost its sequence initialization"

def expectSQLiteLimitExpressions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY);INSERT INTO t VALUES(1),(2),(3),(4);"
  for (clause, values) in [
      ("LIMIT '1.0'", [1]),
      ("LIMIT 1.0 OFFSET length('x')", [2]),
      ("LIMIT abs(-2) OFFSET CAST('1' AS TEXT)", [2,3]),
      ("LIMIT 1+1,4/2", [3,4]),
      ("LIMIT '-9223372036854775808'", [1,2,3,4]),
      ("LIMIT 0xFFFFFFFFFFFFFFFF OFFSET -1.0", [1,2,3,4]),
      ("LIMIT CASE WHEN 1 THEN 2 ELSE 0 END", [1,2]),
      ("LIMIT iif(1,1,abs(-9223372036854775808))", [1]),
      ("LIMIT 0 OFFSET abs(-9223372036854775808)", []),
      ("LIMIT abs(-9223372036854775808),0", []),
      ("LIMIT 0 AND missing", []),
      ("LIMIT 0 AND abs(-9223372036854775808)", [])] do
    let (_, results) ← match CoreSQL.execute Core.State.empty
        (setup ++ "SELECT id FROM t ORDER BY id " ++ clause ++ ";") with
      | .ok outcome => pure outcome
      | .error message => fail s!"LIMIT expression: {clause}: {message}"
    let expected ← match values.mapM (fun value => (fun x => [x]) <$> SQLSurface.value (.integer value)) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some expected do fail s!"LIMIT expression rows: {clause}"
  for clause in ["LIMIT 1.5", "LIMIT '1x'", "LIMIT X'31'", "LIMIT NULL",
      "LIMIT -9223372036854775808.0", "LIMIT 1e999", "LIMIT abs(-9223372036854775808)",
      "LIMIT 0 OFFSET not_a_function()", "LIMIT 0 OFFSET missing", "LIMIT 0 AND not_a_function()"] do
    if (CoreSQL.execute Core.State.empty (setup ++ "SELECT id FROM t " ++ clause ++ ";")).isOk then
      fail s!"invalid LIMIT expression accepted: {clause}"
  for expression in ["1.5", "NULL", "missing", "not_a_function()", "abs(-9223372036854775808)"] do
    let query := s!" AS SELECT 1 LIMIT {expression};"
    unless (CoreSQL.execute Core.State.empty
        (setup ++ "CREATE TABLE IF NOT EXISTS t" ++ query)).isOk do
      fail "CTAS schema no-op evaluated unused LIMIT"
    if (CoreSQL.execute Core.State.empty ("CREATE TABLE fresh" ++ query)).isOk then
      fail "CTAS omitted required LIMIT error for a new table"
  unless !(CoreSQL.execute Core.State.empty
      (setup ++ "CREATE TABLE IF NOT EXISTS t AS SELECT 1 LIMIT (;" )).isOk do
    fail "CTAS schema no-op hid invalid syntax"
  let parsed ← match CoreTokenGrammar.parseCertified "SELECT 1 LIMIT abs(-2) OFFSET 1;" with
    | .ok result => pure result
    | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "LIMIT replay fixture is not SELECT"
  let some clause := query.limitClause | fail "LIMIT original expressions missing"
  for forged in [{ query with limit := some 3 }, { query with offset := 0 },
      { query with limitClause := none },
      { query with limitClause := some { clause with count := .literal (.integer 2) } },
      { query with limitClause := some { clause with comma := true } },
      { query with limitClause := some { clause with offset := none } }] do
    if (CoreTokenGrammar.check parsed.tokens #[.select forged]).isOk then
      fail "LIMIT replay trusted changed expression, spelling or normalized window"

def expectSQLiteLimitOffset : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,b); INSERT INTO t VALUES(1,1,1),(2,2,2),(3,1,3),(4,3,4);"
  for (query, values) in [
      ("SELECT id FROM t LIMIT 1 OFFSET 1;", [2]),
      ("SELECT id FROM t LIMIT 1,2;", [2,3]),
      ("SELECT id FROM t LIMIT -1 OFFSET 2;", [3,4]),
      ("SELECT id FROM t LIMIT 0 OFFSET 1;", []),
      ("SELECT id FROM t LIMIT 0 OFFSET NULL;", []),
      ("SELECT id FROM t LIMIT NULL,0;", []),
      ("SELECT id FROM t LIMIT 0 OFFSET 9223372036854775808;", []),
      ("SELECT id FROM t LIMIT 1 OFFSET -3;", [1]),
      ("SELECT id FROM t LIMIT +1 OFFSET +1;", [2]),
      ("SELECT DISTINCT v FROM t ORDER BY id LIMIT 1 OFFSET 1;", [2]),
      ("SELECT DISTINCT v FROM t ORDER BY id DESC LIMIT 1 OFFSET 1;", [1]),
      ("SELECT DISTINCT v FROM t ORDER BY b DESC LIMIT 1 OFFSET 1;", [2]),
      ("SELECT abs(-9223372036854775808) FROM t LIMIT 1 OFFSET 10;", [])] do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"LIMIT/OFFSET: {message}"
    let expected ← match values.mapM (fun v => (fun x => [x]) <$> SQLSurface.value (.integer v)) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some expected do fail s!"LIMIT/OFFSET rows: {query}"
  for query in ["SELECT DISTINCT abs(-9223372036854775808) FROM t LIMIT 1 OFFSET 10;",
      "SELECT id FROM t WHERE abs(-9223372036854775808) LIMIT 1 OFFSET 10;",
      "SELECT id FROM t LIMIT 9223372036854775808;", "SELECT missing FROM t LIMIT 0 OFFSET 5;"] do
    match CoreSQL.execute Core.State.empty (setup ++ query) with
    | .ok _ => fail s!"LIMIT/OFFSET suppressed a required error: {query}"
    | .error _ => pure ()

def expectSQLiteInList : IO Unit := do
  let cases : List (String × List Value) := [
    ("SELECT NULL IN (), NULL NOT IN (), missing IN ();", [.integer 0, .integer 1, .integer 0]),
    ("SELECT 1 IN (1,2), 1 NOT IN (1,2), 2 IN (1,NULL), NULL IN (1,2);",
      [.integer 1, .integer 0, .null, .null]),
    ("SELECT '1' IN (1), CAST('1' AS NUMERIC) IN (1), 1 IN (CAST('1' AS TEXT));",
      [.integer 0, .integer 1, .integer 0]),
    ("SELECT 1 IN (1,abs(-9223372036854775808)), abs(-9223372036854775808) IN ();",
      [.integer 1, .integer 0])]
  for (query, values) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty query with
      | .ok outcome => pure outcome
      | .error message => fail s!"IN list: {message}"
    let expected ← match values.mapM SQLSurface.value with
      | .ok row => pure row
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [expected] do fail s!"IN list truth: {query}"
  let indexed := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,1),(2,2); CREATE TABLE empty(id INTEGER PRIMARY KEY,v);"
  let (_, results) ← match CoreSQL.execute Core.State.empty (indexed ++
      "SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) AND id=1 LIMIT 1;") with
    | .ok outcome => pure outcome
    | .error message => fail s!"primary equality before IN membership: {message}"
  unless (results.getLast?).map (·.rows.length) == some 1 do
    fail "primary equality did not bound the IN membership scan"
  for query in [
      "SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) LIMIT 1;",
      "SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) AND id>0 LIMIT 1;",
      "SELECT id FROM empty WHERE id=1 AND id IN (1,abs(-9223372036854775808),id);"] do
    match CoreSQL.execute Core.State.empty (indexed ++ query) with
    | .ok _ => fail "IN search did not materialize an invalid RHS"
    | .error _ => pure ()
  for query in ["SELECT 1 IN (1,2,abs(-9223372036854775808));",
      "SELECT NULL IN (abs(-9223372036854775808),1);",
      "SELECT unknown_function() IN ();", "SELECT 1 IN (1,missing);"] do
    match CoreSQL.execute Core.State.empty query with
    | .ok _ => fail s!"invalid IN expression accepted: {query}"
    | .error _ => pure ()

def expectSQLiteWALRecoveryPrefix : IO Unit := do
  let header := CoreWALFileAdapter.header
  let page := Storage.Page.zero PhysicalCodec.pageSize
  let first : PhysicalWAL.Frame := {
    pageNumber := ⟨⟨2, by decide⟩, by decide⟩
    databaseSize := ⟨0, by decide⟩
    page }
  let commit : PhysicalWAL.Frame := {
    pageNumber := ⟨⟨1, by decide⟩, by decide⟩
    databaseSize := ⟨2, by decide⟩
    page }
  let wal : PhysicalWAL.WAL := { header, frames := [first, commit, first] }
  for bytes in [wal.encode, wal.encode ++ [1,2,3],
      wal.encode.take (32 + 2 * PhysicalWAL.frameSize + 17)] do
    match SQLite.WALRead.recover bytes with
    | .ok (some snapshot) =>
      unless snapshot.pageCount == 2 && snapshot.pageSize == 4096 && snapshot.frames.length == 2 do
        fail "WAL recovery exposed an uncommitted or incomplete tail"
    | _ => fail "WAL recovery rejected a valid committed prefix"
  let uncommitted : PhysicalWAL.WAL := { header, frames := [first, first] }
  for bytes in [[], header.encode, uncommitted.encode] do
    match SQLite.WALRead.recover bytes with
    | .ok none => pure ()
    | _ => fail "WAL recovery invented a commit"
  let snapshot : SQLite.WALRead.Snapshot := {
    pageSize := 512, pageCount := 2
    frames := [⟨2, 2, [2]⟩, ⟨2, 0, [1]⟩] }
  let base := fun n => some [UInt8.ofNat n]
  unless snapshot.readPage base 1 == some [1] && snapshot.readPage base 2 == some [2] &&
      (snapshot.readPage base 3).isNone do
    fail "WAL main-page overlay or committed size is incorrect"

def expectSQLiteRowDeletes : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT); INSERT INTO t VALUES(1,'a'),(2,'bb'),(3,'ccc'),(4,NULL); CREATE INDEX tv ON t(v);"
  for (query, removed) in [
      ("DELETE FROM t WHERE length(v)>1;", 2),
      ("DELETE FROM t AS x WHERE x.id%2=0;", 2),
      ("DELETE FROM t WHERE 0 AND abs(-9223372036854775808);", 0),
      ("DELETE FROM t WHERE id+0>0;", 4),
      ("DELETE FROM t WHERE missing+1 AND 0;", 0)] do
    let (state, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"row DELETE: {message}"
    unless (results.getLast?).map (·.changes) == some removed &&
        (state.database.findTable? "t").map (·.rows.length) == some (4 - removed) do
      fail s!"row DELETE count: {query}"
  for query in ["DELETE FROM t WHERE id=1 OR abs(-9223372036854775808);",
      "DELETE FROM t WHERE abs(-9223372036854775808) AND 0;",
      "DELETE FROM t WHERE wrong.id+1;", "DELETE FROM t WHERE missing+1;",
      "DELETE FROM t WHERE unknown_function(id) AND 0;"] do
    match CoreSQL.execute Core.State.empty (setup ++ query) with
    | .ok _ => fail s!"invalid DELETE accepted: {query}"
    | .error _ => pure ()

def expectSQLiteDistinctLimit : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,1),(2,2),(3,1),(4,3);"
  for query in ["SELECT DISTINCT v FROM t ORDER BY id LIMIT 2;",
      "SELECT DISTINCT v FROM t LIMIT 2;", "SELECT DISTINCT v FROM t ORDER BY v LIMIT 2;"] do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"DISTINCT LIMIT: {message}"
    let expected ← match [[Value.integer 1], [Value.integer 2]].mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some expected do
      fail s!"DISTINCT must retain first values before LIMIT: {query}"

def expectSQLiteDistinctOrder : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,b); INSERT INTO t VALUES(1,1,1),(2,1,3),(3,2,2),(4,1,0);"
  for (query, values) in [
      ("SELECT DISTINCT v FROM t ORDER BY b DESC;", [2,1]),
      ("SELECT DISTINCT +v FROM t ORDER BY b DESC;", [2,1]),
      ("SELECT DISTINCT v FROM t ORDER BY id DESC;", [1,2]),
      ("SELECT DISTINCT +v FROM t ORDER BY id DESC;", [1,2]),
      ("SELECT DISTINCT v FROM t ORDER BY b DESC LIMIT 1;", [2]),
      ("SELECT DISTINCT +v FROM t ORDER BY id DESC LIMIT 1;", [1])] do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"DISTINCT source ordering: {message}"
    let expected ← match values.mapM (fun v => (fun x => [x]) <$> SQLSurface.value (.integer v)) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some expected do
      fail s!"DISTINCT source representative ordering: {query}"

def expectSQLiteNumericDistinct : IO Unit := do
  let cases : List (String × String × List Value) := [
    ("1", "1.0", [.integer 1]),
    ("1.0", "1", [.real 1.0]),
    ("0", "-0.0", [.integer 0]),
    ("0.0", "-0.0", [.real 0.0]),
    ("NULL", "NULL", [.null]),
    ("1", "'1'", [.integer 1, .text "1"]),
    ("'1'", "X'31'", [.text "1", .blob #[49]]),
    ("9007199254740992", "9007199254740992.0", [.integer 9007199254740992]),
    ("9007199254740993", "9007199254740992.0", [.integer 9007199254740993, .real 9007199254740992.0]),
    ("-9223372036854775808", "-9223372036854775808.0", [.integer (-9223372036854775808)]),
    ("9223372036854775807", "9223372036854775808.0", [.integer 9223372036854775807, .real 9223372036854775808.0]),
    ("1.5", "1.5", [.real 1.5])]
  for (left, right, values) in cases do
    let setup := s!"CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,{left}),(2,{right});"
    for projection in ["v", "+v"] do
      let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ s!"SELECT DISTINCT {projection} FROM t;") with
        | .ok outcome => pure outcome
        | .error message => fail s!"numeric DISTINCT: {message}"
      let expected ← match values.mapM (fun v => (fun x => [x]) <$> SQLSurface.value v) with
        | .ok rows => pure rows
        | .error message => fail message
      unless (results.getLast?).map (·.rows) == some expected do
        fail s!"numeric DISTINCT changed a representative or merged unequal values: {left}, {right} ({projection})"

def expectSQLiteNumericCompounds : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("SELECT 1 UNION SELECT 1.0;", [[.real 1.0]]),
    ("SELECT 1.0 UNION SELECT 1;", [[.integer 1]]),
    ("SELECT 1 INTERSECT SELECT 1.0;", [[.integer 1]]),
    ("SELECT 1.0 INTERSECT SELECT 1;", [[.real 1.0]]),
    ("SELECT 1 EXCEPT SELECT 1.0;", []),
    ("SELECT 3 UNION SELECT 1 UNION SELECT 2;", [[.integer 1], [.integer 2], [.integer 3]]),
    ("SELECT NULL INTERSECT SELECT NULL;", [[.null]]),
    ("SELECT 1 UNION ALL SELECT 1.0;", [[.integer 1], [.real 1.0]]),
    ("SELECT 1,'x' UNION SELECT 1.0,'x';", [[.real 1.0, .text "x"]]),
    ("SELECT '1' UNION SELECT 1 UNION SELECT X'31';", [[.integer 1], [.text "1"], [.blob #[49]]]),
    ("SELECT 9007199254740993 EXCEPT SELECT 9007199254740992.0;", [[.integer 9007199254740993]])]
  for (query, values) in cases do
    let (state, results) ← match CoreSQL.execute Core.State.empty query with
      | .ok outcome => pure outcome
      | .error message => fail s!"numeric compound: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless results.map (·.rows) == [expected] && state.database.tables.isEmpty do
      fail s!"numeric compound changed multiplicity, ordering, representative, or state: {query}"

def expectSQLiteNumericGroups : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,x); INSERT INTO t VALUES(1,1,5),(2,1.0,7),(3,1,6),(4,'1',2),(5,NULL,NULL),(6,NULL,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT v,count(*) FROM t GROUP BY v;", [[.null,.integer 2],[.integer 1,.integer 3],[.text "1",.integer 1]]),
    ("SELECT v,max(x) FROM t GROUP BY v;", [[.null,.null],[.real 1.0,.integer 7],[.text "1",.integer 2]]),
    ("SELECT v,sum(x) FROM t GROUP BY v;", [[.null,.null],[.integer 1,.integer 18],[.text "1",.integer 2]]),
    ("SELECT v,min(x),max(x),min(x) FROM t GROUP BY v;", [[.null,.null,.null,.null],[.real 1.0,.integer 5,.integer 7,.integer 5],[.text "1",.integer 2,.integer 2,.integer 2]]),
    ("SELECT v,count(x) FROM t GROUP BY v;", [[.null,.integer 0],[.integer 1,.integer 3],[.text "1",.integer 1]]),
    ("SELECT min(v) FROM t WHERE id<4;", [[.integer 1]]),
    ("SELECT max(v) FROM t WHERE id<4;", [[.integer 1]])]
  for (query, values) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ query) with
      | .ok outcome => pure outcome
      | .error message => fail s!"numeric grouping: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some expected do
      fail s!"GROUP BY changed equality, counts, ordering, or representative storage class: {query}"
  let nullSetup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,x);INSERT INTO t VALUES(1,1,NULL),(2,1.0,NULL);"
  let (_, results) ← match CoreSQL.execute Core.State.empty (nullSetup ++ "SELECT v,max(x) FROM t GROUP BY v;") with
    | .ok outcome => pure outcome
    | .error message => fail message
  let real ← match SQLSurface.value (.real 1.0) with
    | .ok value => pure value
    | .error message => fail message
  unless (results.getLast?).map (·.rows) == some [[real,.null]] do
    fail "all-NULL extremum must select the last source row"

def expectSQLiteScalarAdmission : IO Unit := do
  for expression in ["coalesce(1,missing)", "coalesce(1,unknown_function())",
      "abs(-9223372036854775808)"] do
    match CoreSQL.execute Core.State.empty
        s!"CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,{expression});" with
    | .error _ => pure ()
    | .ok _ => fail s!"Core scalar should reject {expression}"
  let sql := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,CAST('12' AS INTEGER));"
  let certificate ← match CoreTokenGrammar.parseCertified sql with
    | .ok certificate => pure certificate
    | .error message => fail message
  let wrongTokens ← match lex
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,CAST('12' AS REAL));" with
    | .ok tokens => pure tokens
    | .error message => fail message
  match CoreTokenGrammar.check wrongTokens certificate.statements with
  | .error _ => pure ()
  | .ok _ => fail "Core grammar accepted a changed CAST type"

def expectSQLiteConstantSelect : IO Unit := do
  let queries := [
    ("SELECT 6*7;", [[42]]),
    ("SELECT CASE WHEN 0 THEN abs(-9223372036854775808) ELSE 7 END;", [[7]]),
    ("SELECT abs(-9223372036854775808) WHERE 0;", []),
    ("SELECT abs(-9223372036854775808) LIMIT 0;", []),
    ("SELECT abs(-9223372036854775808) LIMIT 1 OFFSET 1;", []),
    ("SELECT 1 WHERE '0.5x';", [[1]]),
    ("SELECT 1 UNION ALL SELECT 2;", [[1], [2]])]
  for (sql, expected) in queries do
    let (state, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"constant SELECT {sql}: {message}"
    unless state.database.tables.isEmpty do fail "constant SELECT mutated the database"
    let values ← expected.mapM fun row => row.mapM fun integer =>
      match SQLSurface.value (.integer integer) with
      | .ok value => pure value
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some values do
      fail s!"constant SELECT wrong result: {sql}"

def expectSQLiteColumnAffinity : IO Unit := do
  let (state, results) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,t TEXT,n NUMERIC,r REAL,b BLOB);\n      INSERT INTO t VALUES('1.0',12,'3e0','5.0','001');\n      CREATE INDEX t_n ON t(n);\n      SELECT t,n,r,b FROM t WHERE n='003' AND t=12;" with
    | .ok outcome => pure outcome
    | .error message => fail s!"column affinity: {message}"
  let expected ← ([Value.text "12", .integer 3, .real 5.0, .text "001"]).mapM fun v =>
    match SQLSurface.value v with
    | .ok v => pure v
    | .error message => fail message
  unless (results.getLast?).map (·.rows) == some [expected] do
    fail "column affinity changed value or storage class"
  let table ← match state.database.findTable? "t" with
    | some table => pure table
    | none => fail "column affinity lost table"
  unless CanonicalSchemaSQL.parse (CanonicalSchemaSQL.print table.schema) == some table.schema do
    fail "declared types did not survive canonical schema printing"
  let noncanonical ← match SQLSurface.value (.text "3") with
    | .ok value => pure value
    | .error message => fail message
  if Core.Row.create table.schema
      ([.integer ⟨2, by decide, by decide⟩] ++ expected.set 1 noncanonical) |>.isOk then
    fail "Core row admitted numeric TEXT without applying column affinity"

def expectSQLiteTypedSchemaNames : IO Unit := do
  for typeName in ["DOUBLE PRECISION", "FLOATING POINT", "a\"b TEXT,)", "", "NUMERIC(12,2)"] do
    let schema : Core.Schema := {
      name := "quoted\"table"
      columns := [{ name := "id", notNull := true, integerPrimaryKey := true },
        { name := "v", notNull := true, declaredType := typeName }]
      primaryKey := 0 }
    unless CanonicalSchemaSQL.parse (CanonicalSchemaSQL.print schema) == some schema do
      fail s!"canonical schema lost declared type {typeName}"

def expectSQLiteCertifiedAdmission : IO Unit := do
  for sql in ["CREATE TABLE t(id INTEGER PRIMARY KEY) WITHOUT ROWID;",
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT COLLATE NOCASE);"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then
      fail s!"Core silently discarded unsupported schema syntax: {sql}"
  for expression in ["2 BETWEEN 1 AND 3", "2 NOT BETWEEN 1 AND 3"] do
    match CoreTokenGrammar.parseStatements s!"SELECT {expression};" with
    | .ok _ => pure ()
    | .error message => fail s!"certified BETWEEN: {message}"
  let tokens ← match lex "SELECT 2 BETWEEN 1 AND 3;" with
    | .ok tokens => pure tokens
    | .error message => fail message
  let wrong ← match parse "SELECT (2>=1) AND (99<=3);" with
    | .ok statements => pure statements
    | .error message => fail message
  if (CoreTokenGrammar.check tokens wrong).isOk then
    fail "BETWEEN certificate accepted unequal copies of its left operand"

end SQLeanite.Tests
