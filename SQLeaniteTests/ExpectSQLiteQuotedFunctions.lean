import SQLeaniteTests.ExpectSQLiteSchemaRename

namespace SQLeanite.Tests
open SQLeanite

def expectSQLiteQuotedFunctions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,-3),(2,1.5),(3,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT \"abs\"(-3),[length]('abc'),`typeof`(1.0);", [[.integer 3, .integer 3, .text "real"]]),
    ("SELECT \"sum\"(v),[count](*),`count`(DISTINCT v) FROM t;", [[.real (-1.5), .integer 3, .integer 2]]),
    ("SELECT \"abs\"(DISTINCT -3),coalesce(DISTINCT NULL,2),min(DISTINCT 3,1,2),[max](ALL 1,3);",
      [[.integer 3, .integer 2, .integer 1, .integer 3]]),
    ("SELECT \"abs\"(v) FROM t ORDER BY `abs`(v);", [[.null], [.real 1.5], [.integer 3]]),
    ("UPDATE t SET v=[abs](v); SELECT v FROM t WHERE id=1;", [[.integer 3]]),
    ("SELECT 0 AND \"abs\"(-9223372036854775808);", [[.integer 0]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"quoted functions: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"quoted function mismatch: {sql}"
  for name in ["char", "\"char\"", "[char]", "`char`"] do
    for count in [999, 1000, 1001] do
      let arguments := String.intercalate "," (List.replicate count "65")
      let sql := s!"SELECT length({name}({arguments}));"
      match CoreSQL.execute Core.State.empty sql with
      | .ok (_, results) =>
          unless count ≤ SQLite.Limits.maxFunctionArgs &&
              results.map (·.rows) == [[[(← match SQLSurface.value (.integer count) with
                | .ok value => pure value
                | .error message => fail message)]]] do fail "function argument limit accepted wrong count"
      | .error message => unless count > SQLite.Limits.maxFunctionArgs do fail message
  for sql in ["SELECT 'abs'(-3);", "SELECT \"abs\"();", "SELECT [abs](1,2);",
      "SELECT CAST_INTEGER(1);", "SELECT \"cast_integer\"(1);", "SELECT CAST_INTEGER(DISTINCT 1);",
      "SELECT [cast_integer](DISTINCT 1);", "SELECT lean_distinct_aggregate_abs(1);",
      "SELECT LEAN_DISTINCT_AGGREGATE_ABS(DISTINCT 1);", "SELECT \"lean_dqs\"('v') FROM t;",
      "SELECT \"__sqlean_boolean_true\"();", "SELECT 0 AND \"unknown_function\"();"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"private/invalid function was admitted: {sql}"
    | .error _ => pure ()

def expectSQLiteBooleanKeywords : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,true TEXT,false INTEGER,v); INSERT INTO t VALUES(1,'2',7,2),(2,'0',0,0),(3,NULL,NULL,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT 2 IS TRUE,2 IS (TRUE),2 IS TRUE+0,0 IS FALSE,NULL IS NOT TRUE,NULL IS FALSE;",
      [[.integer 1, .integer 1, .integer 0, .integer 1, .integer 1, .integer 0]]),
    ("SELECT TRUE,FALSE,typeof(TRUE),typeof(FALSE);", [[.integer 1, .integer 0, .text "integer", .text "integer"]]),
    ("SELECT id,TRUE,FALSE,v IS TRUE FROM t ORDER BY id;",
      [[.integer 1, .text "2", .integer 7, .integer 0],
       [.integer 2, .text "0", .integer 0, .integer 0],
       [.integer 3, .null, .null, .integer 1]]),
    ("SELECT id FROM t WHERE id=TRUE ORDER BY id;", []),
    ("SELECT sum(TRUE),sum(FALSE) FROM t;", [[.integer 2, .integer 7]]),
    ("SELECT FALSE AND abs(-9223372036854775808),TRUE OR abs(-9223372036854775808);",
      [[.integer 0, .integer 1]]),
    ("SELECT 1 LIMIT TRUE;", [[.integer 1]]),
    ("SELECT 1 LIMIT FALSE;", []),
    ("UPDATE t SET v=TRUE WHERE id=1; SELECT v,typeof(v) FROM t WHERE id=1;", [[.text "2", .text "text"]]),
    ("DELETE FROM t WHERE false; SELECT id FROM t ORDER BY id;", [[.integer 2], [.integer 3]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"boolean keyword: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"boolean keyword mismatch: {sql}"
  for sql in ["SELECT FALSE AND missing;", "SELECT TRUE OR unknown_function();",
      "SELECT __sqlean_boolean_true() LIMIT 0;", "SELECT TRUE() LIMIT 0;",
      "SELECT TRUE.foo;", "SELECT missing IS TRUE FROM t WHERE FALSE LIMIT 0;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"boolean binding omitted error: {sql}"
    | .error _ => pure ()

def expectSQLiteOperatorPrecedence : IO Unit := do
  let cases : List (String × Value) := [
    ("0.5=-1<0.5", .integer 0), ("1!=(-1)<(-1)", .integer 1),
    ("0 LIKE 2<(-3)", .integer 1), ("3 IS '1'<'2'", .integer 0),
    ("2 NOT BETWEEN 1 AND 3=-3", .integer 0),
    ("'2' BETWEEN 2 AND 1 IS NOT -3", .integer 1),
    ("'a' NOT LIKE 'a' ESCAPE 'x'<=2", .integer 0),
    ("NULL ISNULL", .integer 1), ("NULL NOTNULL", .integer 0),
    ("1 NOT NULL", .integer 1), ("NULL NOT NULL+1", .integer 1),
    ("NULL IS DISTINCT FROM NULL", .integer 0),
    ("NULL IS NOT DISTINCT FROM NULL", .integer 1),
    ("2 IS DISTINCT FROM 1", .integer 1)]
  for (expression, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty ("SELECT " ++ expression ++ ";") with
      | .ok result => pure result
      | .error message => fail s!"operator precedence: {message}"
    let expected ← match SQLSurface.value expected with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [[expected]] do
      fail s!"operator precedence mismatch: {expression}"

def expectSQLiteAggregateResults : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,1),(2,1.0),(3,2),(4,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT sum(v)+count(*),typeof(sum(v)),42 FROM t;", [[.real 8.0, .text "real", .integer 42]]),
    ("SELECT coalesce(sum(v),count(*))+1 FROM t WHERE id<0;", [[.integer 1]]),
    ("SELECT round(avg(DISTINCT v),1),CASE WHEN count(*)>3 THEN sum(v) ELSE 0 END FROM t;",
      [[.real 1.5, .real 4.0]]),
    ("SELECT count(*),sum(7),min(2),max(3);", [[.integer 1, .integer 7, .integer 2, .integer 3]]),
    ("SELECT count(*),sum(7),avg(7),total(7) WHERE 0;", [[.integer 0, .null, .null, .real 0.0]]),
    ("SELECT count(*)+abs(-9223372036854775808) FROM t LIMIT 1 OFFSET 1;", []),
    ("SELECT sum(abs(-9223372036854775808)) WHERE 0;", [[.null]]),
    ("SELECT count(*)+abs(-9223372036854775808) LIMIT 1 OFFSET 1;", []),
    ("SELECT 0 AND sum(v) FROM t;", [[.integer 0]]),
    ("SELECT typeof(count(*)||total(v)/avg(v)) FROM t;", [[.text "real"]]),
    ("SELECT max(v) IS NULL+total(v),typeof(max(v) IS NULL+total(v)) FROM t;",
      [[.integer 0, .text "integer"]]),
    ("SELECT count(*) IS (NULL),count(*) IS NOT ((NULL)) FROM t;", [[.integer 0, .integer 1]]),
    ("SELECT 1||2*3,typeof(1||2*3),2*3||4,typeof(2*3||4);",
      [[.integer 36, .text "integer", .integer 68, .text "integer"]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate result expression: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do
      fail s!"aggregate scalar result mismatch: {sql}"
  let overflow := "CREATE TABLE ov(id INTEGER PRIMARY KEY,v); INSERT INTO ov VALUES(1,9223372036854775807),(2,1);"
  for sql in ["SELECT 0 AND count(abs(-9223372036854775808)) FROM t;",
      "SELECT count(*)+abs(-9223372036854775808) WHERE 0;",
      "SELECT count(*)+unknown_function() LIMIT 0;", "SELECT sum(rowid) LIMIT 0;",
      "SELECT sum(sum(v))+1 FROM t LIMIT 0;",
      "SELECT CASE WHEN 0 THEN sum(v) ELSE 1 END FROM ov;",
      "SELECT sum(v)+1 FROM ov LIMIT 1 OFFSET 1;"] do
    match CoreSQL.execute Core.State.empty (setup ++ overflow ++ sql) with
    | .ok _ => fail s!"aggregate result omitted error: {sql}"
    | .error _ => pure ()

def expectSQLiteNumericAggregates : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × Value) := [
    ("INSERT INTO t VALUES(1,1.5),(2,2.5); SELECT sum(v) FROM t;", .real 4.0),
    ("INSERT INTO t VALUES(1,'1'),(2,'2'); SELECT sum(v) FROM t;", .integer 3),
    ("INSERT INTO t VALUES(1,'12xyz'),(2,'3'); SELECT sum(v) FROM t;", .real 15.0),
    ("INSERT INTO t VALUES(1,CAST(X'31320033' AS TEXT)),(2,'1'); SELECT sum(v) FROM t;", .integer 13),
    ("INSERT INTO t VALUES(1,1),(2,2); SELECT avg(v) FROM t;", .real 1.5),
    ("INSERT INTO t VALUES(1,1),(2,2); SELECT total(v) FROM t;", .real 3.0),
    ("SELECT sum(v) FROM t;", .null),
    ("SELECT avg(v) FROM t;", .null),
    ("SELECT total(v) FROM t;", .real 0.0),
    ("INSERT INTO t VALUES(1,1e308),(2,1.0),(3,-1e308); SELECT sum(v) FROM t;", .real 1.0),
    ("INSERT INTO t VALUES(1,1e999),(2,-1e999); SELECT sum(v) FROM t;", .null),
    ("INSERT INTO t VALUES(1,9223372036854775807),(2,1),(3,0.0); SELECT sum(v) FROM t;", .real 9223372036854775808.0),
    ("INSERT INTO t VALUES(1,0.0),(2,9007199254740993),(3,-9007199254740992); SELECT sum(v) FROM t;", .real 1.0)]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"numeric aggregate: {message}"
    let value ← match SQLSurface.value expected with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some [[value]] do
      fail s!"numeric aggregate result: {sql}"
  match CoreSQL.execute Core.State.empty (setup ++
      "INSERT INTO t VALUES(1,9223372036854775807),(2,1); SELECT sum(v) FROM t;") with
  | .ok _ => fail "SUM omitted the integer overflow error"
  | .error _ => pure ()
  let (_, grouped) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE t(id INTEGER PRIMARY KEY,g,v); INSERT INTO t VALUES(1,1,1.5),(2,1,2.5),(3,2,NULL); SELECT g,sum(v),avg(v),total(v) FROM t GROUP BY g;" with
    | .ok result => pure result
    | .error message => fail s!"grouped numeric aggregate: {message}"
  let expected ← match ([[Value.integer 1, .real 4.0, .real 2.0, .real 4.0],
      [.integer 2, .null, .null, .real 0.0]]).mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows
    | .error message => fail message
  unless (grouped.getLast?).map (·.rows) == some expected do fail "grouped aggregate values"

def expectSQLiteJoinEmptyOuterOn : IO Unit := do
  for setup in [
      "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);",
      "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,'bad'),(2,'bad');",
      "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO r VALUES(1,'bad');"] do
    let (_, expected) ← match CoreSQL.execute Core.State.empty (setup ++
        "SELECT a.id,b.id FROM l a LEFT JOIN r b ON 1 ORDER BY a.id,b.id;") with
      | .ok result => pure result
      | .error message => fail message
    for predicate in ["abs(-9223372036854775808)", "abs(a.k)", "coalesce(a.k,b.k)",
        "json_extract(a.k,'$')", "a.k+b.k>0", "a.k LIKE '%a%'", "abs(-9223372036854775808) OR 1"] do
      let (_, actual) ← match CoreSQL.execute Core.State.empty (setup ++
          s!"SELECT a.id,b.id FROM l a LEFT JOIN r b ON {predicate} ORDER BY a.id,b.id;") with
        | .ok result => pure result
        | .error message => fail s!"empty outer ON {predicate}: {message}"
      unless (actual.getLast?).map (·.rows) == (expected.getLast?).map (·.rows) do
        fail "empty outer ON changed its null-extension rows"
    for predicate in ["not_a_function(a.k)", "coalesce(missing,1)", "sum(a.k)",
        "abs(a.k,a.k)", "likelihood(a.k,2.0)", "min(a.k COLLATE missing,'x')", "-0x8000000000000000"] do
      if (CoreSQL.execute Core.State.empty (setup ++
          s!"SELECT a.id,b.id FROM l a LEFT JOIN r b ON {predicate};")).isOk then
        fail s!"empty outer ON suppressed a required error: {predicate}"

  let nonempty := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,1);INSERT INTO r VALUES(1,1);"
  if (CoreSQL.execute Core.State.empty (nonempty ++
      "SELECT a.id,b.id FROM l a LEFT JOIN r b ON abs(-9223372036854775808);")).isOk then
    fail "nonempty outer ON lost its runtime overflow"

def expectSQLiteJoinZeroLimit : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,'bad');INSERT INTO r VALUES(1,2);"
  for predicate in ["abs(-9223372036854775808)","abs(a.k)","coalesce(a.k,b.k)",
      "json_extract(a.k,'$')","a.k+b.k>0","a.k LIKE 'a%'",
      "abs(-9223372036854775808) OR 1"] do
    for source in [s!"l a LEFT JOIN r b ON {predicate}", s!"l a,r b WHERE {predicate}"] do
      let sql := s!"SELECT a.id,b.id FROM {source} ORDER BY 2,1 LIMIT 0;"
      let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
        | .ok result => pure result
        | .error message => fail s!"zero-limit join: {sql}: {message}"
      unless (output.getLast?).map (·.rows) == some [] do fail "zero-limit join returned rows"
  for predicate in ["not_a_function(a.k)","coalesce(missing,1)","sum(a.k)",
      "abs(a.k,a.k)","likelihood(a.k,2.0)","min(a.k COLLATE missing,'x')",
      "1 OR min(a.k COLLATE missing,'x')", "-0x8000000000000000"] do
    let sql := s!"SELECT a.id,b.id FROM l a LEFT JOIN r b ON {predicate} LIMIT 0;"
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"zero-limit join suppressed a required error: {sql}"
  let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++
      "CREATE TABLE Extra AS SELECT a.id,b.id FROM l a LEFT JOIN r b ON abs(-9223372036854775808) OR 1 LIMIT 0;SELECT * FROM Extra;") with
    | .ok result => pure result
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some [] do fail "zero-limit CTAS returned rows"

def expectSQLiteJoinStaticConditions : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,'bad'),(2,NULL);INSERT INTO r VALUES(1,1);"
  for (predicate, selected) in [("0 AND abs(-9223372036854775808)",false),
      ("1 OR abs(-9223372036854775808)",true),("abs(a.k) IN ()",false),
      ("abs(-9223372036854775808) NOT IN ()",true),
      ("0 AND json_extract(a.k,'$')",false),("1 OR random()",true),
      ("1 AND 0 AND abs(b.k)",false)] do
    let sql := s!"SELECT a.id,b.id FROM l a JOIN r b ON {predicate} ORDER BY a.id,b.id;"
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"static joined condition: {message}"
    let expected ← match (if selected then [[Value.integer 1,.integer 1],[.integer 2,.integer 1]] else []).mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"static joined rows: {sql}"
  for sql in ["SELECT a.id FROM l a,r b WHERE abs(-9223372036854775808) OR 1 ORDER BY a.id;",
      "SELECT a.id FROM l a,r b WHERE 1 OR min(a.k COLLATE missing,'x') ORDER BY a.id;",
      "SELECT a.id FROM l a LEFT JOIN r b ON 1 OR abs(-9223372036854775808) ORDER BY a.id;"] do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail message
    let expected ← match ([[Value.integer 1],[.integer 2]]).mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail "static join context changed rows"
  for sql in ["SELECT a.id FROM l a,r b WHERE 0 AND not_a_function(a.k);",
      "SELECT a.id FROM l a,r b WHERE 0 AND coalesce(missing,1);",
      "SELECT a.id FROM l a,r b WHERE 1 OR sum(a.k);",
      "SELECT a.id FROM l a,r b WHERE 0 AND abs(a.k,a.k);",
      "SELECT a.id FROM l a,r b WHERE 1 OR likelihood(a.k,2.0);",
      "SELECT a.id FROM l a,r b WHERE 0 AND min(a.k COLLATE missing,'x');",
      "SELECT a.id FROM l a,r b WHERE abs(-9223372036854775808) AND 0;",
      "SELECT a.id FROM l a LEFT JOIN r b ON abs(-9223372036854775808) OR 1;",
      "SELECT a.id FROM l a LEFT JOIN r b ON 1 OR min(a.k COLLATE missing,'x') LIMIT 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"static joined condition suppressed a required error: {sql}"

def expectSQLiteLiteralNullPreparation : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k,true);CREATE TABLE r(id INTEGER PRIMARY KEY,k,true);INSERT INTO l VALUES(1,'a',1),(2,NULL,0);INSERT INTO r VALUES(1,'b',1);"
  for predicate in ["'x' IS NULL AND missing", "1 ISNULL AND missing",
      "-1 IS NULL AND missing", "- -1 ISNULL AND missing", "1e999 IS NULL AND missing",
      "X'00' IS NULL AND missing", "'x' IS NOT DISTINCT FROM NULL AND true",
      "-0x8000000000000000 IS NULL AND missing", "0x10000000000000000 ISNULL AND missing",
      "(1 NOTNULL) ISNULL AND missing"] do
    let sql := s!"SELECT a.id,b.id FROM l a LEFT JOIN r b ON {predicate} ORDER BY a.id;"
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"literal NULL preparation: {sql}: {message}"
    let expected ← match ([[Value.integer 1,.null],[.integer 2,.null]]).mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"literal NULL rows: {sql}"
  for predicate in ["1 COLLATE binary IS NULL AND missing", "NULL IS NULL AND missing",
      "~1 ISNULL AND missing", "(1+0) ISNULL AND missing", "true ISNULL AND missing",
      "1 NOTNULL AND missing", "1 ISNULL AND not_a_function()"] do
    if (CoreSQL.execute Core.State.empty (setup ++
        s!"SELECT a.id FROM l a,r b WHERE {predicate} LIMIT 0;")).isOk then
      fail s!"NULL preparation incorrectly hid required validation: {predicate}"
  let (_, output) ← match CoreSQL.execute Core.State.empty
      "SELECT 1 ISNULL, -1 NOTNULL, 'x' IS NOT DISTINCT FROM NULL, X'00' IS DISTINCT FROM NULL, -0x8000000000000000 ISNULL, 0x10000000000000000 ISNULL;" with
    | .ok result => pure result
    | .error message => fail message
  let expected ← match ([0,1,0,1,0,0] : List Int).mapM (fun number => SQLSurface.value (.integer number)) with
    | .ok values => pure values
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some [expected] do fail "literal NULL constant results"

def expectSQLiteJoinInList : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k TEXT);CREATE TABLE r(id INTEGER PRIMARY KEY,k NUMERIC);INSERT INTO l VALUES(1,NULL),(2,'1'),(3,'01'),(4,'a'),(5,'a ');INSERT INTO r VALUES(1,NULL),(2,1),(3,'A'),(4,'a ');"
  for (condition, values) in [
      ("a.k IN (b.k,NULL)", [[2,2],[5,4]]),
      ("a.k NOT IN (b.k,NULL)", []),
      ("a.k IN (b.k)", [[2,2],[5,4]]),
      ("a.k COLLATE nocase IN (b.k,NULL)", [[2,2],[4,3],[5,4]]),
      ("a.k COLLATE rtrim IN (b.k)", [[2,2],[4,4],[5,4]]),
      ("a.k IN (b.k COLLATE nocase)", [[2,2],[5,4]]),
      ("a.k IN (b.k COLLATE missing)", [[2,2],[5,4]])] do
    let sql := s!"SELECT a.id,b.id FROM l a JOIN r b ON {condition} ORDER BY a.id,b.id;"
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail message
    let expected ← match values.mapM (List.mapM (fun number : Int => SQLSurface.value (.integer number))) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"joined IN rows: {sql}"
  for (condition, values) in [("a.k NOT IN (0,1)",[3,4,5]),("a.k IN (1,2)",[2]),
      ("+a.k IN (1,2)",[]),("missing NOT IN ()",[1,2,3,4,5]),("missing IN ()",[]),
      ("a.k IN ('A' COLLATE nocase)",[4]),("a.k IN ('A' COLLATE nocase,'z')",[]),
      ("a.k IN ('A' COLLATE missing,'z')",[])] do
    let sql := s!"SELECT a.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE {condition} ORDER BY a.id;"
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail message
    let expected ← match values.mapM (fun number : Int => do return [← SQLSurface.value (.integer number)]) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"joined IN affinity or preparation: {sql}"
  for condition in ["a.k IN (missing,NULL)","a.k COLLATE missing IN (b.k,NULL)",
      "a.k IN ('A' COLLATE missing)"] do
    if (CoreSQL.execute Core.State.empty (setup ++
        s!"SELECT a.id FROM l a,r b WHERE {condition} LIMIT 0;")).isOk then
      fail s!"joined IN omitted required validation: {condition}"

end SQLeanite.Tests
