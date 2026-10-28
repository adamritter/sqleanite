import SQLeaniteTests.ExpectPageSizeConversionFailures

namespace SQLeanite.Tests
open SQLeanite

def expectSQLiteMath : IO Unit := do
  let setup := "CREATE TABLE e(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT ceil(1.25),floor(-1.25),trunc(-1.75),ceiling(-0.5);",
      [[.real 2.0, .real (-2.0), .real (-1.0), .real (-0.0)]]),
    ("SELECT typeof(ceil('1')),typeof(ceil('1.0')),floor(9223372036854775807);",
      [[.text "integer", .text "real", .integer 9223372036854775807]]),
    ("SELECT ceil(CAST(X'31320078' AS TEXT)),typeof(ceil(CAST(X'312E300078' AS TEXT)));",
      [[.integer 12, .text "real"]]),
    ("SELECT log(2,'8x'),log(2,X'38'),log(0.5,8),log(1,8),ln(-1),sqrt(-1),pow(-1,0.5),mod(1,0);",
      [[.real 3.0, .real 3.0, .null, .null, .null, .null, .null, .null]]),
    ("SELECT mod(5.5,2),mod(-5.5,2),mod(5.5,-2),mod(1,1e999),mod(1e999,2);",
      [[.real 1.5, .real (-1.5), .real 1.5, .real 1.0, .null]]),
    ("SELECT acos(1),asin(0),atan(0),atan2(0,1),acosh(1),asinh(0),atanh(0);",
      [[.real 0.0, .real 0.0, .real 0.0, .real 0.0, .real 0.0, .real 0.0, .real 0.0]]),
    ("SELECT cos(0),cosh(0),sin(0),sinh(0),tan(0),tanh(0),exp(0),ln(1);",
      [[.real 1.0, .real 1.0, .real 0.0, .real 0.0, .real 0.0, .real 0.0, .real 1.0, .real 0.0]]),
    ("SELECT log(100),log2(8),log10(1000),sqrt(9),pow(2,3),power(2,3),degrees(pi()),radians(180)=pi();",
      [[.real 2.0, .real 3.0, .real 3.0, .real 3.0, .real 8.0, .real 8.0, .real 180.0, .integer 1]]),
    ("SELECT ceil(NULL),sqrt(X'39'),sin('12tail'),ceil('NaN'),ln('Inf');",
      [[.null, .null, .null, .null, .null]]),
    ("SELECT sqrt(abs(-9223372036854775808)) FROM e;", []),
    ("SELECT sqrt(abs(-9223372036854775808)) LIMIT 0;", []),
    ("SELECT coalesce(7,sqrt(abs(-9223372036854775808)));", [[.integer 7]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"math functions: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"math function mismatch: {sql}"
  for sql in ["SELECT sqrt(abs(-9223372036854775808));", "SELECT pi(1);", "SELECT log();",
      "SELECT sqrt(missing) FROM e LIMIT 0;", "SELECT pow(1) FROM e LIMIT 0;",
      "SELECT log(1,2,3);", "SELECT pi() FILTER(WHERE 1);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"math function error omitted: {sql}"
  for (direction, value, expected) in [
      (SQLite.Math.Direction.zero, -0.5, 0x8000000000000000),
      (.up, -0.5, 0x8000000000000000), (.down, 0.5, 0),
      (.zero, -0.0, 0x8000000000000000)] do
    unless (SQLite.Math.roundFloat direction value).toBits == expected do fail "rounding lost signed zero"
  for (left, right, expected) in [(-4.0, 2.0, 0x8000000000000000),
      (-0.0, 1.0, 0x8000000000000000), (Float.ofBits 3, Float.ofBits 2, 1)] do
    match SQLite.Math.remainder left right with
    | .real value => unless value.toBits == expected do fail "remainder lost exact bits"
    | _ => fail "remainder lost REAL type"

def expectSQLiteUnicodeEscape : IO Unit := do
  let setup := "CREATE TABLE e(id INTEGER PRIMARY KEY,v);"
  let cases : List (String × List (List Value)) := [
    ("SELECT unistr(NULL),unistr_quote(NULL);", [[.null, .text "NULL"]]),
    ("SELECT unistr(X'5C7530303431'),unistr(1.25);", [[.text "A", .text "1.25"]]),
    ("SELECT hex(unistr(X'5C75303030305C7530303431'));", [[.text "0041"]]),
    ("SELECT hex(unistr(X'005C71'));", [[.text "005C71"]]),
    ("SELECT hex(unistr(X'5C7530303431005C71'));", [[.text "41005C71"]]),
    ("SELECT hex(unistr(X'5C7544383030'));", [[.text "EDA080"]]),
    ("SELECT hex(unistr(X'5C554646464646464646'));", [[.text "F7BFBFBF"]]),
    ("SELECT hex(unistr(X'5C553030323030303030'));", [[.text "F0808080"]]),
    ("SELECT hex(unistr(X'FF805C7530303431'));", [[.text "FF8041"]]),
    ("SELECT hex(unistr_quote(CAST(X'610A5C27' AS TEXT)));",
      [[.text "756E697374722827615C75303030615C5C27272729"]]),
    ("SELECT unistr_quote(CAST(X'615C62' AS TEXT));", [[.text "'a\\b'"]]),
    ("SELECT unistr_quote(CAST(X'61001B' AS TEXT));", [[.text "'a'"]]),
    ("SELECT unistr_quote(X'001BFF');", [[.text "X'001BFF'"]]),
    ("SELECT unistr(X'5C71') FROM e;", []),
    ("SELECT unistr(X'5C71') LIMIT 0;", []),
    ("SELECT unistr(X'5C71') LIMIT 1 OFFSET 1;", []),
    ("SELECT coalesce('x',unistr(X'5C71'));", [[.text "x"]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"Unicode escape: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"Unicode escape mismatch: {sql}"
  for sql in ["SELECT unistr(X'5C71');", "SELECT unistr(X'5C753132');",
      "SELECT unistr(X'5C7530300031');", "SELECT unistr();", "SELECT unistr_quote(1,2);",
      "SELECT unistr(missing) FROM e LIMIT 0;", "SELECT unistr_quote(missing) FROM e LIMIT 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"Unicode escape error omitted: {sql}"

def expectSQLiteStringAggregates : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,g,v,s);" ++
    "INSERT INTO t VALUES(1,0,NULL,'!'),(2,0,'A',':'),(3,1,'a',NULL),(4,1,'A',':');" ++
    "CREATE TABLE b(id INTEGER PRIMARY KEY,v,s);" ++
    "INSERT INTO b VALUES(1,X'FF0080','!'),(2,X'410042',X'00FF'),(3,1,7),(4,1.0,NULL);" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,g,v,s);"
  let cases : List (String × List (List Value)) := [
    ("SELECT group_concat(v),group_concat(v,s),string_agg(v,s) FROM t;",
      [[.text "A,a,A", .text "Aa:A", .text "Aa:A"]]),
    ("SELECT group_concat(DISTINCT v),group_concat(DISTINCT v COLLATE NOCASE) FROM t;",
      [[.text "A,a", .text "A"]]),
    ("SELECT g,group_concat(v,s) FROM t GROUP BY g ORDER BY g;",
      [[.integer 0, .text "A"], [.integer 1, .text "a:A"]]),
    ("SELECT typeof(group_concat(v)),hex(group_concat(v,s)) FROM b;",
      [[.text "text", .text "FF008000FF4100423731312E30"]]),
    ("SELECT group_concat(DISTINCT v),group_concat(v) FROM b WHERE id>2;",
      [[.text "1", .text "1,1.0"]]),
    ("SELECT id,min(id),group_concat(v,s) FROM t;", [[.integer 1, .integer 1, .text "Aa:A"]]),
    ("SELECT group_concat(v,s),typeof(group_concat(v)) FROM e;", [[.null, .text "null"]]),
    ("SELECT group_concat(v,s) FROM t WHERE v IS NULL;", [[.null]]),
    ("SELECT group_concat(v,s) FROM e GROUP BY g;", []),
    ("SELECT typeof(group_concat('')),hex(group_concat(''));", [[.text "text", .text ""]]),
    ("SELECT hex(group_concat(X'FF0080'));", [[.text "FF0080"]]),
    ("SELECT group_concat(0 AND 0x10000000000000000);", [[.text "0"]]),
    ("SELECT group_concat(v COLLATE missing,s) FROM t;", [[.text "Aa:A"]]),
    ("SELECT group_concat(v,s) AS x FROM t HAVING x='Aa:A';", [[.text "Aa:A"]]),
    ("SELECT group_concat(v,abs(-9223372036854775808)) FROM e;", [[.null]]),
    ("SELECT group_concat(NULL,abs(-9223372036854775808)) LIMIT 0;", []),
    ("SELECT group_concat(v,s) FROM t LIMIT 1 OFFSET 1;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"string aggregate: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"string aggregate mismatch: {sql}"
  for sql in ["SELECT group_concat(NULL,abs(-9223372036854775808));",
      "SELECT group_concat('x',abs(-9223372036854775808));",
      "SELECT group_concat(DISTINCT v,s) FROM e LIMIT 0;", "SELECT string_agg(v) FROM e LIMIT 0;",
      "SELECT group_concat(DISTINCT v COLLATE missing) FROM e LIMIT 0;",
      "SELECT group_concat(v,missing) FROM e LIMIT 0;", "SELECT group_concat(sum(v)) FROM e;",
      "SELECT group_concat(v,abs(-9223372036854775808)) FROM t HAVING 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"string aggregate error omitted: {sql}"

def expectSQLiteGroupedExpressions : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,g,v);INSERT INTO t VALUES(1,'A',2),(2,'a',1),(3,'b',4),(4,'B',3),(5,NULL,5),(6,1,6),(7,1.0,8);" ++
    "CREATE TABLE o(id INTEGER PRIMARY KEY,g,v);INSERT INTO o VALUES(1,1,9223372036854775807),(2,1,1),(3,2,2),(4,3,3);"
  let cases : List (String × List (List Value)) := [
    ("SELECT g,count(*) AS x FROM t GROUP BY g COLLATE NOCASE HAVING x>1 ORDER BY x DESC,g;",
      [[.integer 1, .integer 2], [.text "A", .integer 2], [.text "b", .integer 2]]),
    ("SELECT g,sum(v)+count(*) FROM t GROUP BY g COLLATE NOCASE HAVING count(*)>1 ORDER BY 2 DESC;",
      [[.integer 1, .integer 16], [.text "b", .integer 9], [.text "A", .integer 5]]),
    ("SELECT g,count(*) FROM t GROUP BY g COLLATE NOCASE HAVING g='a';", []),
    ("SELECT g,count(*) FROM t GROUP BY g HAVING g='a';", [[.text "a", .integer 1]]),
    ("SELECT g,sum(v) FROM o GROUP BY g HAVING g>1;", [[.integer 2, .integer 2], [.integer 3, .integer 3]]),
    ("SELECT g,sum(v) FROM o GROUP BY g HAVING NULL;", []),
    ("SELECT g,sum(v) FROM o GROUP BY g ORDER BY g DESC LIMIT 1;", [[.integer 3, .integer 3]]),
    ("SELECT g,sum(v) FROM o GROUP BY g LIMIT 0;", []),
    ("SELECT DISTINCT count(*) FROM t GROUP BY g ORDER BY 1 DESC;", [[.integer 2], [.integer 1]]),
    ("SELECT g,abs(-9223372036854775808) FROM t GROUP BY g LIMIT 1 OFFSET 100;", []),
    ("SELECT g,abs(-9223372036854775808) FROM t GROUP BY g HAVING 0;", []),
    ("SELECT +g,+g,max(id),typeof(+g) FROM t WHERE id>=6 GROUP BY +g;",
      [[.real 1.0, .integer 1, .integer 7, .text "real"]]),
    ("SELECT g||'',max(id),g FROM t WHERE id<=2 GROUP BY g||'' COLLATE NOCASE;",
      [[.text "a", .integer 2, .text "a"]]),
    ("SELECT g||'',max(id),g FROM t WHERE id<=2 GROUP BY 1 COLLATE NOCASE;",
      [[.text "A", .integer 2, .text "a"]]),
    ("SELECT g||'',max(id),g FROM t WHERE id<=2 GROUP BY 1 COLLATE NOCASE ORDER BY 1;",
      [[.text "a", .integer 2, .text "a"]]),
    ("SELECT DISTINCT g||'' AS k,max(id),g FROM t WHERE id<=2 GROUP BY 1 COLLATE NOCASE ORDER BY k;",
      [[.text "A", .integer 2, .text "a"]]),
    ("SELECT g+1 AS k,count(*) FROM o WHERE k>2 GROUP BY k;", [[.integer 3, .integer 1], [.integer 4, .integer 1]]),
    ("SELECT count(*) GROUP BY 1+0 HAVING count(*)>0;", [[.integer 1]]),
    ("SELECT 1 GROUP BY 1;", [[.integer 1]]),
    ("SELECT count(*) WHERE 0 GROUP BY 1+0;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"grouped expression: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"grouped expression mismatch: {sql}"
  for sql in ["SELECT g,sum(v) FROM o GROUP BY g HAVING 0;", "SELECT g,sum(v) FROM o GROUP BY g ORDER BY g LIMIT 1;",
      "SELECT count(*) FROM t GROUP BY 1;", "SELECT count(*) FROM t GROUP BY missing LIMIT 0;",
      "SELECT count(*) FROM t GROUP BY g COLLATE missing LIMIT 0;", "SELECT count(*) FROM t GROUP BY g HAVING missing LIMIT 0;",
      "SELECT DISTINCT g,abs(-9223372036854775808) FROM t GROUP BY g LIMIT 1 OFFSET 100;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"grouped expression error omitted: {sql}"

def expectSQLiteAggregateHaving : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,w TEXT);INSERT INTO t VALUES(1,3,'first'),(2,1,'low'),(3,9,'high'),(4,1,'tie');" ++
    "CREATE TABLE e(id INTEGER PRIMARY KEY,v,w TEXT);CREATE TABLE n(id INTEGER PRIMARY KEY,v,w TEXT);INSERT INTO n VALUES(1,NULL,'first'),(2,NULL,'last');" ++
    "CREATE TABLE d(id INTEGER PRIMARY KEY,v);INSERT INTO d VALUES(1,3),(2,1),(3,1);" ++
    "CREATE TABLE tx(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO tx VALUES(1,'4');" ++
    "CREATE TABLE o(id INTEGER PRIMARY KEY,v);INSERT INTO o VALUES(1,9223372036854775807),(2,1);"
  let cases : List (String × List (List Value)) := [
    ("SELECT count(*) AS x FROM t HAVING x=4;", [[.integer 4]]),
    ("SELECT count(*) FROM t HAVING 0;", []),
    ("SELECT count(*) FROM t HAVING NULL;", []),
    ("SELECT sum(v) AS v FROM t HAVING v=3;", [[.integer 14]]),
    ("SELECT id,w,min(v) FROM t HAVING 1;", [[.integer 2, .text "low", .integer 1]]),
    ("SELECT id,w,min(v),max(v),min(t.v) FROM t HAVING id=3;",
      [[.integer 3, .text "high", .integer 1, .integer 9, .integer 1]]),
    ("SELECT id,min(DISTINCT v) FROM d HAVING id=3;", [[.integer 3, .integer 1]]),
    ("SELECT id,min(v) FROM d HAVING id=2;", [[.integer 2, .integer 1]]),
    ("SELECT id,w,min(v) FROM n HAVING id=2;", [[.integer 2, .text "last", .null]]),
    ("SELECT id,w,count(*) FROM e HAVING id IS NULL;", [[.null, .null, .integer 0]]),
    ("SELECT count(*) FROM t HAVING id=2 ORDER BY min(v);", [[.integer 4]]),
    ("SELECT count(*) FROM t HAVING id=3 AND max(v)>0 ORDER BY min(v);", [[.integer 4]]),
    ("SELECT count(*) FROM tx HAVING v=4;", [[.integer 1]]),
    ("SELECT min(v) AS x FROM tx HAVING x=4;", []),
    ("SELECT count(*) FROM t HAVING count(*)>0 OR abs(-9223372036854775808);", [[.integer 4]]),
    ("SELECT count(*) FROM t HAVING count(*)<0 AND abs(-9223372036854775808);", []),
    ("SELECT abs(-9223372036854775808)+count(*) FROM t HAVING 0;", []),
    ("SELECT count(*) FROM t HAVING 1 COLLATE missing;", [[.integer 4]]),
    ("SELECT count(*) AS x WHERE 0 HAVING x=0;", [[.integer 0]]),
    ("SELECT count(*) HAVING count(*)=1;", [[.integer 1]]),
    ("SELECT count(*) FROM o HAVING 0 ORDER BY sum(v) LIMIT 0;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate HAVING: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"aggregate HAVING mismatch: {sql}"
  for sql in ["SELECT sum(v) FROM o HAVING 0;", "SELECT count(*) FROM o HAVING 0 ORDER BY sum(v);",
      "SELECT count(*) FROM t HAVING abs(-9223372036854775808) LIMIT 1 OFFSET 1;",
      "SELECT 1 FROM t HAVING count(*)>0;", "SELECT count(*) FROM t HAVING sum(sum(v));",
      "SELECT count(*) FROM t HAVING missing LIMIT 0;", "SELECT count(*) FROM t HAVING v=1 COLLATE missing;",
      "SELECT count(*) FROM t HAVING 0 AND no_function(1);", "SELECT count(*) HAVING rowid IS NULL;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"aggregate HAVING error omitted: {sql}"

def expectSQLiteAggregateOrder : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1),(2,2),(3,3);"
  let cases : List (String × List (List Value)) := [
    ("SELECT count(*) FROM t ORDER BY v;", [[.integer 3]]),
    ("SELECT count(*) AS x FROM t ORDER BY x DESC;", [[.integer 3]]),
    ("SELECT sum(v)+count(*) AS x FROM t ORDER BY x;", [[.integer 9]]),
    ("SELECT count(*) FROM t ORDER BY abs(-9223372036854775808);", [[.integer 3]]),
    ("SELECT count(*) FROM t WHERE 0 ORDER BY sum(abs(-9223372036854775808));", [[.integer 0]]),
    ("SELECT count(*) FROM t ORDER BY sum(abs(-9223372036854775808)) LIMIT 0;", []),
    ("SELECT min(v COLLATE NOCASE) FROM t ORDER BY 1 COLLATE RTRIM;", [[.integer 1]]),
    ("SELECT 1 ORDER BY sum(abs(-9223372036854775808));", [[.integer 1]]),
    ("SELECT 1 WHERE 0 ORDER BY count(*);", []),
    ("SELECT count(*),0 AND 0x10000000000000000 ORDER BY 1;", [[.integer 1, .integer 0]]),
    ("SELECT count(*) ORDER BY abs(-9223372036854775808);", [[.integer 1]]),
    ("SELECT sum(1) WHERE 0 ORDER BY sum(abs(-9223372036854775808));", [[.null]]),
    ("SELECT count(*) FROM t ORDER BY v LIMIT 1 OFFSET 1;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"aggregate ORDER BY: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"aggregate ORDER BY mismatch: {sql}"
  for sql in ["SELECT count(*) FROM t ORDER BY sum(abs(-9223372036854775808));",
      "SELECT count(*) FROM t ORDER BY sum(abs(-9223372036854775808)) LIMIT 1 OFFSET 1;",
      "SELECT count(*) FROM t ORDER BY missing LIMIT 0;", "SELECT count(*) FROM t ORDER BY 2;",
      "SELECT count(*) FROM t ORDER BY 1 COLLATE missing;", "SELECT count(*) FROM t ORDER BY no_function(v);",
      "SELECT count(*) FROM t ORDER BY min(v COLLATE missing);", "SELECT 1 FROM t ORDER BY count(*);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then fail s!"aggregate ORDER BY error omitted: {sql}"

def expectSQLiteNumericLiterals : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("SELECT 0xFFFFFFFFFFFFFFFF,0x8000000000000000,0x7FFFFFFFFFFFFFFF,0x80000000;",
      [[.integer (-1), .integer (-9223372036854775808), .integer 9223372036854775807, .integer 2147483648]]),
    ("SELECT 1_000,1_0.0_5,0xA_B,1e1_0;", [[.integer 1000, .real 10.05, .integer 171, .real 10000000000.0]]),
    ("SELECT 0 AND 0x10000000000000000,0x10000000000000000 AND 0;", [[.integer 0, .integer 0]]),
    ("SELECT -0xffffffffffffffff,~0xffffffffffffffff;", [[.integer 1, .integer 0]]),
    ("SELECT 0x0000000000000000000000FFFFFFFFFFFFFFFF;", [[.integer (-1)]]),
    ("SELECT -(9223372036854775808),typeof(-(9223372036854775808));", [[.integer (-9223372036854775808), .text "integer"]]),
    ("SELECT -(+9223372036854775808),typeof(-(+9223372036854775808));", [[.integer (-9223372036854775808), .text "integer"]]),
    ("SELECT -(0x8000000000000000 COLLATE BINARY);", [[.real 9223372036854775808.0]]),
    ("SELECT 1_0.0 UNION ALL SELECT 2 ORDER BY 10.0;", [[.integer 2], [.real 10.0]]),
    ("SELECT 214748364_8 UNION ALL SELECT 2 ORDER BY 2147483648;", [[.integer 2], [.integer 2147483648]]),
    ("SELECT 0xFFFFFFFFFFFFFFFF LIMIT 0xFFFFFFFFFFFFFFFF;", [[.integer (-1)]]),
    ("SELECT CAST('0xffff' AS INTEGER),CAST('1_000' AS INTEGER);", [[.integer 0, .integer 1]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"numeric literal: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"numeric literal mismatch: {sql}"
  for sql in ["SELECT 1__0;", "SELECT 1._0;", "SELECT 0x_1;", "SELECT 0x1g;",
      "SELECT 0x10000000000000000;", "SELECT 0x10000000000000000 LIMIT 0;",
      "SELECT 1 LIMIT 0 OFFSET 0x10000000000000000;", "SELECT -0x8000000000000000 LIMIT 0;",
      "SELECT -(+0x8000000000000000);", "SELECT CASE WHEN 0 THEN -0x8000000000000000 ELSE 1 END;",
      "SELECT 1e+;", "SELECT 123abc;", "SELECT 2147483648 UNION SELECT 2 ORDER BY 02147483648;"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"numeric literal error omitted: {sql}"
  let tokens ← match lex "SELECT 1;" with
    | .ok tokens => pure tokens
    | .error message => fail message
  let wrong : Array Statement := #[.select { columns := #[{ expr := .literal (.real 1.0) }] }]
  if (CoreTokenGrammar.check tokens wrong).isOk then fail "numeric token checker changed INTEGER storage class"

def expectSQLiteLiteralSpelling : IO Unit := do
  let cases : List (String × List (List Value)) := [
    ("SELECT 1.0 UNION ALL SELECT 2 ORDER BY 1.0;", [[.real 1.0], [.integer 2]]),
    ("SELECT 1.0 AS x UNION ALL SELECT 2 ORDER BY x;", [[.real 1.0], [.integer 2]]),
    ("SELECT 1.0,1.00 UNION ALL SELECT 2,0 ORDER BY 1.00;", [[.integer 2, .integer 0], [.real 1.0, .real 1.0]]),
    ("SELECT 1.0 UNION SELECT 1.00 ORDER BY 1.00;", [[.real 1.0]]),
    ("SELECT 1.0 AS x,abs(1.0) UNION ALL SELECT 2,3 ORDER BY abs(x);", [[.real 1.0, .real 1.0], [.integer 2, .integer 3]]),
    ("SELECT 1.0=1.00,1.0+1.00,-1.25;", [[.integer 1, .real 2.0, .real (-1.25)]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty sql with
      | .ok result => pure result
      | .error message => fail s!"literal spelling: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"literal spelling mismatch: {sql}"
  for sql in ["SELECT 0 AND 1.0 UNION ALL SELECT 2 ORDER BY 0 AND 1.00;",
      "SELECT 1.0 UNION SELECT 2 ORDER BY 1.00;",
      "SELECT 1e0 UNION SELECT 2 ORDER BY 1E0;",
      "SELECT abs(1.0) UNION ALL SELECT 2 ORDER BY abs(1.00);",
      "SELECT CASE WHEN 1 THEN 1.0 END UNION SELECT 2 ORDER BY CASE WHEN 1 THEN 1.00 END;",
      "SELECT 1.0 AS x,abs(1.00) UNION ALL SELECT 2,3 ORDER BY abs(x);"] do
    if (CoreSQL.execute Core.State.empty sql).isOk then fail s!"literal token identity lost: {sql}"
  let tokens ← match lex "SELECT 1.0;" with
    | .ok tokens => pure tokens
    | .error message => fail message
  let changed ← match parse "SELECT 1.00;" with
    | .ok statements => pure statements
    | .error message => fail message
  if (CoreTokenGrammar.check tokens changed).isOk then fail "REAL spelling certificate accepted a changed token"
  let dropped : Array Statement := #[.select { columns := #[{ expr := .literal (.real 1.0) }] }]
  if (CoreTokenGrammar.check tokens dropped).isOk then fail "REAL spelling certificate accepted missing provenance"

def expectSQLiteCompoundTails : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'A'),(2,'a'),(3,'B'),(4,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT 1 AS a,2 AS b UNION ALL SELECT 3 AS c,0 AS d ORDER BY d;",
      [[.integer 3, .integer 0], [.integer 1, .integer 2]]),
    ("SELECT 1 AS a,2 AS b UNION ALL SELECT 3 AS c,0 AS a ORDER BY a;",
      [[.integer 1, .integer 2], [.integer 3, .integer 0]]),
    ("SELECT a.v FROM t AS a JOIN t AS b ON a.id=b.id UNION SELECT v FROM t ORDER BY 1 DESC LIMIT 3;",
      [[.text "a"], [.text "B"], [.text "A"]]),
    ("SELECT v FROM t UNION ALL SELECT 'c' ORDER BY 1 DESC NULLS FIRST LIMIT 3;",
      [[.null], [.text "c"], [.text "a"]]),
    ("SELECT 'A' COLLATE NOCASE UNION SELECT 'a' ORDER BY 1 DESC;", [[.text "a"]]),
    ("SELECT 'A' COLLATE NOCASE INTERSECT SELECT 'a' ORDER BY 1 COLLATE BINARY;", [[.text "A"]]),
    ("SELECT 'A' COLLATE BINARY INTERSECT SELECT 'a' ORDER BY 1 COLLATE NOCASE;", []),
    ("SELECT 1 UNION ALL SELECT abs(-9223372036854775808) LIMIT 1;", [[.integer 1]]),
    ("SELECT abs(-9223372036854775808) UNION ALL SELECT 2 LIMIT 1 OFFSET 1;", [[.integer 2]]),
    ("SELECT abs(-9223372036854775808) FROM t UNION ALL SELECT 2 LIMIT 1 OFFSET 4;", [[.integer 2]]),
    ("SELECT 1 UNION SELECT 1 UNION ALL SELECT abs(-9223372036854775808) LIMIT 1;", [[.integer 1]]),
    ("SELECT 1 WHERE 0 INTERSECT SELECT abs(-9223372036854775808) ORDER BY 1;", []),
    ("SELECT abs(-9223372036854775808) UNION SELECT 2 LIMIT 0;", []),
    ("SELECT min(v) AS x FROM t UNION SELECT max(v) FROM t ORDER BY x DESC;", [[.text "a"], [.text "A"]]),
    ("SELECT CAST(X'410078' AS TEXT) COLLATE NOCASE UNION SELECT CAST(X'610059' AS TEXT) ORDER BY 1 DESC;",
      [[.textBytes #[97, 0, 89]]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"compound tail: {sql}: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"compound tail mismatch: {sql}"
  for sql in ["SELECT 1 UNION ALL SELECT missing LIMIT 0;",
      "SELECT 1 UNION ALL SELECT 1,2 LIMIT 0;",
      "SELECT v FROM t UNION SELECT v FROM t ORDER BY v+1;",
      "SELECT 1 UNION ALL SELECT 2 ORDER BY 1 COLLATE missing LIMIT 0;",
      "SELECT 1 UNION ALL SELECT 2 ORDER BY 0 LIMIT 0;",
      "SELECT CASE WHEN 1 THEN 2 END UNION SELECT 3 ORDER BY CASE WHEN 1 THEN 4 END;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"compound tail error omitted: {sql}"
    | .error _ => pure ()

def expectSQLiteCompoundCollations : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'A'),(2,'a'),(3,'B'),(4,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT 'A' COLLATE NOCASE UNION SELECT 'a';", [[.text "a"]]),
    ("SELECT 'A' UNION SELECT 'a' COLLATE NOCASE;", [[.text "a"]]),
    ("SELECT 'A' COLLATE BINARY UNION SELECT 'a' COLLATE NOCASE;", [[.text "A"], [.text "a"]]),
    ("SELECT 'a' COLLATE RTRIM INTERSECT SELECT 'a ';", [[.text "a"]]),
    ("SELECT 'a' COLLATE RTRIM EXCEPT SELECT 'a ';", []),
    ("SELECT 'A' COLLATE NOCASE,1 UNION SELECT 'a',1.0;", [[.text "a", .real 1.0]]),
    ("SELECT v FROM t UNION SELECT 'a' COLLATE NOCASE;", [[.null], [.text "A"], [.text "B"], [.text "a"]]),
    ("SELECT +v FROM t UNION SELECT 'a' COLLATE NOCASE;", [[.null], [.text "A"], [.text "B"], [.text "a"]]),
    ("SELECT CAST(v AS TEXT) FROM t UNION SELECT 'a' COLLATE NOCASE;", [[.null], [.text "A"], [.text "B"], [.text "a"]]),
    ("SELECT v||'' FROM t UNION SELECT 'a' COLLATE NOCASE;", [[.null], [.text "a"], [.text "B"]]),
    ("SELECT v FROM t UNION SELECT 'a' COLLATE missing;", [[.null], [.text "A"], [.text "B"], [.text "a"]]),
    ("SELECT 1 COLLATE missing UNION ALL SELECT 2;", [[.integer 1], [.integer 2]]),
    ("SELECT CAST(X'410078' AS TEXT) COLLATE NOCASE UNION SELECT CAST(X'610059' AS TEXT);",
      [[.textBytes #[97, 0, 89]]]),
    ("SELECT CAST(X'410078' AS TEXT) COLLATE NOCASE INTERSECT SELECT CAST(X'610059' AS TEXT);",
      [[.textBytes #[65, 0, 120]]]),
    ("SELECT CAST(X'FF41' AS TEXT) COLLATE NOCASE UNION SELECT CAST(X'FF61' AS TEXT);",
      [[.textBytes #[255, 97]]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"compound COLLATE: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"compound COLLATE mismatch: {sql}"
  for sql in ["SELECT 1 COLLATE missing UNION SELECT 2;", "SELECT 'a' UNION SELECT 'A' COLLATE missing;",
      "SELECT 'a' COLLATE NOCASE UNION SELECT 1,2;"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"compound collation/width error omitted: {sql}"
    | .error _ => pure ()

def expectSQLiteCollatedGroups : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,n); INSERT INTO t VALUES(1,'a',3),(2,'A',1),(3,'a ',2),(4,'B',4),(5,NULL,NULL),(6,NULL,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT v,count(*) FROM t GROUP BY v COLLATE NOCASE;",
      [[.null, .integer 2], [.text "a", .integer 2], [.text "a ", .integer 1], [.text "B", .integer 1]]),
    ("SELECT v,min(n) FROM t GROUP BY v COLLATE NOCASE;",
      [[.null, .null], [.text "A", .integer 1], [.text "a ", .integer 2], [.text "B", .integer 4]]),
    ("SELECT v,max(n),min(n),max(n) FROM t GROUP BY v COLLATE NOCASE LIMIT 1 OFFSET 1;",
      [[.text "A", .integer 3, .integer 1, .integer 3]]),
    ("SELECT v COLLATE NOCASE,count(*) FROM t WHERE v COLLATE NOCASE='a' GROUP BY v COLLATE NOCASE;",
      [[.text "a", .integer 2]]),
    ("SELECT v,count(*) FROM t GROUP BY v COLLATE RTRIM LIMIT 1 OFFSET 3;", [[.text "a", .integer 2]]),
    ("SELECT v,sum(n) FROM t GROUP BY v COLLATE NOCASE LIMIT 0;", [])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"collated group: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"collated group mismatch: {sql}"
  let huge := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,n);INSERT INTO t VALUES(1,'a',9223372036854775807),(2,'A',1),(3,'b',0),(4,'c',9223372036854775807),(5,'C',1);"
  for sql in ["SELECT v,sum(n) FROM t GROUP BY v COLLATE NOCASE LIMIT 0;",
      "SELECT v,sum(n) FROM t WHERE id>2 GROUP BY v COLLATE NOCASE LIMIT 1;"] do
    match CoreSQL.execute Core.State.empty (huge ++ sql) with
    | .error message => fail s!"group LIMIT evaluated excluded accumulator: {message}"
    | .ok _ => pure ()
  for sql in ["SELECT v,sum(n) FROM t GROUP BY v COLLATE NOCASE LIMIT 1 OFFSET 1;",
      "SELECT v,count(*) FROM t GROUP BY v COLLATE missing LIMIT 0;"] do
    match CoreSQL.execute Core.State.empty (huge ++ sql) with
    | .ok _ => fail "group OFFSET/metadata omitted required error"
    | .error _ => pure ()

def expectSQLiteExpressionCollations : IO Unit := do
  let setup := "CREATE TABLE t(id INTEGER PRIMARY KEY,v,txt TEXT); INSERT INTO t VALUES(1,'a',1),(2,'A',2),(3,'a ',3),(4,NULL,4);"
  let cases : List (String × List (List Value)) := [
    ("SELECT 'A' COLLATE NOCASE='a','a' COLLATE RTRIM='a ',X'41' COLLATE NOCASE='a';",
      [[.integer 1, .integer 1, .integer 0]]),
    ("SELECT 'a' IN ('A' COLLATE NOCASE),'a' IN ('A' COLLATE NOCASE,'z'),'a' COLLATE NOCASE IN ('A','z','x');",
      [[.integer 1, .integer 0, .integer 1]]),
    ("SELECT CASE 'a' WHEN 'A' COLLATE NOCASE THEN 1 ELSE 0 END,min('a' COLLATE NOCASE,'A'),max('a' COLLATE NOCASE,'A');",
      [[.integer 1, .text "A", .text "a"]]),
    ("SELECT id FROM t WHERE txt COLLATE NOCASE=1;", [[.integer 1]]),
    ("SELECT id FROM t WHERE v='a' COLLATE NOCASE ORDER BY id;", [[.integer 1], [.integer 2]]),
    ("SELECT DISTINCT v COLLATE NOCASE FROM t;", [[.text "a"], [.text "a "], [.null]]),
    ("SELECT DISTINCT v COLLATE RTRIM FROM t ORDER BY v COLLATE RTRIM;", [[.null], [.text "A"], [.text "a"]]),
    ("SELECT min(v COLLATE NOCASE)='A',max(v COLLATE RTRIM)='a',count(DISTINCT v COLLATE NOCASE) FROM t;",
      [[.integer 1, .integer 1, .integer 2]]),
    ("SELECT nullif(min(v COLLATE NOCASE),'A'),coalesce(min(v COLLATE NOCASE),'z')='A' FROM t;", [[.null, .integer 1]]),
    ("SELECT 1 COLLATE missing,1 IN (1 COLLATE missing,2),CASE WHEN 1 THEN 7 ELSE 2 COLLATE NOCASE END;",
      [[.integer 1, .integer 1, .integer 7]]),
    ("UPDATE t SET v='changed' WHERE v COLLATE NOCASE='A'; SELECT v FROM t WHERE id=2;", [[.text "changed"]])]
  for (sql, expected) in cases do
    let (_, results) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"expression COLLATE: {message}"
    let rows ← match expected.mapM (List.mapM SQLSurface.value) with
      | .ok result => pure result
      | .error message => fail message
    unless (results.getLast?).map (·.rows) == some rows do fail s!"expression COLLATE mismatch: {sql}"
  for sql in ["SELECT 1 COLLATE missing=1 LIMIT 0;", "SELECT DISTINCT 1 COLLATE missing;",
      "SELECT min(v COLLATE missing) FROM t LIMIT 0;", "SELECT DISTINCT sum(id) COLLATE missing FROM t;",
      "SELECT DISTINCT sum(1) COLLATE missing;", "SELECT 1 IN (1 COLLATE missing);"] do
    match CoreSQL.execute Core.State.empty (setup ++ sql) with
    | .ok _ => fail s!"missing COLLATE was silently used: {sql}"
    | .error _ => pure ()

end SQLeanite.Tests
