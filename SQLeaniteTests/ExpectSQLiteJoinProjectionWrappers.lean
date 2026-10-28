import SQLeaniteTests.ExpectSQLiteQuotedFunctions
import SQLeaniteTests.ExpectSQLiteUpdateIgnore

namespace SQLeanite.Tests
open SQLeanite

def expectSQLiteJoinProjectionWrappers : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY);INSERT INTO l VALUES(1,'Z'),(2,'a'),(3,'A'),(4,'a ');INSERT INTO r VALUES(1);"
  let cases : List (String × List String) := [
    ("SELECT DISTINCT a.k COLLATE nocase FROM l a,r b ORDER BY 1;", ["a","a ","Z"]),
    ("SELECT DISTINCT likely(a.k COLLATE nocase) AS x FROM l a,r b ORDER BY x;", ["a","a ","Z"]),
    ("SELECT DISTINCT +a.k COLLATE rtrim FROM l a,r b ORDER BY 1;", ["A","Z","a"]),
    ("SELECT a.k COLLATE nocase AS x FROM l a,r b ORDER BY x COLLATE binary;", ["A","Z","a","a "]),
    ("SELECT +a.k FROM l a,r b ORDER BY likely(a.k);", ["A","Z","a","a "]),
    ("SELECT a.k COLLATE missing FROM l a,r b ORDER BY a.id;", ["Z","a","A","a "]),
    ("SELECT a.k COLLATE nocase FROM l a,r b UNION SELECT 'A' ORDER BY 1;", ["A","a ","Z"]),
    ("SELECT likely(a.k) FROM l a,r b UNION SELECT 'A' COLLATE nocase ORDER BY 1;", ["A","a ","Z"]),
    ("SELECT +a.k FROM l a,r b UNION SELECT 'A' COLLATE nocase ORDER BY 1;", ["A","Z","a","a "])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"joined projection wrapper: {sql}: {message}"
    let expected ← match values.mapM (fun value => do return [← SQLSurface.value (.text value)]) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"joined projection wrapper values: {sql}"
  for sql in ["SELECT DISTINCT a.k COLLATE missing FROM l a,r b LIMIT 0;",
      "SELECT a.k COLLATE missing FROM l a,r b ORDER BY 1 LIMIT 0;",
      "SELECT likely(a.k) FROM l a,r b ORDER BY 0;",
      "SELECT likelihood(a.k,2.0) FROM l a,r b LIMIT 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"joined projection wrapper omitted required validation: {sql}"

def expectSQLiteJoinComparisonWrappers : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k TEXT);CREATE TABLE r(id INTEGER PRIMARY KEY,k TEXT);INSERT INTO l VALUES(1,'A'),(2,'a '),(3,NULL);INSERT INTO r VALUES(1,'a'),(2,'A '),(3,NULL);"
  for (condition, values) in [
      ("a.k COLLATE nocase=b.k", [[1,1],[2,2]]),
      ("a.k COLLATE rtrim=b.k", [[1,2],[2,1]]),
      ("a.k COLLATE nocase IS b.k", [[1,1],[2,2],[3,3]]),
      ("a.k COLLATE nocase<b.k", [[1,2]]),
      ("a.k COLLATE rtrim>=b.k", [[1,2],[2,1],[2,2]])] do
    let sql := s!"SELECT a.id,b.id FROM l a JOIN r b ON {condition} ORDER BY a.id,b.id;"
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail message
    let expected ← match values.mapM (List.mapM (fun number : Int => SQLSurface.value (.integer number))) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"joined comparison collation: {sql}"
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k TEXT,true INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY);INSERT INTO l VALUES(1,'2',2),(2,'01',1),(3,'1tail',1);INSERT INTO r VALUES(1);"
  for (condition, values) in [("k IS true",[1,2]),("k IS +true",[1]),("k IS likely(true)",[1])] do
    let sql := s!"SELECT a.id FROM l a,r b WHERE {condition} ORDER BY a.id;"
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail message
    let expected ← match values.mapM (fun number : Int => do return [← SQLSurface.value (.integer number)]) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"joined expression affinity: {sql}"
  let (_, output) ← match CoreSQL.execute Core.State.empty
      "SELECT 2 IS true COLLATE missing,NULL IS true COLLATE missing,'1tail' IS true COLLATE nocase;" with
    | .ok result => pure result
    | .error message => fail message
  let expected ← match ([1,0,1] : List Int).mapM (fun number => SQLSurface.value (.integer number)) with
    | .ok values => pure values
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some [expected] do fail "collated IS truth shortcut differs"
  for sql in ["SELECT a.id FROM l a,r b WHERE a.k COLLATE missing=b.id LIMIT 0;",
      "SELECT a.id FROM l a,r b WHERE a.k IS true COLLATE missing;",
      "SELECT a.id FROM l a,r b WHERE a.k IS likelihood(true,2.0);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"joined comparison wrapper ignored required validation: {sql}"

def expectSQLiteJoinIs : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,NULL),(2,0),(3,1),(4,2),(5,'1tail'),(6,'x');INSERT INTO r VALUES(1,NULL),(2,1),(3,0),(4,2);"
  let cases : List (String × List (List Value)) := [
    ("SELECT a.id,b.id FROM l a JOIN r b ON a.k IS b.k ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1],[.integer 2,.integer 3],[.integer 3,.integer 2],[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE a.k IS TRUE ORDER BY a.id;",
      [[.integer 3,.integer 3],[.integer 4,.integer 4],[.integer 5,.null]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE a.k IS FALSE ORDER BY a.id;",
      [[.integer 2,.integer 2],[.integer 6,.null]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE a.k IS NOT TRUE ORDER BY a.id;",
      [[.integer 1,.integer 1],[.integer 2,.integer 2],[.integer 6,.null]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE a.k IS NOT DISTINCT FROM b.k ORDER BY a.id;",
      [[.integer 1,.integer 1],[.integer 4,.integer 4]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE a.k IS +true ORDER BY a.id;",
      [[.integer 3,.integer 3]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"joined IS comparison: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"joined IS rows: {sql}"
  let (_, output) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE l(id INTEGER PRIMARY KEY,k,true);CREATE TABLE r(id INTEGER PRIMARY KEY);INSERT INTO l VALUES(1,2,1),(2,NULL,NULL);INSERT INTO r VALUES(1);SELECT a.id FROM l a,r b WHERE a.k IS true ORDER BY a.id;" with
    | .ok result => pure result
    | .error message => fail message
  let two ← match SQLSurface.value (.integer 2) with
    | .ok result => pure result
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some [[two]] do
    fail "IS truth keyword ignored declared source-column shadowing"

def expectSQLiteJoinTruth : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,NULL),(2,0),(3,2),(4,0.5),(5,'1tail'),(6,X'302E35FF'),(7,'x');INSERT INTO r VALUES(1,NULL),(2,1);"
  let cases : List (String × List (List Value)) := [
    ("SELECT a.id,b.id FROM l a JOIN r b ON a.k ORDER BY a.id,b.id;",
      [[.integer 3,.integer 1],[.integer 3,.integer 2],[.integer 4,.integer 1],[.integer 4,.integer 2],
       [.integer 5,.integer 1],[.integer 5,.integer 2],[.integer 6,.integer 1],[.integer 6,.integer 2]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE a.k ORDER BY a.id;",
      [[.integer 3,.null],[.integer 4,.null],[.integer 5,.null],[.integer 6,.null]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE NOT a.k ORDER BY a.id;",
      [[.integer 2,.integer 2],[.integer 7,.null]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE b.k ORDER BY a.id;",
      [[.integer 2,.integer 2]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON NULL ORDER BY a.id LIMIT 2;",
      [[.integer 1,.null],[.integer 2,.null]]),
    ("SELECT a.id,b.id FROM l a,r b WHERE 0 AND missing ORDER BY a.id,b.id;",[]),
    ("SELECT a.id,b.id FROM l a,r b WHERE NULL ORDER BY a.id,b.id;",[])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"join truth: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"join truth rows: {sql}"
  for sql in ["SELECT a.id FROM l a,r b WHERE 1 OR missing;",
      "SELECT a.id FROM l a,r b WHERE false AND missing;",
      "SELECT a.id FROM l a,r b WHERE 0 AND not_a_function();"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"join truth preparation erased a required name/function error: {sql}"
  let (_, output) ← match CoreSQL.execute Core.State.empty
      "CREATE TABLE l(id INTEGER PRIMARY KEY,true);CREATE TABLE r(id INTEGER PRIMARY KEY);INSERT INTO l VALUES(1,2),(2,0);INSERT INTO r VALUES(1);SELECT a.id,b.id FROM l a,r b WHERE true ORDER BY a.id,b.id;" with
    | .ok result => pure result
    | .error message => fail message
  let one ← match SQLSurface.value (.integer 1) with
    | .ok result => pure result
    | .error message => fail message
  unless (output.getLast?).map (·.rows) == some [[one,one]] do
    fail "bare Boolean-name truth conversion lost source-column shadowing"

def expectSQLiteJoinLookupScan : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,rowid NUMERIC);INSERT INTO l VALUES(1,'a'),(2,'b');INSERT INTO r VALUES(1,2),(2,1),(3,NULL),(4,1);"
  for (source, tail, expected) in [
      ("l a,r b", "", [[2,2,1],[1,1,2],[1,1,4]]),
      ("l a,r b", " LIMIT 2", [[2,2,1],[1,1,2]]),
      ("l a,r b", " ORDER BY a.id DESC", [[2,2,1],[1,1,2],[1,1,4]]),
      ("l a,r b", " ORDER BY b.id DESC,a.k", [[1,1,4],[1,1,2],[2,2,1]]),
      ("l a CROSS JOIN r b", "", [[1,1,2],[1,1,4],[2,2,1]])] do
    let sql := s!"SELECT rowid,a.id,b.id FROM {source} WHERE rowid=a.id{tail};"
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"join rowid lookup scan: {message}"
    let expected ← match expected.mapM (List.mapM (fun number : Int => SQLSurface.value (.integer number))) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"join rowid lookup traversal differs: {sql}"

def expectSQLiteJoinRowidNames : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,rowid TEXT);CREATE TABLE r(id INTEGER PRIMARY KEY,v);INSERT INTO l VALUES(1,'declared'),(2,NULL);INSERT INTO r VALUES(1,'a'),(3,'b');"
  let cases : List (String × List (List Value)) := [
    ("SELECT rowid,a.id,b.id FROM l a,r b ORDER BY a.id,b.id;",
      [[.text "declared",.integer 1,.integer 1],[.text "declared",.integer 1,.integer 3],
       [.null,.integer 2,.integer 1],[.null,.integer 2,.integer 3]]),
    ("SELECT rowid,a.rowid,b.rowid FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.id;",
      [[.text "declared",.text "declared",.integer 1],[.null,.null,.null]]),
    ("SELECT rowid,a.id,b.id FROM r a LEFT JOIN l b ON a.id=b.id ORDER BY a.id;",
      [[.text "declared",.integer 1,.integer 1],[.null,.integer 3,.null]]),
    ("SELECT a.id,b.id FROM l a,r b WHERE rowid='declared' ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1],[.integer 1,.integer 3]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"joined rowid name binding: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"joined rowid rows: {sql}"
  for sql in ["SELECT oid FROM l a,r b;", "SELECT * FROM l a JOIN r b USING(rowid);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"invalid joined rowid name accepted: {sql}"
  let (created, _) ← match CoreSQL.execute Core.State.empty (setup ++
      "CREATE TABLE made AS SELECT rowid FROM l a,r b ORDER BY a.id,b.id;") with
    | .ok result => pure result
    | .error message => fail message
  let some table := created.database.findTable? "made" | fail "joined rowid CTAS missing"
  unless table.schema.catalogColumns.map (·.name) == ["rowid"] &&
      table.schema.catalogColumns.map (·.affinity) == [.text] && table.rows.length == 4 do
    fail "joined rowid CTAS lost declared-column metadata"

def expectSQLiteColumnVisibility : IO Unit := do
  let setup := "CREATE TABLE n(v);INSERT INTO n VALUES('a'),('b');CREATE TABLE t(k TEXT PRIMARY KEY,v);INSERT INTO t VALUES('x','c');CREATE TABLE s(rowid,oid,_rowid_);INSERT INTO s VALUES(31,41,51);CREATE TABLE named(id INTEGER PRIMARY KEY,__sqleanite_rowid TEXT);INSERT INTO named VALUES(8,'declared');"
  let invalid := [
    "SELECT __sqleanite_rowid FROM n;",
    "SELECT n.__sqleanite_rowid FROM n;",
    "SELECT __sqleanite_rowid FROM t;",
    "SELECT v FROM n ORDER BY __sqleanite_rowid;",
    "SELECT sum(__sqleanite_rowid) FROM n;",
    "SELECT count(*) FROM n WHERE __sqleanite_rowid=1;",
    "SELECT v FROM n GROUP BY __sqleanite_rowid;",
    "SELECT a.__sqleanite_rowid,b.k FROM n a,t b LIMIT 0;",
    "UPDATE n SET v='wrong' WHERE __sqleanite_rowid=1;",
    "UPDATE n SET __sqleanite_rowid=9;",
    "DELETE FROM n WHERE __sqleanite_rowid=1;",
    "INSERT INTO n(__sqleanite_rowid,v) VALUES(9,'wrong');",
    "CREATE INDEX bad ON n(__sqleanite_rowid);",
    "CREATE INDEX bad ON n(rowid);"]
  for sql in invalid do
    for empty in ["", "DELETE FROM n;DELETE FROM t;"] do
      if (CoreSQL.execute Core.State.empty (setup ++ empty ++ sql)).isOk then
        fail s!"internal column name escaped into SQL: {sql}"
  let cases : List (String × List (List Value)) := [
    ("SELECT rowid,oid,_rowid_,v FROM n ORDER BY rowid;",
      [[.integer 1,.integer 1,.integer 1,.text "a"],[.integer 2,.integer 2,.integer 2,.text "b"]]),
    ("SELECT rowid AS __sqleanite_rowid,v FROM n ORDER BY __sqleanite_rowid DESC;",
      [[.integer 2,.text "b"],[.integer 1,.text "a"]]),
    ("SELECT a.rowid AS __sqleanite_rowid,b.k FROM n a,t b ORDER BY __sqleanite_rowid;",
      [[.integer 1,.text "x"],[.integer 2,.text "x"]]),
    ("UPDATE n SET rowid=8 WHERE oid=1;SELECT rowid,v FROM n ORDER BY rowid;",
      [[.integer 2,.text "b"],[.integer 8,.text "a"]]),
    ("SELECT rowid,oid,_rowid_ FROM s;",[[.integer 31,.integer 41,.integer 51]]),
    ("SELECT __sqleanite_rowid,rowid FROM named;",[[.text "declared",.integer 8]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"visible column lookup: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"visible column rows: {sql}"

def expectSQLiteJoinAtoms : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k TEXT,true INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k TEXT,false INTEGER);INSERT INTO l VALUES(1,'a',1),(2,'b',0),(3,NULL,NULL);INSERT INTO r VALUES(1,'A',0),(2,'B',1);"
  let cases : List (String × List (List Value)) := [
    ("SELECT DISTINCT 1,NULL,'x',X'80FF',1.5,-1,~1,NOT NULL FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY 1;",
      [[.integer 1,.null,.text "x",.blob #[128,255],.real 1.5,.integer (-1),.integer (-2),.null]]),
    ("SELECT true,false FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.id;",
      [[.integer 1,.integer 0],[.integer 0,.integer 1],[.null,.null]]),
    ("SELECT \"true\",\"false\" FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.id;",
      [[.integer 1,.integer 0],[.integer 0,.integer 1],[.null,.null]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE true=1 ORDER BY a.id;",
      [[.integer 1,.integer 1]]),
    ("SELECT a.id,b.id FROM l a NATURAL LEFT JOIN r b WHERE true=1 ORDER BY a.id;",
      [[.integer 1,.null]]),
    ("SELECT \"k\",true,false FROM l a NATURAL LEFT JOIN r b ORDER BY a.id;",
      [[.text "a",.integer 1,.null],[.text "b",.integer 0,.null],[.null,.null,.null]]),
    ("SELECT 1 AS z,a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY z DESC,a.id;",
      [[.integer 1,.integer 1,.integer 1],[.integer 1,.integer 2,.integer 2],[.integer 1,.integer 3,.null]]),
    ("SELECT DISTINCT 1 FROM l a,r b ORDER BY 1 LIMIT 1 OFFSET 1;",[])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"join atoms: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"join atom rows: {sql}"
  for sql in ["SELECT \"k\" FROM l a,r b;", "SELECT \"missing\" FROM l a,r b LIMIT 0;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"invalid quoted join name accepted: {sql}"
  let (created, _) ← match CoreSQL.execute Core.State.empty (setup ++
      "CREATE TABLE made AS SELECT DISTINCT 1 AS x,'one' AS y,X'80FF' AS z FROM l a,r b ORDER BY 1;") with
    | .ok result => pure result
    | .error message => fail message
  let some table := created.database.findTable? "made" | fail "join atom CTAS missing"
  unless table.rows.length == 1 && table.schema.visibleColumns.map (·.name) == ["x","y","z"] do
    fail "join atom CTAS metadata or DISTINCT rows differ"

def expectSQLiteJoinSort : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,NULL),(2,'A'),(3,'a '),(4,'a');INSERT INTO r VALUES(1,'a'),(2,NULL),(3,'B');"
  let cases : List (String × List (List Value)) := [
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.k COLLATE nocase ASC NULLS LAST,a.id;",
      [[.integer 2,.integer 2],[.integer 4,.null],[.integer 3,.integer 3],[.integer 1,.integer 1]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.k COLLATE rtrim ASC NULLS FIRST,a.id;",
      [[.integer 1,.integer 1],[.integer 2,.integer 2],[.integer 3,.integer 3],[.integer 4,.null]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.k COLLATE nocase DESC NULLS FIRST,a.id;",
      [[.integer 1,.integer 1],[.integer 3,.integer 3],[.integer 2,.integer 2],[.integer 4,.null]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY b.k DESC NULLS FIRST,a.id;",
      [[.integer 2,.integer 2],[.integer 4,.null],[.integer 1,.integer 1],[.integer 3,.integer 3]]),
    ("SELECT a.id AS seq,b.k AS z FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY z COLLATE nocase ASC NULLS LAST,seq;",
      [[.integer 1,.text "a"],[.integer 3,.text "B"],[.integer 2,.null],[.integer 4,.null]]),
    ("SELECT a.id,a.k FROM l a JOIN r b ON a.id=b.id ORDER BY 2 COLLATE nocase DESC NULLS LAST,1;",
      [[.integer 3,.text "a "],[.integer 2,.text "A"],[.integer 1,.null]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"join NULL/collation sort: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"join NULL/collation ordering rows: {sql}"
  for term in ["a.k", "NULL", "true", "1"] do
    if (CoreSQL.execute Core.State.empty
        (setup ++ s!"SELECT a.id FROM l a,r b ORDER BY {term} COLLATE missing LIMIT 0;")).isOk then
      fail "join ordering dropped an unknown collation"
  let parsed ← match CoreTokenGrammar.parseCertified
      "SELECT a.id FROM l a,r b ORDER BY a.k COLLATE nocase NULLS LAST;" with
    | .ok result => pure result
    | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "join sort AST missing"
  let some term := query.orderBy[0]? | fail "join order term missing"
  if (CoreTokenGrammar.check parsed.tokens #[.select { query with
      orderBy := query.orderBy.set! 0 { term with nullsFirst := some true } }]).isOk then
    fail "join token replay accepted changed NULL placement"

def expectSQLiteJoinOrder : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,'b'),(2,'a');INSERT INTO r VALUES(1,'c'),(2,'d');"
  let cases : List (String × List (List Value)) := [
    ("SELECT b.id AS id,a.id FROM l a CROSS JOIN r b ORDER BY id,a.id;",
      [[.integer 1,.integer 1],[.integer 1,.integer 2],[.integer 2,.integer 1],[.integer 2,.integer 2]]),
    ("SELECT b.id,a.id FROM l a CROSS JOIN r b ORDER BY 1 DESC,+2;",
      [[.integer 2,.integer 1],[.integer 2,.integer 2],[.integer 1,.integer 1],[.integer 1,.integer 2]]),
    ("SELECT a.*,b.* FROM l a CROSS JOIN r b ORDER BY id DESC,b.id;",
      [[.integer 2,.text "a",.integer 1,.text "c"],[.integer 2,.text "a",.integer 2,.text "d"],
       [.integer 1,.text "b",.integer 1,.text "c"],[.integer 1,.text "b",.integer 2,.text "d"]]),
    ("SELECT * FROM l a JOIN r b USING(id) ORDER BY 3 DESC;",
      [[.integer 2,.text "a",.text "d"],[.integer 1,.text "b",.text "c"]]),
    ("SELECT a.id AS z,b.id AS z FROM l a CROSS JOIN r b ORDER BY \"z\" DESC,b.id;",
      [[.integer 2,.integer 1],[.integer 2,.integer 2],[.integer 1,.integer 1],[.integer 1,.integer 2]]),
    ("SELECT a.id AS \"true\",b.id FROM l a JOIN r b USING(id) ORDER BY true DESC;",
      [[.integer 2,.integer 2],[.integer 1,.integer 1]]),
    ("SELECT a.id,b.id FROM l a JOIN r b USING(id) ORDER BY 2147483648,1.0,NULL,'x',true,a.id;",
      [[.integer 1,.integer 1],[.integer 2,.integer 2]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"join ORDER BY: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"join ORDER BY rows: {sql}"
  for sql in ["SELECT a.id,b.id FROM l a,r b ORDER BY id;",
      "SELECT a.id FROM l a,r b ORDER BY 0 LIMIT 0;",
      "SELECT a.id FROM l a,r b ORDER BY -1;",
      "SELECT a.* AS z FROM l a,r b;", "SELECT * z FROM l a,r b;",
      "CREATE TABLE IF NOT EXISTS l AS SELECT * AS z FROM l a,r b;"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"invalid join ORDER BY/star alias accepted: {sql}"
  let parsed ← match CoreTokenGrammar.parseCertified "SELECT a.* FROM l a,r b;" with
    | .ok result => pure result
    | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "star AST missing"
  let some column := query.columns[0]? | fail "star result missing"
  let tokens ← match lex "SELECT a.* AS z FROM l a,r b;" with
    | .ok result => pure result
    | .error message => fail message
  if (CoreTokenGrammar.check tokens #[.select { query with
      columns := query.columns.set! 0 { column with alias := some "z" } }]).isOk then
    fail "independent replay admitted an aliased result star"

def expectSQLiteJoinWindow : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);INSERT INTO l VALUES(1,1),(2,1.0),(3,'1'),(4,NULL),(5,NULL);INSERT INTO r VALUES(1,1),(2,1.0),(3,NULL);"
  let cases : List (String × List (List Value)) := [
    ("SELECT DISTINCT a.k FROM l a CROSS JOIN r b ORDER BY a.id,b.id;",
      [[.integer 1],[.text "1"],[.null]]),
    ("SELECT DISTINCT a.k FROM l a CROSS JOIN r b ORDER BY a.id DESC,b.id DESC;",
      [[.null],[.text "1"],[.real 1.0]]),
    ("SELECT DISTINCT a.k,b.k FROM l a CROSS JOIN r b WHERE a.id<3 ORDER BY a.id DESC,b.id;",
      [[.real 1.0,.integer 1],[.real 1.0,.null]]),
    ("SELECT DISTINCT a.k FROM l a JOIN r b USING(id) ORDER BY b.id DESC,a.id DESC;",
      [[.text "1"],[.real 1.0]]),
    ("SELECT DISTINCT a.k FROM l a CROSS JOIN r b ORDER BY b.id DESC,a.id DESC;",
      [[.null],[.text "1"],[.integer 1]]),
    ("SELECT DISTINCT b.k FROM l a JOIN r b ORDER BY b.id DESC,a.k DESC,a.id LIMIT 1 OFFSET 1;",
      [[.integer 1]]),
    ("SELECT DISTINCT b.k FROM l a JOIN r b ON a.id=b.id ORDER BY b.id DESC,a.k DESC,a.id LIMIT 1 OFFSET 1;",
      [[.real 1.0]]),
    ("SELECT DISTINCT a.k FROM l a CROSS JOIN r b ORDER BY a.id,b.id LIMIT -1 OFFSET 1;",
      [[.text "1"],[.null]]),
    ("SELECT DISTINCT a.k,b.k FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.id,b.id LIMIT 1,2;",
      [[.text "1",.null],[.null,.null]]),
    ("SELECT DISTINCT a.k FROM l a JOIN r b ON a.id=b.id ORDER BY a.id LIMIT 1 OFFSET 1;",
      [[.text "1"]]),
    ("SELECT a.id,b.id FROM l a LEFT JOIN r b USING(id) ORDER BY a.id,b.id LIMIT 2 OFFSET 3;",
      [[.integer 4,.null],[.integer 5,.null]]),
    ("SELECT DISTINCT k FROM l a NATURAL LEFT JOIN r b ORDER BY a.id,b.id LIMIT 2 OFFSET 1;",
      [[.text "1"],[.null]]),
    ("SELECT DISTINCT a.k FROM l a CROSS JOIN r b ORDER BY a.id,b.id LIMIT 0 OFFSET 1.5;",[]),
    ("SELECT a.k FROM l a CROSS JOIN r b ORDER BY a.id,b.id LIMIT 2 OFFSET 999999999999;",[])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"join DISTINCT/window: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do
      fail s!"join DISTINCT/window rows: {sql}"
  let (created, _) ← match CoreSQL.execute Core.State.empty (setup ++
      "CREATE TABLE made AS SELECT DISTINCT a.k FROM l a CROSS JOIN r b ORDER BY a.id,b.id LIMIT -1 OFFSET 1;") with
    | .ok result => pure result
    | .error message => fail message
  let some table := created.database.findTable? "made" | fail "join window CTAS missing"
  unless table.rows.length == 2 do fail "join window CTAS lost DISTINCT/OFFSET"

def expectSQLiteJoinUsing : IO Unit := do
  let setup := "CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER,lv TEXT);CREATE TABLE r(id INTEGER PRIMARY KEY,k TEXT,rv TEXT);CREATE TABLE n(other_id INTEGER PRIMARY KEY,z);INSERT INTO l VALUES(1,1,'l1'),(2,2,'l2'),(3,NULL,'l3');INSERT INTO r VALUES(1,'01','r1'),(4,'2','r4'),(3,NULL,'r3');INSERT INTO n VALUES(9,'z');"
  let cases : List (String × List (List Value)) := [
    ("SELECT a.id,k,b.id FROM l a JOIN r b USING(k) ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1,.integer 1],[.integer 2,.integer 2,.integer 4]]),
    ("SELECT a.id,k,b.id FROM l a, r b USING('K') ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1,.integer 1],[.integer 2,.integer 2,.integer 4]]),
    ("SELECT * FROM l a NATURAL JOIN r b ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1,.text "l1",.text "r1"]]),
    ("SELECT * FROM l a LEFT NATURAL JOIN r b ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1,.text "l1",.text "r1"],
       [.integer 2,.integer 2,.text "l2",.null],[.integer 3,.null,.text "l3",.null]]),
    ("SELECT id,k FROM l a JOIN r b USING(k,id) ORDER BY a.id,b.id;",
      [[.integer 1,.integer 1]]),
    ("SELECT id FROM l a JOIN r b USING(id,id) ORDER BY a.id,b.id;",
      [[.integer 1],[.integer 3]]),
    ("SELECT a.id,b.other_id FROM l a NATURAL LEFT JOIN n b ORDER BY a.id,b.other_id;",
      [[.integer 1,.integer 9],[.integer 2,.integer 9],[.integer 3,.integer 9]])]
  for (sql, values) in cases do
    let (_, output) ← match CoreSQL.execute Core.State.empty (setup ++ sql) with
      | .ok result => pure result
      | .error message => fail s!"USING/NATURAL join: {message}"
    let expected ← match values.mapM (List.mapM SQLSurface.value) with
      | .ok rows => pure rows
      | .error message => fail message
    unless (output.getLast?).map (·.rows) == some expected do fail s!"USING/NATURAL rows: {sql}"
  for sql in ["SELECT * FROM l JOIN r USING(rowid);", "SELECT * FROM l JOIN r USING(lv);",
      "SELECT rowid FROM l JOIN r USING(id);", "SELECT id FROM l JOIN r USING(k);",
      "SELECT * FROM l NATURAL JOIN r ON l.id=r.id;", "SELECT * FROM l NATURAL JOIN r USING(k);"] do
    if (CoreSQL.execute Core.State.empty (setup ++ sql)).isOk then
      fail s!"invalid shared-column resolution accepted: {sql}"
  for suffix in ["NATURAL JOIN r ON l.id=r.id", "NATURAL JOIN r USING(k)", "JOIN r USING(missing)"] do
    unless (CoreSQL.execute Core.State.empty
        (setup ++ s!"CREATE TABLE IF NOT EXISTS l AS SELECT * FROM l {suffix};")).isOk do
      fail "CTAS schema no-op did not defer join semantic errors"
  if (CoreSQL.execute Core.State.empty
      (setup ++ "CREATE TABLE IF NOT EXISTS l AS SELECT * FROM l JOIN r ON l.id=r.id USING(id);")).isOk then
    fail "CTAS schema no-op hid invalid ON/USING syntax"
  let (created, _) ← match CoreSQL.execute Core.State.empty
      (setup ++ "CREATE TABLE made AS SELECT * FROM l NATURAL LEFT JOIN r ORDER BY l.id,r.id;") with
    | .ok result => pure result
    | .error message => fail message
  let some table := created.database.findTable? "made" | fail "USING CTAS table missing"
  unless table.schema.visibleColumns.map (·.name) == ["id","k","lv","rv"] && table.rows.length == 3 do
    fail "USING CTAS did not preserve the merged projection"
  let sql := "SELECT a.id FROM l a JOIN r b USING(k);"
  let parsed : CoreTokenGrammar.CertifiedParse sql ← match CoreTokenGrammar.parseCertified sql with
    | .ok result => pure result
    | .error message => fail message
  let some (Statement.select query) := parsed.statements[0]? | fail "USING AST missing"
  let some right := query.sources[1]? | fail "USING right source missing"
  for forged in [{ right with usingColumns := #["id"] }, { right with usingColumns := #[] },
      { right with naturalJoin := true }] do
    if (CoreTokenGrammar.check parsed.tokens
        #[.select { query with sources := query.sources.set! 1 forged }]).isOk then
      fail "USING token replay accepted changed shared columns or join type"

end SQLeanite.Tests
