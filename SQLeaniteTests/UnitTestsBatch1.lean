import SQLeaniteTests.UnitTestsBatch0

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def unitTestsBatch1 : Array (String × IO Unit) := #[
  ("distinct limit", expectSQL "distinct limit" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(1),(2),(3);
    SELECT DISTINCT x FROM t ORDER BY x LIMIT 2 OFFSET 1;"
    #[#[.integer 2], #[.integer 3]]),
  ("distinct expression collation", expectSQL "distinct expression collation" "
    CREATE TABLE t(x); INSERT INTO t VALUES('b'),('B');
    SELECT DISTINCT x COLLATE nocase FROM t;"
    #[#[.text "b"]]),
  ("rtrim compound collation", expectSQL "rtrim compound collation" "
    CREATE TABLE t(x COLLATE rtrim); INSERT INTO t VALUES(''),(' '),('  ');
    SELECT x FROM t UNION SELECT 1;"
    #[#[.integer 1], #[.text ""]]),
  ("distinct aggregates", expectSQL "distinct aggregates" "
    CREATE TABLE t(x COLLATE nocase, n); INSERT INTO t VALUES('A',1),('a',1),(NULL,2),('B',2);
    SELECT count(DISTINCT x), sum(DISTINCT n), count(ALL n) FROM t;"
    #[#[.integer 2, .integer 3, .integer 4]]),
  ("distinct aggregate arity", expectError "distinct aggregate arity" "
    CREATE TABLE t(x,y); SELECT string_agg(DISTINCT x,y) FROM t;"
    "DISTINCT aggregates must have exactly one argument"),
  ("unique expression index", expectError "unique expression index" "
    CREATE TABLE t(a,b); CREATE UNIQUE INDEX tx ON t(a+b);
    INSERT INTO t VALUES(0,1),(1,0);"
    "UNIQUE constraint failed: index 'tx'"),
  ("index expression safety", expectError "index expression safety" "
    CREATE TABLE t(a); CREATE INDEX tx ON t(a+random());"
    "non-deterministic functions prohibited in index expressions"),
  ("index subquery safety", expectError "index subquery safety" "
    CREATE TABLE t(a); CREATE INDEX tx ON t(a+(SELECT 1));"
    "subqueries prohibited in index expressions"),
  ("where result alias", expectSQL "where result alias" "
    CREATE TABLE t(a); INSERT INTO t VALUES('abc001xyz'),('abc002xyz');
    SELECT substr(a,4,3) AS k FROM t WHERE k=printf('%03d',2);"
    #[#[.text "002"]]),
  ("delete returning", expectSQL "delete returning" "
    CREATE TABLE t(a,b); CREATE INDEX ignored ON t(a); INSERT INTO t VALUES(1,'x'),(2,'y');
    DELETE FROM t INDEXED BY ignored WHERE a=1 RETURNING *;"
    #[#[.integer 1, .text "x"]]),
  ("json expression", expectSQL "json expression" "
    CREATE TABLE t(y); INSERT INTO t VALUES('{b:5}');
    SELECT json_insert('{}','$.a',json(y))->>'$.a.b' FROM t;"
    #[#[.integer 5]]),
  ("forward inner join on scope", expectSQL "forward inner join on scope" "
    CREATE TABLE t(x); INSERT INTO t VALUES(0),(1);
    SELECT count(*) FROM t AS a JOIN t AS b ON d.x=a.x JOIN t AS d ON d.x=a.x;"
    #[#[.integer 4]]),
  ("correlated aggregate lift", expectSQL "correlated aggregate lift" "
    CREATE TABLE jjj(x); CREATE TABLE nnn(x);
    SELECT (SELECT 'mmm' UNION SELECT DISTINCT max(name) ORDER BY 1)
      FROM sqlite_master;"
    #[#[.text "mmm"]]),
  ("drop index if exists", expectSQL "drop index if exists" "
    CREATE TABLE t(x); DROP INDEX IF EXISTS absent; SELECT count(*) FROM t;"
    #[#[.integer 0]]),
  ("compound derived table", expectSQL "compound derived table" "
    CREATE TABLE a(x); CREATE TABLE b(x); INSERT INTO a VALUES(1); INSERT INTO b VALUES(3);
    SELECT z.x FROM (SELECT x FROM a UNION SELECT x FROM b) AS z ORDER BY z.x;"
    #[#[.integer 1], #[.integer 3]]),
  ("compound global order limit", expectSQL "compound global order limit" "
    SELECT 1 AS x UNION SELECT 3 ORDER BY x DESC LIMIT 1;"
    #[#[.integer 3]]),
  ("compound reverse collation", expectSQL "compound reverse collation" "
    SELECT 'a' AS x UNION ALL SELECT 'z' ORDER BY 1 COLLATE reverse;"
    #[#[.text "z"], #[.text "a"]]),
  ("compound inherited collation", expectSQL "compound inherited collation" "
    CREATE TABLE a(x COLLATE nocase); CREATE TABLE b(x COLLATE nocase);
    INSERT INTO a VALUES('ABC'); INSERT INTO b VALUES('abc');
    SELECT x FROM a INTERSECT SELECT x FROM b;"
    #[#[.text "ABC"]]),
  ("compound expression collation", expectSQL "compound expression collation" "
    CREATE TABLE a(x); CREATE TABLE b(x);
    INSERT INTO a VALUES('ABC'); INSERT INTO b VALUES('abc');
    SELECT x COLLATE nocase FROM a EXCEPT SELECT x FROM b;" #[]),
  ("compound order validation", expectError "compound order validation"
    "SELECT 1 AS x UNION SELECT 3 ORDER BY x+1;" "does not match any column"),
  ("correlated inner scope", expectSQL "correlated inner scope" "
    CREATE TABLE t(a,b); INSERT INTO t VALUES('outer','1'),('inner','2');
    SELECT a FROM t AS o WHERE b IN (SELECT b FROM t WHERE a='inner');"
    #[#[.text "inner"]]),
  ("subquery arity", expectError "subquery arity" "
    SELECT 1 IN (SELECT 1,2);" "sub-select returns 2 columns - expected 1"),
  ("double-quoted string mode", expectError "double-quoted string mode" "
    PRAGMA lean_dqs_dml=0; SELECT \"missing\";" "should this be a string literal"),
  ("values query", expectSQL "values query" "VALUES(1,'a'),(2,'b');"
    #[#[.integer 1, .text "a"], #[.integer 2, .text "b"]]),
  ("values compound", expectSQL "values compound" "
    VALUES(1),(2),(3) EXCEPT VALUES(2);"
    #[#[.integer 1], #[.integer 3]]),
  ("compound clause placement", expectError "compound clause placement" "
    SELECT 1 ORDER BY 1 UNION ALL SELECT 2;" "ORDER BY clause should come after UNION ALL"),
  ("live view", expectSQL "live view" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1); CREATE VIEW v(y) AS SELECT x+1 FROM t;
    INSERT INTO t VALUES(4); SELECT y FROM v ORDER BY y;"
    #[#[.integer 2], #[.integer 5]]),
  ("view with cte", expectSQL "view with cte" "
    CREATE VIEW v(x) AS WITH c(y) AS (SELECT 123)
      SELECT (SELECT min(y) OVER()) FROM c GROUP BY y;
    SELECT * FROM v;" #[#[.integer 123]]),
  ("view rollback", expectError "view rollback" "
    BEGIN; CREATE VIEW v AS SELECT 1 AS x; ROLLBACK; SELECT * FROM v;" "no such table"),
  ("grouped aggregates", expectSQL "grouped aggregates" "
    CREATE TABLE t(k,v); INSERT INTO t VALUES('a',1),('a',2),('b',4);
    SELECT k,sum(v) AS total FROM t GROUP BY k HAVING total>2 ORDER BY total;"
    #[#[.text "a", .integer 3], #[.text "b", .integer 4]]),
  ("derived aggregate having", expectSQL "derived aggregate having" "
    CREATE TABLE t(k,v); INSERT INTO t VALUES(1,1),(2,2),(2,4);
    SELECT a,k FROM (SELECT avg(v) AS a,k FROM t GROUP BY k HAVING a>1) ORDER BY k;"
    #[#[.real 3.0, .integer 2]]),
  ("group and order aliases", expectSQL "group and order aliases" "
    CREATE TABLE t(k); INSERT INTO t VALUES(0),(0),(1);
    SELECT k+1 AS x,count(*) AS n FROM t GROUP BY x ORDER BY 10-(2*x+n);"
    #[#[.integer 2, .integer 1], #[.integer 1, .integer 2]]),
  ("aggregate where alias", expectSQL "aggregate where alias" "
    CREATE TABLE t(a,b,c); INSERT INTO t VALUES(1,'aa','bb'),(2,'cc','dd');
    SELECT a AS x,b||c AS y FROM t WHERE y='aabb' GROUP BY x,y;"
    #[#[.integer 1, .text "aabb"]]),
  ("group ordinal validation", expectError "group ordinal validation" "
    CREATE TABLE t(k); SELECT k,count(*) FROM t GROUP BY 0;" "GROUP BY term out of range"),
  ("three-part group name", expectError "three-part group name" "
    CREATE TABLE t(k); INSERT INTO t VALUES(1);
    SELECT k,count(*) FROM t GROUP BY temp.t.k;" "no such column: temp.t.k"),
  ("empty aggregate row", expectSQL "empty aggregate row" "
    CREATE TABLE t(a,b); SELECT a,sum(b) FROM t WHERE 0;"
    #[#[.null, .null]]),
  ("generated column recomputation", expectSQL "generated column recomputation" "
    CREATE TABLE t(a REAL,b REAL GENERATED ALWAYS AS (a+1));
    INSERT INTO t(a) VALUES(1); UPDATE t SET a=4;
    ALTER TABLE t ADD COLUMN c REAL AS (b+1); SELECT * FROM t;"
    #[#[.real 4.0, .real 5.0, .real 6.0]]),
  ("aggregate alias recursion", expectError "aggregate alias recursion" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1); SELECT min(x) AS m FROM t
    GROUP BY x HAVING max(m+1)>0;" "misuse of aliased aggregate m"),
  ("table constraint parser", expectSQL "table constraint parser" "
    CREATE TABLE t(a,b,c,PRIMARY KEY(a,b)); INSERT INTO t VALUES(1,2,3);
    INSERT INTO t SELECT a+(SELECT max(a) FROM t),b,c FROM t; SELECT count(*) FROM t;"
    #[#[.integer 2]]),
  ("syntax diagnostics", expectError "syntax diagnostics" "SELECT 1 WHERE 1=;"
    "near \";\": syntax error"),
  ("limit expression", expectSQL "limit expression" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(2),(3); SELECT x FROM t LIMIT 1+1;"
    #[#[.integer 1], #[.integer 2]]),
  ("foreign key cascade", expectSQL "foreign key cascade" "
    PRAGMA foreign_keys=ON;
    CREATE TABLE p(a,b UNIQUE); CREATE TABLE c(d REFERENCES p(b) ON DELETE CASCADE);
    CREATE TABLE log(x); CREATE TRIGGER cd AFTER DELETE ON c BEGIN INSERT INTO log VALUES(old.d); END;
    INSERT INTO p VALUES(1,7); INSERT INTO c VALUES(7); REPLACE INTO p VALUES(2,7);
    SELECT p.a,count(c.d),count(log.x) FROM p LEFT JOIN c ON c.d=p.b,log;"
    #[#[.integer 2, .integer 0, .integer 1]]),
  ("foreign key enforcement", expectError "foreign key enforcement" "
    PRAGMA foreign_keys=ON; CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(k REFERENCES p(k));
    INSERT INTO c VALUES(9);" "FOREIGN KEY constraint failed"),
  ("count changes", expectSQL "count changes" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(2),(3); PRAGMA count_changes=ON;
    DELETE FROM t WHERE x<3; DELETE FROM t;"
    #[#[.integer 2], #[.integer 1]]),
  ("delete trigger update", expectSQL "delete trigger update" "
    CREATE TABLE t(x); CREATE TABLE counter(n); INSERT INTO t VALUES(1),(2); INSERT INTO counter VALUES(0);
    CREATE TRIGGER td AFTER DELETE ON t BEGIN UPDATE counter SET n=n+1; END;
    DELETE FROM t; SELECT n FROM counter;"
    #[#[.integer 2]]),
  ("trigger outer diagnostic", expectError "trigger outer diagnostic" "
    CREATE TABLE source(a,b); INSERT INTO source VALUES(1,2); CREATE TABLE target(n);
    CREATE TRIGGER ti AFTER INSERT ON target BEGIN
      SELECT a FROM source WHERE a>new.missing UNION ALL SELECT b FROM source;
    END;
    INSERT INTO target VALUES(1);" "no such column: new.missing"),
  ("composite uniqueness", expectError "composite uniqueness" "
    CREATE TABLE t(a,b,c,UNIQUE(a,b)); INSERT INTO t VALUES(1,2,3),(1,2,4);"
    "UNIQUE constraint failed: t.a, t.b"),
  ("update preserves scan slot", expectSQL "update preserves scan slot" "
    CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,10),(2,20);
    UPDATE t SET v=11 WHERE id=1; SELECT * FROM t;"
    #[#[.integer 1, .integer 11], #[.integer 2, .integer 20]]),
  ("alter add column", expectSQL "alter add column" "
    CREATE TABLE t(x); INSERT INTO t VALUES(7); ALTER TABLE t ADD COLUMN y DEFAULT 3;
    SELECT x,y,printf('y%d',x) FROM t;"
    #[#[.integer 7, .integer 3, .text "y7"]]),
  ("like and glob", expectSQL "like and glob" "
    SELECT 'Alpha' LIKE 'a_ph%', 'abc' GLOB 'a*';"
    #[#[.integer 1, .integer 1]]),
  ("recursive cte insert", expectSQL "recursive cte insert" "
    CREATE TABLE t(x);
    WITH RECURSIVE n(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM n WHERE x<4)
      INSERT INTO t SELECT x FROM n;
    SELECT x FROM t ORDER BY x;"
    #[#[.integer 1], #[.integer 2], #[.integer 3], #[.integer 4]]),
  ("recursive select seed", expectSQL "recursive select seed" "
    WITH RECURSIVE n(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM n WHERE x<3)
      SELECT x FROM n ORDER BY x;"
    #[#[.integer 1], #[.integer 2], #[.integer 3]]),
  ("implicit recursive cte", expectSQL "implicit recursive cte" "
    CREATE TABLE t(x);
    WITH n(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM n WHERE x<3)
      INSERT INTO t SELECT x FROM n;
    SELECT x FROM t ORDER BY x;"
    #[#[.integer 1], #[.integer 2], #[.integer 3]]),
  ("row varying random", expectSQL "row varying random" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(2),(3),(4),(5);
    SELECT abs(random())%5 AS r FROM t GROUP BY 1 ORDER BY 1;"
    #[#[.integer 0], #[.integer 1], #[.integer 2], #[.integer 3], #[.integer 4]]),
  ("index schema catalog", expectSQL "index schema catalog" "
    CREATE TABLE t(x); CREATE INDEX tx ON t(x);
    SELECT name FROM sqlite_master WHERE type='index';"
    #[#[.text "tx"]]),
  ("empty window input", expectSQL "empty window input" "
    CREATE TABLE t(x); SELECT sum(x) OVER() FROM t;" #[]),
  ("rowid reuse after empty", expectSQL "rowid reuse after empty" "
    CREATE TABLE t(x); INSERT INTO t VALUES(1),(2); DELETE FROM t; INSERT INTO t VALUES(3);
    SELECT rowid FROM t;" #[#[.integer 1]]),
  ("integer cast numeric prefix", expectSQL "integer cast numeric prefix" "
    SELECT CAST('123abc' AS INTEGER), CAST('1.5' AS REAL)+1;"
    #[#[.integer 123, .real 2.5]]),
  ("IS truth predicates", expectSQL "IS truth predicates" "
    SELECT NULL IS TRUE,NULL IS NOT TRUE,2 IS TRUE,0 IS FALSE;"
    #[#[.integer 0, .integer 1, .integer 1, .integer 1]]),
  ("json extract", expectSQL "json extract" "
    SELECT json_extract('{\"a\":5}', '$.a'), printf('%s%d','x',4),
      json_extract('{outer:{answer:\"ok\"}}', '$.outer.answer');"
    #[#[.integer 5, .text "x4", .text "ok"]]),
  ("expression index scan order", expectSQL "expression index scan order" "
    CREATE TABLE t(b); INSERT INTO t VALUES('one'),('two'),('three');
    CREATE INDEX tx ON t(b||'x');
    SELECT b='two',b='three' FROM t WHERE b||'x'>'onex';"
    #[#[.integer 0, .integer 1], #[.integer 1, .integer 0]]),
  ("aggregate subquery order source", expectSQL "aggregate subquery order source" "
    CREATE TABLE t(c0); INSERT INTO t VALUES(1),(2);
    SELECT (SELECT count(*) FROM t ORDER BY c0);" #[#[.integer 2]]),
  ("automatic index catalog", expectSQL "automatic index catalog" "
    CREATE TABLE t(a UNIQUE PRIMARY KEY,b,UNIQUE(a,b));
    SELECT name,sql IS NULL FROM sqlite_master WHERE type='index' ORDER BY name;"
    #[#[.text "sqlite_autoindex_t_1", .integer 1],
      #[.text "sqlite_autoindex_t_2", .integer 1]]),
  ("automatic index cannot drop", expectError "automatic index cannot drop" "
    CREATE TABLE t(a UNIQUE); DROP INDEX sqlite_autoindex_t_1;"
    "index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped"),
  ("create index if not exists", expectSQL "create index if not exists" "
    CREATE TABLE t(a); CREATE INDEX IF NOT EXISTS i ON t(a);
    CREATE INDEX IF NOT EXISTS i ON t(a);
    SELECT count(*) FROM sqlite_master WHERE type='index' AND name='i';"
    #[#[.integer 1]]),
  ("composite index prefix order", expectSQL "composite index prefix order" "
    CREATE TABLE t(a,b,c); CREATE INDEX i ON t(a,b);
    INSERT INTO t VALUES('', '',1),('',NULL,2),(NULL,'',3);
    SELECT c FROM t WHERE a='';" #[#[.integer 2], #[.integer 1]]),
  ("reserved schema name", expectError "reserved schema name" "CREATE TABLE sqlite_private(x);"
    "object name reserved for internal use"),
  ("conflict rollback state", expectConflictRollback),
  ("not null conflict default", expectSQL "not null conflict default" "
    CREATE TABLE t(x NOT NULL ON CONFLICT REPLACE DEFAULT 5);
    INSERT INTO t VALUES(NULL); INSERT OR REPLACE INTO t VALUES(NULL);
    SELECT x FROM t;" #[#[.integer 5], #[.integer 5]]),
  ("explicit abort overrides constraint", expectError "explicit abort overrides constraint" "
    CREATE TABLE t(x NOT NULL ON CONFLICT REPLACE DEFAULT 5);
    INSERT OR ABORT INTO t VALUES(NULL);" "NOT NULL constraint failed: t.x"),
  ("check conflict ignore", expectSQL "check conflict ignore" "
    CREATE TABLE t(a CHECK(a!=2));
    INSERT OR IGNORE INTO t VALUES(1),(2),(3); SELECT a FROM t ORDER BY a;"
    #[#[.integer 1], #[.integer 3]]),
  ("duplicate unique conflict policies", expectSQL "duplicate unique conflict policies" "
    CREATE TABLE t(x PRIMARY KEY,UNIQUE(x,x),UNIQUE(x,x) ON CONFLICT REPLACE);
    INSERT INTO t VALUES(1); SELECT x FROM t;" #[#[.integer 1]]),
  ("named check diagnostic", expectError "named check diagnostic" "
    CREATE TABLE t(x CONSTRAINT positive CHECK(x>0)); INSERT INTO t VALUES(0);"
    "CHECK constraint failed: positive"),
  ("check schema validation", expectError "check schema validation" "
    CREATE TABLE t(x,CHECK(x<(SELECT 1)));" "subqueries prohibited in CHECK constraints"),
  ("ignored check integrity", expectSQL "ignored check integrity" "
    CREATE TABLE t(x CHECK(x>0)); PRAGMA ignore_check_constraints=ON;
    INSERT INTO t VALUES(0); PRAGMA ignore_check_constraints=OFF; PRAGMA integrity_check;"
    #[#[.text "CHECK constraint failed in t"]]),
  ("OR FAIL partial update", expectFailKeepsEarlierUpdates),
  ("multiple primary keys", expectError "multiple primary keys" "
    CREATE TABLE t(a PRIMARY KEY,b PRIMARY KEY);" "has more than one primary key"),
  ("failed unique index atomicity", expectFailedUniqueIndexIsAtomic),
  ("serialized connection stress", expectSerializedConnectionStress),
  ("verified WAL concurrency model", expectWALConcurrencyModel),
  ("WAL reader-writer stress", expectWALConnectionStress),
  ("cross-process serialized MVP commits", expectCrossProcessSerializedMVP),
  ("cross-process physical WAL readers and writers", expectCrossProcessPhysicalWAL),
  ("missing table error", expectError "missing table" "SELECT * FROM absent;" "no such table"),
  ("row width error", expectError "row width" "CREATE TABLE t(a,b); INSERT INTO t VALUES(1);" "2 columns")
]

def unitTests : Array (String × IO Unit) := unitTestsBatch0 ++ unitTestsBatch1

end SQLeanite.Tests
