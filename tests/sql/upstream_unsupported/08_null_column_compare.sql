-- Split out of 08_null.sql. Comparing two columns in a WHERE clause is not
-- supported by the Core predicate surface; it rejects with
--   unsupported verified-MVP SQL: non-literal INSERT value
-- Every other three-valued-logic case in 08_null.sql matches C SQLite exactly.
CREATE TABLE t1(a INTEGER PRIMARY KEY, b, c);
INSERT INTO t1 VALUES(1,0,0);
INSERT INTO t1 VALUES(2,0,1);
INSERT INTO t1 VALUES(5,NULL,0);
INSERT INTO t1 VALUES(7,NULL,NULL);
SELECT a FROM t1 WHERE b=c ORDER BY a;
