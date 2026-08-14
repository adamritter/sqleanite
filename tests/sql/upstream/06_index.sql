-- Adapted from upstream test/index.test: index creation and use.
CREATE TABLE t1(a INTEGER PRIMARY KEY, b);
INSERT INTO t1 VALUES(1,'alpha');
INSERT INTO t1 VALUES(2,'beta');
INSERT INTO t1 VALUES(3,'gamma');
CREATE INDEX i1 ON t1(b);
SELECT a FROM t1 WHERE b='beta';
SELECT a FROM t1 WHERE b='none';
INSERT INTO t1 VALUES(4,'beta');
SELECT a FROM t1 WHERE b='beta' ORDER BY a;
DELETE FROM t1 WHERE a=2;
SELECT a FROM t1 WHERE b='beta' ORDER BY a;
