PRAGMA journal_mode=WAL;
CREATE TABLE t(a INTEGER PRIMARY KEY, b);
INSERT INTO t VALUES(1,'x'),(2,'y');
SELECT count(*) FROM t;
PRAGMA integrity_check;
