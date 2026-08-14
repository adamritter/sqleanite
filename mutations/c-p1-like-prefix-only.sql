CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT);
INSERT INTO t VALUES(1,'apple'),(2,'apricot'),(3,'banana');
SELECT group_concat(b) FROM (SELECT b FROM t WHERE b LIKE 'ap%' ORDER BY b);
SELECT group_concat(b) FROM (SELECT b FROM t WHERE b LIKE 'banana' ORDER BY b);
SELECT count(*) FROM t WHERE b LIKE 'zzz%';
