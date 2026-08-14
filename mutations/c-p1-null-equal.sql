CREATE TABLE t(a INTEGER PRIMARY KEY, b);
INSERT INTO t VALUES(1,'x'),(2,NULL),(3,'z');
SELECT 'srt', group_concat(a) FROM (SELECT a FROM t ORDER BY b);
SELECT 'eq', count(*) FROM t WHERE b='x';
SELECT 'dist', count(DISTINCT b) FROM t;
SELECT 'uni', count(*) FROM (SELECT b FROM t UNION SELECT b FROM t);
SELECT 'grp', count(*) FROM (SELECT b FROM t GROUP BY b);
