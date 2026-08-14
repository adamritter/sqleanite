-- Adapted from upstream test/insert.test: INSERT forms.
CREATE TABLE t1(one INTEGER PRIMARY KEY, two);
INSERT INTO t1(one,two) VALUES(1,'first');
INSERT INTO t1 VALUES(2,'second');
INSERT INTO t1(two,one) VALUES('third',3);
INSERT INTO t1 VALUES(4,NULL);
SELECT one,two FROM t1 ORDER BY one;
INSERT INTO t1 VALUES(5,'fifth'),(6,'sixth');
SELECT one FROM t1 ORDER BY one;
