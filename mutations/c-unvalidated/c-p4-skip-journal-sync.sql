CREATE TABLE t(id INTEGER PRIMARY KEY, value TEXT);
INSERT INTO t VALUES(1,'first'),(2,'second'),(3,'third');
CREATE INDEX t_value ON t(value);
SELECT id,value FROM t INDEXED BY t_value ORDER BY value;
