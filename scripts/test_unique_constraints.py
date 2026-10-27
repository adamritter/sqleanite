#!/usr/bin/env python3
"""Automatic UNIQUE indexes: SQL results, diagnostics and persisted snapshots."""
import os,random,unittest
from test_pragma_tables import case
QUERIES={
 'column_create':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE);INSERT INTO t VALUES(1,'a'),(2,'b');",
 'table_create':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,UNIQUE(v));INSERT INTO t VALUES(1,'a'),(2,'b');",
 'duplicate':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE);INSERT INTO t VALUES(1,'a');INSERT INTO t VALUES(2,'a');",
 'ignore':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE);INSERT INTO t VALUES(1,'a');INSERT OR IGNORE INTO t VALUES(2,'a');SELECT changes(),* FROM t;",
 'replace':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE);INSERT INTO t VALUES(1,'a');INSERT OR REPLACE INTO t VALUES(2,'a');SELECT changes(),* FROM t;",
 'update_duplicate':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE);INSERT INTO t VALUES(1,'a'),(2,'b');UPDATE t SET v='a' WHERE id=2;",
 'update_ignore':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE);INSERT INTO t VALUES(1,'a'),(2,'b');UPDATE OR IGNORE t SET v='a' WHERE id=2;SELECT changes(),* FROM t;",
 'update_replace':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE);INSERT INTO t VALUES(1,'a'),(2,'b');UPDATE OR REPLACE t SET v='a' WHERE id=2;SELECT changes(),* FROM t;",
 'nulls':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE);INSERT INTO t VALUES(1,NULL),(2,NULL);SELECT * FROM t;",
 'numeric':"CREATE TABLE t(id INTEGER PRIMARY KEY,v NUMERIC UNIQUE);INSERT INTO t VALUES(1,'1');INSERT INTO t VALUES(2,1.0);",
 'binary':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE);INSERT INTO t VALUES(1,'a'),(2,'A');SELECT * FROM t;",
 'two_columns':"CREATE TABLE t(a TEXT UNIQUE,b INTEGER UNIQUE);INSERT INTO t VALUES('a',1),('b',2);PRAGMA index_list(t);",
 'deduplicate':"CREATE TABLE t(a TEXT UNIQUE,UNIQUE(a));INSERT INTO t VALUES('a');PRAGMA index_list(t);",
 'rowid_unique':"CREATE TABLE t(id INTEGER PRIMARY KEY UNIQUE,v UNIQUE);INSERT INTO t VALUES(1,'a');PRAGMA index_list(t);",
 'primary_after':"CREATE TABLE t(a UNIQUE,k TEXT PRIMARY KEY);INSERT INTO t VALUES('a','k');PRAGMA index_list(t);",
 'primary_before':"CREATE TABLE t(k TEXT PRIMARY KEY,a UNIQUE);INSERT INTO t VALUES('k','a');PRAGMA index_list(t);",
 'primary_same':"CREATE TABLE t(k TEXT UNIQUE PRIMARY KEY,a UNIQUE);INSERT INTO t VALUES('k','a');PRAGMA index_list(t);",
 'table_primary_after':"CREATE TABLE t(a UNIQUE,k TEXT,PRIMARY KEY(k));INSERT INTO t VALUES('a','k');PRAGMA index_list(t);",
 'table_primary_before':"CREATE TABLE t(a,k TEXT,PRIMARY KEY(k),UNIQUE(a));INSERT INTO t VALUES('a','k');PRAGMA index_list(t);",
 'upsert':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE,n);INSERT INTO t VALUES(1,'a',3);INSERT INTO t VALUES(2,'a',9) ON CONFLICT(v) DO UPDATE SET n=excluded.n RETURNING *;",
 'drop_index':"CREATE TABLE t(a UNIQUE);DROP INDEX sqlite_autoindex_t_1;",
 'transaction':"BEGIN;CREATE TABLE t(a UNIQUE);INSERT INTO t VALUES('a');COMMIT;",
 'rollback':"BEGIN;CREATE TABLE t(a UNIQUE);ROLLBACK;",
 'schema':"CREATE TABLE t(a UNIQUE);SELECT type,name,tbl_name,sql FROM sqlite_schema ORDER BY type,name;",
 'index_info':"CREATE TABLE t(a UNIQUE);PRAGMA index_info(sqlite_autoindex_t_1);PRAGMA index_xinfo(sqlite_autoindex_t_1);",
}
rng=random.Random(int(os.environ.get('SQLEANITE_UNIQUE_SEED','358600')))
for i in range(12):
 values=rng.sample(range(-1000,1000),12);rows=','.join(f'({j},{v})' for j,v in enumerate(values));QUERIES['generated_'+str(i)]=f'CREATE TABLE t(id INTEGER PRIMARY KEY,v INTEGER UNIQUE);INSERT INTO t VALUES{rows};INSERT OR IGNORE INTO t VALUES(100,{values[0]});SELECT * FROM t ORDER BY id;'
class UniqueConstraints(unittest.TestCase):pass
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(UniqueConstraints,'test_'+name+'_'+suffix,case(sql,mode,'CREATE TABLE seed(x INTEGER);'))
FOREIGN_SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,a TEXT UNIQUE,b INTEGER UNIQUE);INSERT INTO t VALUES(1,'a',10),(2,'b',20);"
FOREIGN_QUERIES={
 'insert':"INSERT INTO t VALUES(3,'c',30);SELECT * FROM t ORDER BY id;",
 'nothing':"INSERT INTO t VALUES(3,'a',30) ON CONFLICT DO NOTHING;SELECT * FROM t ORDER BY id;",
 'update':"UPDATE t SET a='c' WHERE id=1;SELECT * FROM t ORDER BY id;",
 'delete':"DELETE FROM t WHERE id=1;PRAGMA index_list(t);",
 'empty':"DELETE FROM t;INSERT INTO t VALUES(3,NULL,NULL),(4,NULL,NULL);SELECT * FROM t ORDER BY id;",
 'multiple_conflicts':"INSERT INTO t VALUES(3,'a',20);",
 'upsert':"INSERT INTO t VALUES(3,'a',30) ON CONFLICT(a) DO UPDATE SET b=excluded.b RETURNING *;",
 'replace_both':"INSERT OR REPLACE INTO t VALUES(3,'a',20);SELECT * FROM t ORDER BY id;",
 'returning':"INSERT INTO t VALUES(3,'c',30) RETURNING *;",
 'schema':"SELECT rowid,type,name,rootpage,sql FROM sqlite_schema ORDER BY rowid;",
}
for name,sql in FOREIGN_QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(UniqueConstraints,'test_foreign_'+name+'_'+suffix,case(sql,mode,FOREIGN_SETUP))
if __name__=='__main__':unittest.main()
