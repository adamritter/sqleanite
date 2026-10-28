#!/usr/bin/env python3
"""Actual WITHOUT ROWID PK direction, repeated-column layout and secondary keys."""
import os,random,unittest
from test_without_rowid import case
class WithoutRowidKeys(unittest.TestCase):pass
OBS='SELECT * FROM t;PRAGMA index_xinfo(t);PRAGMA index_list(t);'
Q={
 'desc_create':('',"CREATE TABLE t(a TEXT,b,n,PRIMARY KEY(a DESC)) WITHOUT ROWID;INSERT INTO t VALUES('a','one',1),('b','two',2);"+OBS),
 'desc_open':("CREATE TABLE t(a TEXT,b,n,PRIMARY KEY(a DESC)) WITHOUT ROWID;INSERT INTO t VALUES('a','one',1),('b','two',2);",OBS),
 'desc_update':("CREATE TABLE t(a TEXT,b,n,PRIMARY KEY(a DESC)) WITHOUT ROWID;INSERT INTO t VALUES('a','one',1),('b','two',2);","UPDATE t SET a='c' WHERE a='a';"+OBS),
 'mixed':("CREATE TABLE t(a TEXT,b TEXT,n,PRIMARY KEY(a DESC,b ASC)) WITHOUT ROWID;INSERT INTO t VALUES('a','a',1),('b','a',2),('a','b',3);",'UPDATE t SET n=n+1;'+OBS),
 'all_desc':("CREATE TABLE t(a TEXT,b TEXT,n,PRIMARY KEY(a DESC,b DESC)) WITHOUT ROWID;INSERT INTO t VALUES('a','a',1),('b','a',2),('a','b',3);",'UPDATE t SET n=n+1;'+OBS),
 'secondary':("CREATE TABLE t(a TEXT,b TEXT,n,PRIMARY KEY(a DESC,b)) WITHOUT ROWID;INSERT INTO t VALUES('a','a',1),('b','a',1),('a','b',2);CREATE INDEX x ON t(n);",'UPDATE t SET n=n+1;PRAGMA index_xinfo(x);'+OBS),
 'shared_secondary':("CREATE TABLE t(a TEXT,b TEXT,n,PRIMARY KEY(a DESC,b)) WITHOUT ROWID;INSERT INTO t VALUES('a','a',1),('b','a',1),('a','b',2);CREATE INDEX x ON t(a,n);",'UPDATE t SET n=n+1;PRAGMA index_xinfo(x);'+OBS),
 'repeated_same':("CREATE TABLE t(a TEXT,b TEXT,n,PRIMARY KEY(a,a,b)) WITHOUT ROWID;INSERT INTO t VALUES('a','a',1),('b','a',2),('a','b',3);",'UPDATE t SET n=n+1;'+OBS),
 'repeated_collation':("CREATE TABLE t(a TEXT COLLATE NOCASE,b TEXT,n,PRIMARY KEY(a,a COLLATE BINARY,b)) WITHOUT ROWID;INSERT INTO t VALUES('A','a',1),('a','b',2),('B','a',3);",'UPDATE t SET n=n+1;'+OBS),
 'repeated_direction':("CREATE TABLE t(a TEXT,b TEXT,n,PRIMARY KEY(a DESC,a ASC,b)) WITHOUT ROWID;INSERT INTO t VALUES('a','a',1),('b','a',2),('a','b',3);",'UPDATE t SET n=n+1;'+OBS),
 'repeated_suffix':("CREATE TABLE t(a TEXT COLLATE NOCASE,b TEXT,n,PRIMARY KEY(a,a COLLATE BINARY,b)) WITHOUT ROWID;INSERT INTO t VALUES('A','a',1),('a','b',2),('B','a',3);CREATE INDEX x ON t(a,n);",'UPDATE t SET n=n+1;PRAGMA index_xinfo(x);'+OBS),
 'desc_unique':("CREATE TABLE t(a TEXT,b TEXT UNIQUE,n,PRIMARY KEY(a DESC)) WITHOUT ROWID;INSERT INTO t VALUES('a','a',1),('b','b',2);","INSERT OR REPLACE INTO t VALUES('c','a',3);"+OBS),
}
rng=random.Random(int(os.environ.get('SQLEANITE_WITHOUT_ROWID_KEYS_SEED','1868001')))
for i in range(12):
 n=rng.randrange(20,900)
 Q[f'fresh_{i}']=("CREATE TABLE t(a TEXT,b TEXT,n,PRIMARY KEY(a DESC,b)) WITHOUT ROWID;INSERT INTO t VALUES('a','a',1),('b','a',2),('a','b',3);",f'UPDATE t SET n={n};'+OBS)
for name,(setup,sql) in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(WithoutRowidKeys,'test_'+name+'_'+suffix,case(setup,sql,mode))
if __name__=='__main__':unittest.main()
