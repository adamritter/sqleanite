#!/usr/bin/env python3
"""Partial-index SQL, opening, mutation and independent file regressions.

Each case fails normally until the production SQL/file path supports it.
Run one: python scripts/test_partial_indexes.py PartialIndexes.test_create_rollback
"""
import os,random,unittest
from test_check_add_column import case
class PartialIndexes(unittest.TestCase):pass
BASE="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'a',-2),(2,'b',0),(3,'c',2),(4,'d',3),(5,'e',NULL);"
CREATE='CREATE INDEX pi ON t(n) WHERE n>0;'
OBSERVE='SELECT id,v,n FROM t ORDER BY id;PRAGMA index_list(t);PRAGMA index_xinfo(pi);'
Q={
 'create':(BASE,CREATE+'SELECT n FROM t WHERE n>0 ORDER BY n;'+OBSERVE),
 'empty_create':('CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);',CREATE+OBSERVE),
 'null_predicate':(BASE,'CREATE INDEX pi ON t(n) WHERE n IS NULL;SELECT id FROM t WHERE n IS NULL;'+OBSERVE),
 'false_predicate':(BASE,'CREATE INDEX pi ON t(n) WHERE 0;'+OBSERVE),
 'expression_predicate':(BASE,'CREATE INDEX pi ON t(n) WHERE n%2=0 AND n>0;'+OBSERVE),
 'read_opened':(BASE+CREATE,'SELECT n FROM t WHERE n>0 ORDER BY n;'+OBSERVE),
 'virtual_metadata':(BASE+CREATE,"SELECT * FROM pragma_index_list('t');SELECT * FROM pragma_index_xinfo('pi');"),
 'drop_if_exists':(BASE+CREATE,'DROP INDEX IF EXISTS pi;PRAGMA index_list(t);'),
 'multiple_metadata':(BASE+CREATE+'CREATE INDEX ni ON t(v);',"PRAGMA index_list(t);SELECT * FROM pragma_index_list('t');"),
 'index_root_identity':(BASE+CREATE+'CREATE INDEX ni ON t(v);',"UPDATE t SET n=8 WHERE id=1;SELECT name,rootpage FROM sqlite_schema WHERE type='index' ORDER BY name;"),
 'insert_enter':(BASE+CREATE,"INSERT INTO t VALUES(6,'f',7);"+OBSERVE),
 'insert_outside':(BASE+CREATE,"INSERT INTO t VALUES(6,'f',-7);"+OBSERVE),
 'insert_null':(BASE+CREATE,"INSERT INTO t VALUES(6,'f',NULL);"+OBSERVE),
 'update_enter':(BASE+CREATE,'UPDATE t SET n=8 WHERE id=1;'+OBSERVE),
 'update_leave':(BASE+CREATE,'UPDATE t SET n=-8 WHERE id=3;'+OBSERVE),
 'update_key':(BASE+CREATE,'UPDATE t SET n=8 WHERE id=3;'+OBSERVE),
 'update_rowid':(BASE+CREATE,'UPDATE t SET id=30 WHERE id=3;'+OBSERVE),
 'delete_indexed':(BASE+CREATE,'DELETE FROM t WHERE id=3;'+OBSERVE),
 'delete_outside':(BASE+CREATE,'DELETE FROM t WHERE id=1;'+OBSERVE),
 'replace':(BASE+CREATE,"INSERT OR REPLACE INTO t VALUES(3,'replaced',-9);"+OBSERVE),
 'ignore':(BASE+CREATE,"INSERT OR IGNORE INTO t VALUES(3,'ignored',9);"+OBSERVE),
 'drop':(BASE+CREATE,'DROP INDEX pi;SELECT * FROM t ORDER BY id;PRAGMA index_list(t);'),
 'rollback':(BASE+CREATE,'BEGIN;UPDATE t SET n=8 WHERE id=1;ROLLBACK;'+OBSERVE),
 'savepoint':(BASE+CREATE,'SAVEPOINT s;UPDATE t SET n=8 WHERE id=1;ROLLBACK TO s;RELEASE s;'+OBSERVE),
 'create_rollback':(BASE,'BEGIN;'+CREATE+'ROLLBACK;PRAGMA index_list(t);'),
 'create_if_exists':(BASE+CREATE,'CREATE INDEX IF NOT EXISTS pi ON t(absent(n)) WHERE missing;'+OBSERVE),
 'unique_active':(BASE,'CREATE UNIQUE INDEX pi ON t(n) WHERE n>0;INSERT INTO t VALUES(6,\'f\',2);'),
 'unique_outside':(BASE,'CREATE UNIQUE INDEX pi ON t(n) WHERE n>0;INSERT INTO t VALUES(6,\'f\',0);'+OBSERVE),
 'unique_ignore':(BASE,"CREATE UNIQUE INDEX pi ON t(n) WHERE n>0;INSERT OR IGNORE INTO t VALUES(6,'f',2);"+OBSERVE),
 'unique_replace':(BASE,"CREATE UNIQUE INDEX pi ON t(n) WHERE n>0;INSERT OR REPLACE INTO t VALUES(6,'f',2);"+OBSERVE),
 'wide_keys':("CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);WITH RECURSIVE c(i) AS(VALUES(1) UNION ALL SELECT i+1 FROM c WHERE i<24) INSERT INTO t SELECT i,printf('%03000d',i),i-12 FROM c;CREATE INDEX pi ON t(v) WHERE n>0;",'UPDATE t SET n=n+20 WHERE id<=12;SELECT count(*) FROM t WHERE n>0;'+OBSERVE),
 'mixed_keys':("CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n);INSERT INTO t VALUES(1,'a',NULL),(2,'b',1),(3,'c',1.5),(4,'d','abc'),(5,'e',x'0001');CREATE INDEX pi ON t(n) WHERE id>1;","INSERT INTO t VALUES(6,'f',2.5);"+OBSERVE),
}
rng=random.Random(int(os.environ.get('SQLEANITE_PARTIAL_INDEX_SEED','1828001')))
for i in range(12):
 boundary=rng.randrange(-20,20);value=rng.randrange(-50,50)
 setup=BASE+f'CREATE INDEX pi ON t(n) WHERE n>{boundary};'
 Q[f'fresh_{i}']=(setup,f'UPDATE t SET n={value} WHERE id={i%5+1};SELECT id,n FROM t WHERE n>{boundary} ORDER BY n,id;'+OBSERVE)
for name,(setup,sql) in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(PartialIndexes,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
