#!/usr/bin/env python3
"""Exact persisted index declarations after production file commits."""
import os,random,unittest
from test_pragma_tables import case
SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'a',10),(2,'b',20),(3,'c',30);"
QUERIES={
 'create_text': 'CREATE INDEX ix ON t(v);',
 'create_integer': 'CREATE INDEX ix ON t(n);',
 'create_unique': 'CREATE UNIQUE INDEX ix ON t(n);',
 'quoted': 'CREATE INDEX "Odd Index" ON "t" ( "v" );',
 'case_space': 'create unique index if not exists "Ix" on t (n ASC);',
 'insert': "CREATE INDEX ix ON t(v);INSERT INTO t VALUES(4,'d',40);",
 'update': "CREATE INDEX ix ON t(v);UPDATE t SET v='x' WHERE id=1;",
 'delete': 'CREATE INDEX ix ON t(n);DELETE FROM t WHERE id=1;',
 'delete_all': 'CREATE INDEX ix ON t(n);DELETE FROM t;',
 'two_indexes': 'CREATE INDEX iv ON t(v);CREATE UNIQUE INDEX ix ON t(n);',
 'drop_other': 'CREATE INDEX iv ON t(v);CREATE INDEX ix ON t(n);DROP INDEX iv;',
 'transaction': 'BEGIN;CREATE INDEX ix ON t(n);INSERT INTO t VALUES(4,\'d\',40);COMMIT;',
 'rollback': 'BEGIN;CREATE INDEX ix ON t(n);ROLLBACK;',
 'savepoint': 'SAVEPOINT a;CREATE INDEX iv ON t(v);SAVEPOINT b;CREATE INDEX ix ON t(n);ROLLBACK TO b;RELEASE a;',
 'metadata': 'PRAGMA application_id=1234;PRAGMA user_version=77;CREATE INDEX ix ON t(n);',
 'upsert': "CREATE UNIQUE INDEX ix ON t(n);INSERT INTO t VALUES(4,'d',10) ON CONFLICT(n) DO UPDATE SET v=excluded.v;",
}
class IndexCatalog(unittest.TestCase):pass
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(IndexCatalog,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
rng=random.Random(int(os.environ.get('SQLEANITE_INDEX_CATALOG_SEED','358400')))
for i in range(12):
 name='fresh_'+str(rng.randrange(1000000));column=rng.choice(['n','v']);sql=f'CREATE INDEX "{name}" ON t ("{column}");UPDATE t SET n=n+1 WHERE id={rng.randrange(1,4)};'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(IndexCatalog,'test_generated_'+str(i)+'_'+suffix,case(sql,mode,SETUP))
for label,setup in {
 'existing':SETUP+'CREATE UNIQUE INDEX "original index" ON t (n);',
 'overflow':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,printf('%.*c',9000,'x'),10),(2,'b',20);CREATE INDEX original ON t(v);",
 'many_rows':"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);WITH RECURSIVE c(i) AS(VALUES(1) UNION ALL SELECT i+1 FROM c WHERE i<300) INSERT INTO t SELECT i,printf('value %d',i),i FROM c;CREATE INDEX original ON t(n);",
}.items():
 for name,sql in {'insert':"INSERT INTO t VALUES(400,'new',400);",'update':"UPDATE t SET v='changed' WHERE id=1;",'shrink':'DELETE FROM t WHERE id>1;','clear':'DELETE FROM t;'}.items():
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(IndexCatalog,'test_'+label+'_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
