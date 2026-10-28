#!/usr/bin/env python3
"""Composite physical index keys, metadata and actual multi-column uniqueness."""
import os,random,unittest,subprocess,tempfile
from pathlib import Path
from test_pragma_tables import BINARY,SQLITE
from test_check_add_column import case
class CompositeIndexes(unittest.TestCase):pass
BASE="CREATE TABLE t(id INTEGER PRIMARY KEY,a TEXT,b,n);INSERT INTO t VALUES(1,'A',1,1),(2,'A',2,2),(3,'b',1,3),(4,NULL,1,4),(5,'A',NULL,5);"
CREATE='CREATE INDEX ci ON t(a,b);'
OBSERVE='SELECT * FROM t ORDER BY id;PRAGMA index_list(t);PRAGMA index_xinfo(ci);'
Q={
 'unique_expression':(BASE,"CREATE UNIQUE INDEX ci ON t(lower(a),b);INSERT INTO t VALUES(6,'a',1,6);"),
 'unique_partial':(BASE,"CREATE UNIQUE INDEX ci ON t(a,b) WHERE n>1;INSERT INTO t VALUES(6,'A',2,6);"),
 'replace_collated':(BASE,"CREATE UNIQUE INDEX ci ON t(a COLLATE NOCASE,b);INSERT OR REPLACE INTO t VALUES(6,'a',1,6);"+OBSERVE),
 'rowid_update':(BASE+CREATE,'UPDATE t SET id=30 WHERE id=1;'+OBSERVE),
 'second_error':(BASE,"CREATE INDEX ci ON t(a,abs(b));INSERT INTO t VALUES(6,'d',-9223372036854775808,6);"),
 'unknown_second':(BASE,'CREATE INDEX ci ON t(a,absent(b));'),
 'rowid_second':(BASE,'CREATE INDEX ci ON t(a,rowid+1);'),
 'qualified_second':(BASE,'CREATE INDEX ci ON t(a,t.b+1);'),
 'unknown_collation_second':(BASE,'CREATE INDEX ci ON t(a,b COLLATE missing);'),
 'create_duplicate':(BASE+"INSERT INTO t VALUES(6,'A',1,6);",'CREATE UNIQUE INDEX ci ON t(a,b);'),
 'mixed_numeric':(BASE,'CREATE INDEX ci ON t(a,b+0.0);'+OBSERVE),
 'create_rollback':(BASE,'BEGIN;'+CREATE+'ROLLBACK;PRAGMA index_list(t);'),
 'create':(BASE,CREATE+OBSERVE),
 'open':(BASE+CREATE,OBSERVE),
 'insert':(BASE+CREATE,"INSERT INTO t VALUES(6,'A',3,6);"+OBSERVE),
 'update':(BASE+CREATE,"UPDATE t SET a='changed',b=8 WHERE id=2;"+OBSERVE),
 'delete':(BASE+CREATE,'DELETE FROM t WHERE id=2;'+OBSERVE),
 'drop':(BASE+CREATE,'DROP INDEX ci;PRAGMA index_list(t);'),
 'partial':(BASE,'CREATE INDEX ci ON t(a,b) WHERE n>2;UPDATE t SET n=9 WHERE id=1;'+OBSERVE),
 'expression':(BASE,'CREATE INDEX ci ON t(lower(a),b+1);'+OBSERVE),
 'collated':(BASE,'CREATE INDEX ci ON t(a COLLATE NOCASE,b);'+OBSERVE),
 'unique':(BASE,"CREATE UNIQUE INDEX ci ON t(a,b);INSERT INTO t VALUES(6,'A',1,6);"),
 'unique_prefix':(BASE,"CREATE UNIQUE INDEX ci ON t(a,b);INSERT INTO t VALUES(6,'A',3,6);"+OBSERVE),
 'ignore':(BASE,"CREATE UNIQUE INDEX ci ON t(a,b);INSERT OR IGNORE INTO t VALUES(6,'A',1,6);"+OBSERVE),
 'replace':(BASE,"CREATE UNIQUE INDEX ci ON t(a,b);INSERT OR REPLACE INTO t VALUES(6,'A',1,6);"+OBSERVE),
 'nulls':(BASE,"CREATE UNIQUE INDEX ci ON t(a,b);INSERT INTO t VALUES(6,NULL,1,6),(7,'A',NULL,7);"+OBSERVE),
 'three_keys':(BASE,'CREATE INDEX ci ON t(a,b,n);'+OBSERVE),
 'virtual':(BASE+CREATE,"SELECT * FROM pragma_index_info('ci');SELECT * FROM pragma_index_xinfo('ci');"),
 'rollback':(BASE+CREATE,"BEGIN;UPDATE t SET a='changed';ROLLBACK;"+OBSERVE),
 'wide':("CREATE TABLE t(id INTEGER PRIMARY KEY,a,b,n);WITH RECURSIVE c(i) AS(VALUES(1) UNION ALL SELECT i+1 FROM c WHERE i<20) INSERT INTO t SELECT i,printf('%03000d',i),i%3,i FROM c;CREATE INDEX ci ON t(a,b);",'UPDATE t SET b=b+5 WHERE id<10;'+OBSERVE),
}
rng=random.Random(int(os.environ.get('SQLEANITE_COMPOSITE_INDEX_SEED','1842001')))
for i in range(12):
 amount=rng.randrange(10,900)
 Q[f'fresh_{i}']=(BASE+CREATE,f'UPDATE t SET b={amount} WHERE id={i%5+1};'+OBSERVE)
for name,(setup,sql) in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(CompositeIndexes,'test_'+name+'_'+suffix,case(sql,mode,setup))
def corrupt_case(mode):
 def test(self):
  with tempfile.TemporaryDirectory(prefix='sqleanite-composite-corrupt-') as directory:
   path=Path(directory)/'corrupt.db'
   setup=BASE+"CREATE INDEX ci ON t(a,b);PRAGMA writable_schema=ON;UPDATE sqlite_schema SET sql='CREATE INDEX ci ON t(a,b+1)' WHERE name='ci';PRAGMA writable_schema=OFF;"
   subprocess.run([SQLITE,str(path)],input='.dbconfig defensive off\n'+setup,text=True,capture_output=True,check=True)
   check=subprocess.run([SQLITE,str(path),'PRAGMA integrity_check;'],text=True,capture_output=True,check=True)
   self.assertNotEqual(check.stdout.strip(),'ok')
   result=subprocess.run([str(BINARY),mode,str(path)],input='SELECT * FROM t;',text=True,capture_output=True,timeout=30)
   self.assertEqual(result.returncode,1)
   self.assertIn('invalid general MVP SQLite image',result.stderr)
 return test
for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(CompositeIndexes,'test_corrupt_second_'+suffix,corrupt_case(mode))
if __name__=='__main__':unittest.main()
