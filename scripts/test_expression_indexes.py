#!/usr/bin/env python3
"""Scalar expression-index SQL and independent persisted-file regressions."""
import os,random,unittest,subprocess,tempfile
from pathlib import Path
from test_pragma_tables import BINARY,SQLITE
from test_check_add_column import case
class ExpressionIndexes(unittest.TestCase):pass
BASE="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'A',-2),(2,'b',0),(3,'C',2),(4,'d',3),(5,NULL,NULL);"
CREATE='CREATE INDEX ei ON t(lower(v));'
OBSERVE='SELECT * FROM t ORDER BY id;PRAGMA index_list(t);PRAGMA index_xinfo(ei);'
Q={
 'create':(BASE,CREATE+"SELECT id FROM t WHERE lower(v)='missing';"+OBSERVE),
 'opened':(BASE+CREATE,"SELECT id FROM t WHERE lower(v)='a';"+OBSERVE),
 'insert':(BASE+CREATE,"INSERT INTO t VALUES(6,'E',7);"+OBSERVE),
 'update':(BASE+CREATE,"UPDATE t SET v='Changed' WHERE id=3;"+OBSERVE),
 'delete':(BASE+CREATE,'DELETE FROM t WHERE id=3;'+OBSERVE),
 'drop':(BASE+CREATE,'DROP INDEX ei;PRAGMA index_list(t);'),
 'numeric':(BASE,'CREATE INDEX ei ON t(n*1.0);UPDATE t SET n=8 WHERE id=1;'+OBSERVE),
 'partial':(BASE,'CREATE INDEX ei ON t(lower(v)) WHERE n>0;UPDATE t SET n=8 WHERE id=1;'+OBSERVE),
 'unique':(BASE,'CREATE UNIQUE INDEX ei ON t(lower(v));INSERT INTO t VALUES(6,\'a\',9);'),
 'ignore':(BASE,'CREATE UNIQUE INDEX ei ON t(lower(v));INSERT OR IGNORE INTO t VALUES(6,\'a\',9);'+OBSERVE),
 'replace':(BASE,'CREATE UNIQUE INDEX ei ON t(lower(v));INSERT OR REPLACE INTO t VALUES(6,\'a\',9);'+OBSERVE),
 'virtual_metadata':(BASE+CREATE,"SELECT * FROM pragma_index_list('t');SELECT * FROM pragma_index_xinfo('ei');"),
 'rowid_error':(BASE,'CREATE INDEX ei ON t(rowid+0);'),
 'qualified_error':(BASE,'CREATE INDEX ei ON t(t.n+0);'),
 'function_error':(BASE,'CREATE INDEX ei ON t(absent(n));'),
 'quoted_column':(BASE,'CREATE INDEX ei ON t("n");'+OBSERVE),
 'quoted_partial':(BASE,'CREATE INDEX ei ON t("n") WHERE n>0;'+OBSERVE),
 'quoted_expression':(BASE,'CREATE INDEX ei ON t(lower("v"));'+OBSERVE),
 'empty_binding':('CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);','CREATE INDEX ei ON t(absent(n));'),
 'random_error':(BASE,'CREATE INDEX ei ON t(random());'),
 'changes_error':(BASE,'CREATE INDEX ei ON t(changes());'),
 'lastid_error':(BASE,'CREATE INDEX ei ON t(last_insert_rowid());'),
 'version_error':(BASE,'CREATE INDEX ei ON t(sqlite_version());'),
 'clock_time_error':(BASE,'CREATE INDEX ei ON t(current_time);'),
 'clock_timestamp_error':(BASE,'CREATE INDEX ei ON t(current_timestamp);'),
 'clock_error':(BASE,'CREATE INDEX ei ON t(current_date);'),
 'date_error':(BASE,"CREATE INDEX ei ON t(date('now'));"),
 'aggregate_error':(BASE,'CREATE INDEX ei ON t(sum(n));'),
 'subquery_error':(BASE,'CREATE INDEX ei ON t((SELECT 1));'),
 'date_key':(BASE,"CREATE INDEX ei ON t(date('2000-01-01','+'||n||' days'));"+OBSERVE),
 'lazy_date':(BASE,"CREATE INDEX ei ON t(CASE WHEN 1 THEN n ELSE date('now') END);"+OBSERVE),
 'mixed_numeric':("CREATE TABLE t(id INTEGER PRIMARY KEY,v,n);INSERT INTO t VALUES(1,1,1),(2,2,1.0),(3,3,1.5),(4,4,'2'),(5,5,NULL);",'CREATE INDEX ei ON t(+n);'+OBSERVE),
 'overflow':(BASE,"CREATE INDEX ei ON t(v||printf('%.*c',3000,'z'));UPDATE t SET v='overflow' WHERE id=1;"+OBSERVE),
 'rollback':(BASE+CREATE,"BEGIN;UPDATE t SET v='Changed' WHERE id=1;ROLLBACK;"+OBSERVE),
}
rng=random.Random(int(os.environ.get('SQLEANITE_EXPRESSION_INDEX_SEED','1831001')))
for i in range(12):
 amount=rng.randrange(2,100);value=rng.randrange(-20,30)
 Q[f'fresh_{i}']=(BASE+f'CREATE INDEX ei ON t(n+{amount});',f'UPDATE t SET n={value} WHERE id={i%5+1};'+OBSERVE)
for name,(setup,sql) in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(ExpressionIndexes,'test_'+name+'_'+suffix,case(sql,mode,setup))
def corrupt_case(mode):
 def test(self):
  with tempfile.TemporaryDirectory(prefix='sqleanite-expression-corrupt-') as directory:
   path=Path(directory)/'corrupt.db'
   setup=BASE+"CREATE INDEX ei ON t(upper(v));PRAGMA writable_schema=ON;UPDATE sqlite_schema SET sql='CREATE INDEX ei ON t(lower(v))' WHERE name='ei';PRAGMA writable_schema=OFF;"
   subprocess.run([SQLITE,str(path)],input='.dbconfig defensive off\n'+setup,text=True,capture_output=True,check=True)
   check=subprocess.run([SQLITE,str(path),'PRAGMA integrity_check;'],text=True,capture_output=True,check=True)
   self.assertNotEqual(check.stdout.strip(),'ok')
   result=subprocess.run([str(BINARY),mode,str(path)],input='SELECT * FROM t;',text=True,capture_output=True,timeout=30)
   self.assertEqual(result.returncode,1)
   self.assertIn('invalid general MVP SQLite image',result.stderr)
 return test
for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(ExpressionIndexes,'test_corrupt_key_'+suffix,corrupt_case(mode))
if __name__=='__main__':unittest.main()
