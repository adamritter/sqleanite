#!/usr/bin/env python3
"""Reference comparisons for PRAGMA table functions, including hidden columns."""
import os
from pathlib import Path
import random
import re
import subprocess
import tempfile
import unittest
from test_last_insert_rowid import snapshot
ROOT=Path(__file__).resolve().parents[1]
SQLITE=os.environ.get('SQLITE3_BIN','sqlite3')
BINARY=ROOT/'.lake/build/bin/sqleanite'
QUERIES={
 'table_info': "SELECT * FROM pragma_table_info('t');",
 'table_xinfo': "SELECT * FROM pragma_table_xinfo('t');",
 'index_list': "SELECT * FROM pragma_index_list('t');",
 'index_info': "SELECT * FROM pragma_index_info('ix');",
 'index_xinfo': "SELECT * FROM pragma_index_xinfo('ix');",
 'pragma_list': "SELECT name FROM pragma_pragma_list() ORDER BY name;",
 'filter': "SELECT name,type FROM pragma_table_info('t') WHERE cid>0 ORDER BY cid DESC;",
 'aggregate': "SELECT count(*),sum(cid),min(name) FROM pragma_table_info('t');",
 'join': "SELECT p.name,q.cid FROM pragma_table_info('t') p JOIN pragma_table_xinfo('t') q ON p.cid=q.cid ORDER BY p.cid;",
 'union': "SELECT name FROM pragma_table_info('t') UNION SELECT name FROM pragma_index_info('ix') ORDER BY 1;",
 'derived': "SELECT name FROM (SELECT name FROM pragma_table_info('t')) ORDER BY name;",
 'cte': "WITH p AS (SELECT * FROM pragma_table_info('t')) SELECT name FROM p ORDER BY cid;",
 'quoted': "SELECT p.name FROM main.\"pragma_table_info\"('t') AS p ORDER BY p.cid;",
 'case': "SELECT name FROM PRAGMA_TABLE_INFO('t');",
 'expression': "SELECT name FROM pragma_table_info(lower('T'));",
 'concat': "SELECT name FROM pragma_table_info('' || 't');",
 'null': "SELECT count(*) FROM pragma_table_info(NULL);",
 'empty': "SELECT * FROM pragma_table_info('missing');",
 'no_argument': "SELECT * FROM pragma_table_info();",
 'temp': "SELECT * FROM pragma_table_info('t','temp');",
 'schema': "SELECT * FROM pragma_table_info('t','main');",
 'hidden': "SELECT rowid,arg,typeof(arg),schema,typeof(schema) FROM pragma_table_info('t');",
 'hidden_schema': "SELECT p.arg,p.schema,p._rowid_ FROM pragma_table_info('t','main') p;",
 'hidden_filter': "SELECT name FROM pragma_table_info('t') WHERE arg='t' AND schema IS NULL ORDER BY cid;",
 'hidden_left': "SELECT p.name,q.arg,q.schema FROM pragma_table_info('t') p LEFT JOIN pragma_table_info('missing','main') q ON p.cid=q.cid ORDER BY p.cid;",
 'hidden_both': "SELECT p.arg,q.arg FROM pragma_table_info('t') p JOIN pragma_table_info('t') q ON p.cid=q.cid ORDER BY p.cid;",
 'hidden_alias': "SELECT name AS arg FROM pragma_table_info('t') ORDER BY arg;",
 'affinity': "SELECT count(*) FROM pragma_table_info('t') WHERE cid='0';",
 'limit': "SELECT * FROM pragma_table_info('t') LIMIT 1 OFFSET 1;",
 'unknown_schema': "SELECT * FROM pragma_table_info('t','missing');",
 'too_many': "SELECT * FROM pragma_table_info('t','main',0);",
 'list_arity': "SELECT * FROM pragma_pragma_list('main');",
 'unknown_function': "SELECT * FROM absent_function('t');",
 'ordinary_table': "SELECT * FROM t(1);",
 'unknown_column': "SELECT * FROM pragma_table_info(missing);",
 'ambiguous': "SELECT arg FROM pragma_table_info('t') p JOIN pragma_table_info('t') q ON p.cid=q.cid;",
 'runtime_error': "SELECT * FROM pragma_table_info(abs(-9223372036854775808));",
}
class PragmaTables(unittest.TestCase): pass

def case(sql,mode,setup):
 def test(self):
  with tempfile.TemporaryDirectory(prefix='sqleanite-pragma-tables-') as directory:
   left=Path(directory)/'lean.db'; right=Path(directory)/'sqlite.db'
   for path in (left,right): subprocess.run([SQLITE,str(path)],input=setup,text=True,check=True,capture_output=True)
   lean=subprocess.run([str(BINARY),mode,str(left)],input=sql,text=True,capture_output=True,timeout=30)
   ref=subprocess.run([SQLITE,'-batch','-bail',str(right)],input=sql,text=True,capture_output=True,timeout=30)
   self.assertEqual(lean.returncode,ref.returncode,lean.stderr+' / '+ref.stderr)
   self.assertEqual(lean.stdout,ref.stdout,lean.stderr)
   if ref.returncode:
    def error(result):
     line=result.stderr.splitlines()[0] if result.stderr else ''
     return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',line)
    self.assertEqual(error(lean),error(ref))
   self.assertEqual(snapshot(left),snapshot(right))
 return test

setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER DEFAULT 7);CREATE INDEX ix ON t(n);'
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(PragmaTables,'test_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_PRAGMA_TABLE_SEED','356901')))
for i in range(12):
 fields=','.join(f'c{k} {rng.choice(["TEXT","INTEGER","BLOB",""])} DEFAULT {rng.randrange(-1000,1000)}' for k in range(rng.randrange(1,10)))
 sql="SELECT * FROM pragma_table_info('fresh') ORDER BY cid;SELECT arg,schema FROM pragma_table_info('fresh','main') ORDER BY cid;"
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(PragmaTables,'test_generated_'+str(i)+'_'+suffix,case(sql,mode,'CREATE TABLE fresh('+fields+');'))
if __name__=='__main__': unittest.main()
