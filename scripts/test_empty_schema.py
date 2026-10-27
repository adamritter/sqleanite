#!/usr/bin/env python3
"""SQLite-created empty schemas may have the legitimate encoding marker zero."""
import os
from contextlib import ExitStack
import select
import time
from pathlib import Path
import random
import subprocess
import tempfile
import unittest
from test_pragma_tables import case, SQLITE, BINARY
from test_last_insert_rowid import snapshot
class EmptySchema(unittest.TestCase): pass
READ='SELECT 42;PRAGMA user_version;PRAGMA application_id;SELECT count(*) FROM sqlite_schema;'
WRITE='CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,\'árvíz 😀\');SELECT * FROM t;PRAGMA user_version;PRAGMA application_id;'
SCRIPTS={'read':READ,'create':WRITE,'unique':"CREATE TABLE t(x TEXT UNIQUE);INSERT INTO t VALUES('a'),('b');SELECT * FROM t ORDER BY x;",'rollback':'BEGIN;CREATE TABLE t(x);ROLLBACK;SELECT count(*) FROM sqlite_schema;','commit':'BEGIN;CREATE TABLE t(x);INSERT INTO t VALUES(5);COMMIT;SELECT * FROM t;','metadata':'PRAGMA user_version=23;PRAGMA application_id=41;'+READ}
for page in (512,1024,2048,4096,8192,16384,32768,65536):
 for name,sql in SCRIPTS.items():
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setup=f'PRAGMA page_size={page};PRAGMA user_version=7;PRAGMA application_id=99;'
   setattr(EmptySchema,f'test_{page}_{name}_{suffix}',case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_EMPTY_SCHEMA_SEED','359000')))
for i in range(12):
 setup=f'PRAGMA user_version={rng.randrange(1,100000)};PRAGMA application_id={rng.randrange(1,100000)};'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(EmptySchema,f'test_fresh_{i}_{suffix}',case(WRITE,mode,setup))
def existing_case(sql, mode, populated=False, wal=False):
 def test(self):
  with tempfile.TemporaryDirectory(prefix='sqleanite-zero-encoding-') as folder, ExitStack() as stack:
   paths=[Path(folder)/'lean.db',Path(folder)/'sqlite.db']
   for path in paths:
    setup="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,'árvíz 😀');" if populated else 'PRAGMA user_version=17;'
    subprocess.run([SQLITE,str(path)],input=setup,text=True,capture_output=True,check=True)
    data=bytearray(path.read_bytes());data[56:60]=bytes(4);path.write_bytes(data)
    if wal:
     keeper=subprocess.Popen([SQLITE,'-batch','-bail',str(path)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
     def close(keeper=keeper):
      keeper.stdin.close()
      try: keeper.wait(timeout=5)
      except subprocess.TimeoutExpired: keeper.kill();keeper.wait()
      keeper.stdout.close();keeper.stderr.close()
     stack.callback(close)
     keeper.stdin.write(b"PRAGMA journal_mode=WAL;PRAGMA user_version=18;\n.print ready\n");keeper.stdin.flush()
     output=b'';deadline=time.monotonic()+5
     while b'ready' not in output:
      remaining=deadline-time.monotonic()
      self.assertGreater(remaining,0,'SQLite WAL fixture did not become ready')
      ready,_,_=select.select([keeper.stdout],[],[],remaining)
      self.assertTrue(ready,'SQLite WAL fixture timed out')
      chunk=os.read(keeper.stdout.fileno(),4096)
      self.assertTrue(chunk,'SQLite WAL fixture exited')
      output+=chunk
     raw=Path(str(path)+'-wal').read_bytes()
     page_size=int.from_bytes(raw[8:12],'big')
     headers=[raw[i+24:i+24+page_size] for i in range(32,len(raw),24+page_size) if int.from_bytes(raw[i:i+4],'big')==1]
     self.assertTrue(headers,'fixture has no WAL header frame')
     self.assertEqual(int.from_bytes(headers[-1][56:60],'big'),0,'fixture lost zero encoding marker')
   left,right=paths
   lean=subprocess.run([str(BINARY),mode,str(left)],input=sql,text=True,capture_output=True,timeout=30)
   ref=subprocess.run([SQLITE,'-batch','-bail',str(right)],input=sql,text=True,capture_output=True,timeout=30)
   self.assertEqual(ref.returncode,0,ref.stderr)
   self.assertEqual(lean.returncode,0,lean.stderr)
   self.assertEqual(lean.stdout,ref.stdout)
   self.assertEqual(snapshot(left),snapshot(right))
 return test
for populated in (False,True):
 queries={'read':READ,'metadata':'PRAGMA user_version=123;'+READ}
 if populated:
  queries.update({'rows':'SELECT * FROM t;','insert':"INSERT INTO t VALUES(2,'új');SELECT * FROM t ORDER BY id;",'update':"UPDATE t SET v='más';SELECT * FROM t;"})
 else:queries.update({'create':WRITE,'rollback':SCRIPTS['rollback'],'unique':SCRIPTS['unique']})
 for name,sql in queries.items():
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(EmptySchema,f'test_existing_{populated}_{name}_{suffix}',existing_case(sql,mode,populated))
  setattr(EmptySchema,f'test_live_wal_{populated}_{name}',existing_case(sql,'--verified-wal-file',populated,wal=True))
if __name__=='__main__':unittest.main()
