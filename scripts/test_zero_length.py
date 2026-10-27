#!/usr/bin/env python3
"""Existing zero-length databases: lazy reads, first writes and transactions."""
import os
import random
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_pragma_tables import SQLITE,BINARY
from test_last_insert_rowid import snapshot
class ZeroLength(unittest.TestCase):pass
QUERIES={
 'empty':('',True),
 'select':('SELECT 1,NULL,typeof(1);',True),
 'schema':('SELECT count(*) FROM sqlite_schema;',True),
 'pragma':('PRAGMA user_version;PRAGMA application_id;',True),
 'transaction':('BEGIN;SELECT 1;ROLLBACK;',True),
 'savepoint':('SAVEPOINT a;SELECT 1;ROLLBACK TO a;RELEASE a;',True),
 'create':('CREATE TABLE t(x);',False),
 'insert':("CREATE TABLE t(id INTEGER PRIMARY KEY,x TEXT);INSERT INTO t VALUES(1,'árvíz 😀');SELECT * FROM t;",False),
 'rollback':('BEGIN;CREATE TABLE t(x);INSERT INTO t VALUES(1);ROLLBACK;SELECT count(*) FROM sqlite_schema;',True),
 'savepoint_write':('SAVEPOINT a;CREATE TABLE t(x);INSERT INTO t VALUES(1);ROLLBACK TO a;RELEASE a;SELECT count(*) FROM sqlite_schema;',False),
 'metadata':('PRAGMA user_version=123;PRAGMA application_id=456;PRAGMA user_version;PRAGMA application_id;',False),
 'unique_check':('CREATE TABLE t(x UNIQUE CHECK(x>0));INSERT INTO t VALUES(1),(2);SELECT * FROM t;',False),
}
def case(sql,readonly,mode,initial=b''):
 def test(self):
  with tempfile.TemporaryDirectory(prefix='sqleanite-zero-length-') as d:
   left=Path(d)/'lean.db';right=Path(d)/'sqlite.db'
   left.write_bytes(initial);right.write_bytes(initial)
   l=subprocess.run([str(BINARY),mode,str(left)],input=sql,text=True,capture_output=True,timeout=30)
   r=subprocess.run([SQLITE,'-batch','-bail',str(right)],input=sql,text=True,capture_output=True,timeout=30)
   self.assertEqual((l.returncode,l.stdout),(r.returncode,r.stdout),l.stderr+' / '+r.stderr)
   self.assertEqual(snapshot(left),snapshot(right))
   if readonly:
    self.assertEqual(right.read_bytes(),initial)
    self.assertEqual(left.read_bytes(),initial,'Read-only/rolled-back opening materialized the empty file')
 return test
for name,(sql,readonly) in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(ZeroLength,'test_'+name+'_'+suffix,case(sql,readonly,mode))
rng=random.Random(int(os.environ.get('SQLEANITE_ZERO_LENGTH_SEED','364001')))
for i in range(12):
 n=rng.randrange(1,12);base=rng.randrange(-10000,10000)
 sql='CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES'+','.join(f"({k+1},'{base+k}é')" for k in range(n))+';SELECT * FROM t ORDER BY id;'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(ZeroLength,'test_fresh_'+str(i)+'_'+suffix,case(sql,False,mode))
def invalid_case(contents,mode):
 def test(self):
  with tempfile.TemporaryDirectory(prefix='sqleanite-short-file-') as d:
   left=Path(d)/'lean.db';right=Path(d)/'sqlite.db'
   left.write_bytes(contents);right.write_bytes(contents)
   l=subprocess.run([str(BINARY),mode,str(left)],input='SELECT * FROM sqlite_schema;',text=True,capture_output=True,timeout=30)
   r=subprocess.run([SQLITE,'-batch','-bail',str(right)],input='SELECT * FROM sqlite_schema;',text=True,capture_output=True,timeout=30)
   self.assertNotEqual(r.returncode,0)
   self.assertNotEqual(l.returncode,0,l.stdout)
   self.assertEqual(left.read_bytes(),contents)
   self.assertEqual(right.read_bytes(),contents)
 return test
for byte in [0,65,255]:
 for name in ['select','schema','create','insert','unique_check']:
  sql,readonly=QUERIES[name]
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(ZeroLength,'test_one_byte_'+str(byte)+'_'+name+'_'+suffix,case(sql,readonly,mode,bytes([byte])))
for length in [2,16,99,100,512,4096]:
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(ZeroLength,'test_invalid_'+str(length)+'_'+suffix,invalid_case(bytes(length),mode))
if __name__=='__main__':unittest.main()
