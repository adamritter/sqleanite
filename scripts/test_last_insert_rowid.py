#!/usr/bin/env python3
"""Compare connection rowid registers against the pinned SQLite executable."""
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SQLITE = os.environ.get('SQLITE3_BIN', 'sqlite3')
BINARY = ROOT / '.lake/build/bin/sqleanite'
SCRIPTS = {
 'initial': 'SELECT last_insert_rowid();',
 'explicit': 'INSERT INTO t VALUES(70,1);SELECT last_insert_rowid();',
 'automatic': 'INSERT INTO t(v) VALUES(1),(2);SELECT last_insert_rowid();',
 'descending': 'INSERT INTO t VALUES(90,1),(3,2),(-8,3);SELECT last_insert_rowid();',
 'zero': 'INSERT INTO t VALUES(0,1);SELECT last_insert_rowid();',
 'bounds': 'INSERT INTO t VALUES(9223372036854775807,1),(-9223372036854775808,2);SELECT last_insert_rowid();',
 'rollback': 'BEGIN;INSERT INTO t VALUES(70,1);ROLLBACK;SELECT last_insert_rowid();',
 'savepoint': 'SAVEPOINT a;INSERT INTO t VALUES(70,1);ROLLBACK TO a;RELEASE a;SELECT last_insert_rowid();',
 'update_rowid': 'INSERT INTO t VALUES(70,1);UPDATE t SET id=90;SELECT last_insert_rowid();',
 'update_expression': 'INSERT INTO t VALUES(70,1);UPDATE t SET id=id+1,v=last_insert_rowid() RETURNING id,v,last_insert_rowid();SELECT last_insert_rowid();',
 'delete': 'INSERT INTO t VALUES(70,1);DELETE FROM t;SELECT last_insert_rowid();',
 'ignore': 'INSERT INTO t VALUES(70,1),(5,2);INSERT OR IGNORE INTO t VALUES(70,3);SELECT last_insert_rowid();',
 'replace': 'INSERT INTO t VALUES(70,1),(5,2);INSERT OR REPLACE INTO t VALUES(70,3);SELECT last_insert_rowid();',
 'empty_insert': 'INSERT INTO t VALUES(70,1);INSERT INTO t SELECT 4,1 WHERE 0;SELECT last_insert_rowid();',
 'insert_select': 'INSERT INTO t VALUES(70,1);INSERT INTO t SELECT id-100,last_insert_rowid() FROM t;SELECT last_insert_rowid();',
 'input_sequence': 'INSERT INTO t VALUES(50,0);INSERT INTO t VALUES(3,last_insert_rowid()),(2,last_insert_rowid());SELECT * FROM t ORDER BY id;',
 'input_returning': 'INSERT INTO t VALUES(50,0);INSERT INTO t VALUES(3,last_insert_rowid()),(2,last_insert_rowid()) RETURNING id,v,last_insert_rowid();',
 'returning': 'INSERT INTO t VALUES(80,1),(4,2) RETURNING id,last_insert_rowid();SELECT last_insert_rowid();',
 'ignore_returning': 'INSERT INTO t VALUES(80,1);INSERT OR IGNORE INTO t VALUES(80,2),(5,3) RETURNING id,last_insert_rowid();SELECT last_insert_rowid();',
 'auto': 'CREATE TABLE a(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO a VALUES(80,1);SELECT last_insert_rowid();INSERT INTO a(v) VALUES(2);SELECT last_insert_rowid();',
 'auto_empty': 'INSERT INTO t VALUES(80,1);CREATE TABLE a(id INTEGER PRIMARY KEY AUTOINCREMENT);INSERT INTO a SELECT 1 WHERE 0;SELECT last_insert_rowid();',
 'auto_returning': 'CREATE TABLE a(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO a(v) VALUES(1),(last_insert_rowid()) RETURNING id,v,last_insert_rowid();SELECT last_insert_rowid();',
 'auto_stream': 'CREATE TABLE a(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO a(v) VALUES(1),(last_insert_rowid());SELECT * FROM a;SELECT last_insert_rowid();',
 'hidden_rowid': 'CREATE TABLE a(v);INSERT INTO a(rowid,v) VALUES(80,1),(4,2);SELECT last_insert_rowid();',
 'ctas': 'INSERT INTO t VALUES(80,1);CREATE TABLE a AS SELECT * FROM t;SELECT last_insert_rowid();',
 'derived': 'INSERT INTO t VALUES(80,1);SELECT last_insert_rowid(),x FROM (SELECT 4 AS x);SELECT last_insert_rowid();',
 'cte': 'INSERT INTO t VALUES(80,1);WITH c(x) AS (VALUES(1),(2)) SELECT last_insert_rowid(),x FROM c;SELECT last_insert_rowid();',
 'recursive': 'INSERT INTO t VALUES(80,1);WITH RECURSIVE c(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM c WHERE x<3) SELECT last_insert_rowid(),x FROM c;',
 'multiple_tables': 'CREATE TABLE a(v);INSERT INTO t VALUES(80,1);INSERT INTO a VALUES(1);SELECT last_insert_rowid();',
 'nested': 'INSERT INTO t VALUES(80,1);SELECT CASE WHEN last_insert_rowid()=80 THEN last_insert_rowid()+1 ELSE 0 END;',
}

STREAM_SETUP = 'CREATE TABLE src(k INTEGER);INSERT INTO src VALUES(1),(2),(3);INSERT INTO t VALUES(50,0);'
SCRIPTS.update({
 'stream_select': STREAM_SETUP+'INSERT INTO t SELECT k,last_insert_rowid() FROM src;SELECT * FROM t ORDER BY id;',
 'stream_predicate': STREAM_SETUP+'INSERT INTO t SELECT k,last_insert_rowid() FROM src WHERE last_insert_rowid()>k;SELECT * FROM t ORDER BY id;',
 'stream_limit': STREAM_SETUP+'INSERT INTO t SELECT k,last_insert_rowid() FROM src LIMIT 2 OFFSET 1;SELECT * FROM t ORDER BY id;',
 'stream_ignore': STREAM_SETUP+'INSERT INTO t VALUES(2,99);INSERT OR IGNORE INTO t SELECT k,last_insert_rowid() FROM src;SELECT * FROM t ORDER BY id;',
 'stream_replace': STREAM_SETUP+'INSERT INTO t VALUES(2,99);INSERT OR REPLACE INTO t SELECT k,last_insert_rowid() FROM src;SELECT * FROM t ORDER BY id;',
 'stream_returning': STREAM_SETUP+'INSERT INTO t SELECT k,last_insert_rowid() FROM src RETURNING id,v,last_insert_rowid();',
 'stream_self': 'INSERT INTO t VALUES(1,2),(3,4);INSERT INTO t SELECT id+10,last_insert_rowid() FROM t;SELECT * FROM t ORDER BY id;',
 'stream_auto': STREAM_SETUP+'CREATE TABLE a(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO a(v) SELECT last_insert_rowid() FROM src;SELECT * FROM a;',
 'stream_alias': STREAM_SETUP+'INSERT INTO t SELECT s.k,last_insert_rowid() FROM src AS s;SELECT * FROM t ORDER BY id;',
 'stream_empty': STREAM_SETUP+'INSERT INTO t SELECT k,last_insert_rowid() FROM src WHERE 0;SELECT last_insert_rowid();',
})

class LastInsertRowid(unittest.TestCase):
    pass

def snapshot(path):
    catalog = subprocess.check_output([SQLITE,str(path),"SELECT type,name,tbl_name,sql FROM sqlite_schema ORDER BY type,name;"])
    tables = subprocess.check_output([SQLITE,str(path),"SELECT name FROM sqlite_schema WHERE type='table' ORDER BY name;"],text=True).splitlines()
    content = [catalog, subprocess.check_output([SQLITE,str(path),'PRAGMA integrity_check;'])]
    for table in tables:
        quoted = '"'+table.replace('"','""')+'"'
        content.append(subprocess.check_output([SQLITE,str(path),f'SELECT rowid,* FROM {quoted} ORDER BY rowid;']))
    return content

def case(sql, mode):
    def test(self):
        with tempfile.TemporaryDirectory(prefix='sqleanite-lastid-') as folder:
            left = Path(folder)/'lean.db'; right = Path(folder)/'sqlite.db'
            for path in (left,right):
                subprocess.run([SQLITE,str(path)],input='CREATE TABLE t(id INTEGER PRIMARY KEY,v INTEGER);',text=True,check=True,capture_output=True)
            lean = subprocess.run([str(BINARY),mode,str(left)],input=sql,text=True,capture_output=True,timeout=30)
            reference = subprocess.run([SQLITE,'-batch','-bail',str(right)],input=sql,text=True,capture_output=True,timeout=30)
            self.assertEqual(reference.returncode,0,reference.stderr)
            self.assertEqual(lean.returncode,0,lean.stderr)
            self.assertEqual(lean.stdout,reference.stdout)
            self.assertEqual(snapshot(left),snapshot(right))
    return test

rng = random.Random(int(os.environ.get('SQLEANITE_LASTID_SEED', '356735')))
for i in range(12):
    ids = rng.sample(range(-10000,10000),rng.randrange(2,10))
    rows = ','.join(f'({key},last_insert_rowid())' for key in ids)
    returning = ' RETURNING id,v,last_insert_rowid()' if i%2 else ''
    SCRIPTS['generated_'+str(i)] = f'INSERT INTO t VALUES{rows}{returning};SELECT last_insert_rowid();BEGIN;UPDATE t SET id=id+30000;ROLLBACK;SELECT last_insert_rowid();SELECT * FROM t ORDER BY id;'
for name,sql in SCRIPTS.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(LastInsertRowid,'test_'+name+'_'+suffix,case(sql,mode))
if __name__ == '__main__':
    unittest.main()
