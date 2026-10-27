#!/usr/bin/env python3
"""Reference comparisons for connection counters in both public file modes."""
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
 'initial': 'SELECT changes(),total_changes();',
 'insert': 'INSERT INTO t VALUES(1,10),(2,20);SELECT changes(),total_changes();',
 'unchanged_update': 'INSERT INTO t VALUES(1,10),(2,20);UPDATE t SET v=v;SELECT changes(),total_changes();',
 'zero_update': 'INSERT INTO t VALUES(1,10);UPDATE t SET v=2 WHERE id=99;SELECT changes(),total_changes();',
 'delete': 'INSERT INTO t VALUES(1,10),(2,20);DELETE FROM t WHERE id=1;SELECT changes(),total_changes();',
 'rollback': 'BEGIN;INSERT INTO t VALUES(1,10);ROLLBACK;SELECT changes(),total_changes();',
 'savepoint': 'SAVEPOINT a;INSERT INTO t VALUES(1,10);ROLLBACK TO a;RELEASE a;SELECT changes(),total_changes();',
 'ddl': 'INSERT INTO t VALUES(1,10);CREATE TABLE other(v);SELECT changes(),total_changes();',
 'ctas': 'INSERT INTO t VALUES(1,10),(2,20);CREATE TABLE other AS SELECT * FROM t;SELECT changes(),total_changes();',
 'nested': 'INSERT INTO t VALUES(1,10);SELECT CASE WHEN changes()=1 THEN total_changes()+10 ELSE 0 END;',
 'projection': 'INSERT INTO t VALUES(1,10),(2,20);SELECT id,changes(),total_changes() FROM t ORDER BY id;',
 'predicate': 'INSERT INTO t VALUES(1,10);SELECT id FROM t WHERE changes()=1;',
 'insert_expression': 'INSERT INTO t VALUES(1,10);INSERT INTO t VALUES(2,changes()+total_changes());SELECT * FROM t ORDER BY id;',
 'update_expression': 'INSERT INTO t VALUES(1,10);UPDATE t SET v=changes()+total_changes();SELECT * FROM t;',
 'insert_select': 'INSERT INTO t VALUES(1,10);INSERT INTO t SELECT 2,changes();SELECT changes(),total_changes();',
 'returning': 'INSERT INTO t VALUES(1,10);UPDATE t SET v=11 RETURNING changes(),total_changes();SELECT changes(),total_changes();',
 'replace': 'INSERT INTO t VALUES(1,10);INSERT OR REPLACE INTO t VALUES(1,20);SELECT changes(),total_changes();',
 'commit': 'BEGIN;INSERT INTO t VALUES(1,10);COMMIT;SELECT changes(),total_changes();',
}
class ConnectionCounters(unittest.TestCase):
    pass

def case(sql, mode):
    def test(self):
        with tempfile.TemporaryDirectory(prefix='sqleanite-counters-') as folder:
            left = Path(folder)/'lean.db'; right = Path(folder)/'sqlite.db'
            for path in [left,right]:
                subprocess.run([SQLITE,str(path)],input='CREATE TABLE t(id INTEGER PRIMARY KEY,v INTEGER);',text=True,check=True,capture_output=True)
            lean = subprocess.run([str(BINARY),mode,str(left)],input=sql,text=True,capture_output=True,timeout=30)
            reference = subprocess.run([SQLITE,'-batch','-bail',str(right)],input=sql,text=True,capture_output=True,timeout=30)
            self.assertEqual(reference.returncode,0,reference.stderr)
            self.assertEqual(lean.returncode,0,lean.stderr)
            self.assertEqual(lean.stdout,reference.stdout)
            observation='PRAGMA integrity_check;SELECT * FROM t ORDER BY id;'
            self.assertEqual(subprocess.check_output([SQLITE,str(left),observation]),subprocess.check_output([SQLITE,str(right),observation]))
    return test
# Fresh generated sequences vary row counts, values, no-op updates and rollbacks.
rng = random.Random(int(os.environ.get('SQLEANITE_COUNTER_SEED', '356318')))
for i in range(10):
    n = rng.randrange(1,9)
    rows = ','.join(f'({k},{rng.randrange(-10000,10000)})' for k in range(1,n+1))
    statements = [f'INSERT INTO t VALUES{rows};', 'SELECT changes(),total_changes();',
                  'BEGIN;', f'UPDATE t SET v=v+1 WHERE id<={rng.randrange(n+1)};',
                  'SELECT changes(),total_changes();', 'ROLLBACK;',
                  'SELECT changes(),total_changes();',
                  f'DELETE FROM t WHERE id>{rng.randrange(n+1)};',
                  'SELECT changes(),total_changes();']
    SCRIPTS['generated_'+str(i)] = ''.join(statements)
for name,sql in SCRIPTS.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(ConnectionCounters,'test_'+name+'_'+suffix,case(sql,mode))
if __name__ == '__main__':
    unittest.main()
