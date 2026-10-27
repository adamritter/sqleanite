#!/usr/bin/env python3
"""UPDATE only reevaluates CHECK predicates that reference assigned columns."""
import os
import random
import unittest
from test_pragma_tables import case
class CheckDependencies(unittest.TestCase): pass
SETUP='CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(1,-1,0);'
QUERIES={
 'constant':'UPDATE t SET y=5;SELECT * FROM t;',
 'expression':'UPDATE t SET y=y+5;SELECT * FROM t;',
 'returning':'UPDATE t SET y=5 RETURNING *;',
 'ignore':'UPDATE OR IGNORE t SET y=5;SELECT * FROM t;',
 'replace':'UPDATE OR REPLACE t SET y=5;SELECT * FROM t;',
 'rowid':'UPDATE t SET id=2;SELECT * FROM t;',
 'upsert':'INSERT INTO t VALUES(1,1,1) ON CONFLICT(id) DO UPDATE SET y=5;SELECT * FROM t;',
 'same_column':'UPDATE t SET x=x;',
 'no_rows':'UPDATE t SET y=5 WHERE 0;SELECT * FROM t;',
}
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(CheckDependencies,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
EXTRA={
 'folded_missing': ('CREATE TABLE t(y);', 'CREATE TABLE c(x CHECK(0 AND missing));INSERT INTO t VALUES(1);'),
 'folded_column': ('CREATE TABLE t(x CHECK(0 AND x));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(0);', 'UPDATE t SET x=1;SELECT * FROM t;'),
 'constant_check': ('CREATE TABLE t(x,y,CHECK(0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(0,0);', 'UPDATE t SET x=1,y=2;SELECT * FROM t;'),
 'multiple_unrelated': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y CHECK(y<0),z);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(1,-1,1,0);', 'UPDATE t SET z=7;SELECT * FROM t;'),
 'multiple_referenced': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y CHECK(y<0),z);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(1,-1,1,0);', 'UPDATE t SET x=2;SELECT * FROM t;'),
 'quoted': ('CREATE TABLE t("X X" CHECK("X X">0),y);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1,0);', 'UPDATE t SET y=1;SELECT * FROM t;'),
 'quoted_self': ('CREATE TABLE t("X X" CHECK("X X">0),y);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1,0);', 'UPDATE t SET "X X"="X X";'),
 'qualified': ('CREATE TABLE t(x,y,CHECK(t.x>0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1,0);', 'UPDATE t SET y=1;SELECT * FROM t;'),
 'rowid_reorder': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(1,-1,0),(2,-2,0),(3,-3,0);', 'UPDATE t SET id=id+10;SELECT * FROM t ORDER BY id;'),
 'rowid_check': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x,CHECK(_rowid_>0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1,0);', 'UPDATE t SET x=2;SELECT * FROM t;'),
 'rowid_check_self': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x,CHECK(_rowid_>0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1,0);', 'UPDATE t SET id=id;'),
 'unique_replace': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y UNIQUE);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(1,-1,10),(2,2,20);', 'UPDATE OR REPLACE t SET y=20 WHERE id=1;SELECT * FROM t;'),
 'unique_ignore': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y UNIQUE);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(1,-1,10),(2,2,20);', 'UPDATE OR IGNORE t SET y=20 WHERE id=1;SELECT * FROM t;'),
 'unique_abort': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y UNIQUE);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(1,-1,10),(2,2,20);', 'UPDATE t SET y=20 WHERE id=1;'),
 'rowid_replace': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(1,-1,10),(2,2,20);', 'UPDATE OR REPLACE t SET id=2 WHERE id=1;SELECT * FROM t;'),
 'default_replace': ('CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>0),y NOT NULL DEFAULT 7);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(1,-1,10);', 'UPDATE OR REPLACE t SET y=NULL;SELECT * FROM t;'),
 'upsert_abort': (SETUP, 'INSERT OR IGNORE INTO t VALUES(1,1,1) ON CONFLICT(id) DO UPDATE SET x=x;'),
 'counters': (SETUP, 'UPDATE t SET id=2 RETURNING *;SELECT changes(),total_changes(),last_insert_rowid();'),
 'rollback': (SETUP, 'BEGIN;UPDATE t SET y=5;ROLLBACK;SELECT * FROM t;'),
 'savepoint': (SETUP, 'SAVEPOINT a;UPDATE t SET id=9;ROLLBACK TO a;RELEASE a;SELECT * FROM t;'),
}
for name,(setup,sql) in EXTRA.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(CheckDependencies,'test_extra_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_CHECK_DEPENDENCIES_SEED','362001')))
for i in range(12):
 threshold=rng.randrange(-100,100);bad=threshold-rng.randrange(1,100);n=rng.randrange(1,8);delta=rng.randrange(1,1000)
 setup=f'CREATE TABLE t(id INTEGER PRIMARY KEY,x CHECK(x>{threshold}),y);PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES'+','.join(f'({j+1},{bad-j},0)' for j in range(n))+';'
 sql=f'UPDATE t SET id=id+{n+delta},y={delta};SELECT * FROM t ORDER BY id;SELECT changes(),total_changes(),last_insert_rowid();'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(CheckDependencies,'test_fresh_'+str(i)+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
