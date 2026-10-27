#!/usr/bin/env python3
"""UPDATE only reevaluates CHECK predicates that reference assigned columns."""
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
if __name__=='__main__':unittest.main()
