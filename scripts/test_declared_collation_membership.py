#!/usr/bin/env python3
"""IN query operands retain explicit and declared collation priority separately."""
import os
import random
import unittest
from test_check_add_column import case

class DeclaredMembership(unittest.TestCase):
    pass

QUERIES={
    'literal': "SELECT 'A' IN (SELECT v FROM g WHERE rowid=1);",
    'literal_not': "SELECT 'A' NOT IN (SELECT v FROM g WHERE rowid=1);",
    'left_declared': 'SELECT rowid,v IN (SELECT w FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'left_binary': 'SELECT rowid,w IN (SELECT v FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'right_explicit': 'SELECT rowid,w IN (SELECT v COLLATE NOCASE FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'right_binary': 'SELECT rowid,v IN (SELECT w COLLATE BINARY FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'left_explicit': 'SELECT rowid,v COLLATE BINARY IN (SELECT w FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'both_explicit': 'SELECT rowid,v COLLATE BINARY IN (SELECT w COLLATE NOCASE FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'right_rtrim': 'SELECT rowid,w IN (SELECT v COLLATE RTRIM FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'right_parent': "SELECT rowid,'A' IN (SELECT v) FROM g ORDER BY rowid;",
    'right_qualified_parent': "SELECT rowid,'A' IN (SELECT g.v) FROM g ORDER BY rowid;",
    'right_literal': 'SELECT rowid,v IN (SELECT \'A\') FROM g ORDER BY rowid;',
    'right_empty': 'SELECT rowid,v IN (SELECT w FROM g WHERE 0) FROM g ORDER BY rowid;',
    'right_null': 'SELECT rowid,v IN (SELECT w FROM g WHERE rowid=1 UNION ALL SELECT NULL) FROM g ORDER BY rowid;',
    'scalar_default_absent': "SELECT (SELECT v FROM g WHERE rowid=1)='A';",
    'scalar_explicit_absent': "SELECT (SELECT v COLLATE NOCASE FROM g WHERE rowid=1)='A';",
    'scalar_outer_declared': 'SELECT rowid,v=(SELECT w FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'cast': 'SELECT rowid,CAST(v AS TEXT) IN (SELECT w FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'plus': 'SELECT rowid,+v IN (SELECT w FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
    'concat_loses': 'SELECT rowid,(v||\'\') IN (SELECT w FROM g WHERE rowid=1) FROM g ORDER BY rowid;',
}
for collation in ('NOCASE','RTRIM'):
    setup=f'CREATE TABLE g(v TEXT COLLATE {collation},w TEXT);'+"INSERT INTO g VALUES('a','A'),('A','a'),('b','B'),('a ','A '),(NULL,'X');"
    for name,sql in QUERIES.items():
        for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
            setattr(DeclaredMembership,'test_'+collation.lower()+'_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_DECLARED_MEMBERSHIP_SEED','369201')))
for i in range(8):
    values=[rng.choice(['a','A','b','B','a ']) for _ in range(rng.randrange(2,12))]
    setup='CREATE TABLE g(v TEXT COLLATE NOCASE);INSERT INTO g VALUES'+','.join("('"+v+"')" for v in values)+';'
    sql="SELECT 'A' IN (SELECT v FROM g);SELECT rowid,v IN (SELECT 'A') FROM g ORDER BY rowid;"
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(DeclaredMembership,f'test_fresh_{i}_{suffix}',case(sql,mode,setup))
if __name__=='__main__':
    unittest.main()
