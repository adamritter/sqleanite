#!/usr/bin/env python3
"""Generated INSERT keeps SQL target provenance separate from physical slots."""
import os
import random
import unittest
from test_check_add_column import case

class GeneratedInsertTargets(unittest.TestCase):
    pass

SETUP='CREATE TABLE g(a,b AS(a+1) STORED);'
QUERIES={
    'implicit_select_wide': 'INSERT INTO g SELECT 1,2;',
    'explicit_select_wide': 'INSERT INTO g(a) SELECT 1,2;',
    'implicit_values_wide': 'INSERT INTO g VALUES(1,2);',
    'explicit_values_wide': 'INSERT INTO g(a) VALUES(1,2);',
    'implicit_derived_wide': 'INSERT INTO g SELECT * FROM (VALUES(1,2));',
    'explicit_derived_wide': 'INSERT INTO g(a) SELECT * FROM (VALUES(1,2));',
    'implicit_values_compound_wide': 'INSERT INTO g VALUES(1,2) UNION ALL VALUES(3,4);',
    'explicit_values_compound_wide': 'INSERT INTO g(a) VALUES(1,2) UNION ALL VALUES(3,4);',
    'implicit_select_empty_wide': 'INSERT INTO g SELECT 1,2 WHERE 0;',
    'explicit_select_empty_wide': 'INSERT INTO g(a) SELECT 1,2 WHERE 0;',
    'implicit_select_narrow': 'INSERT INTO g SELECT 1;SELECT * FROM g;',
    'explicit_select_narrow': 'INSERT INTO g(a) SELECT 1;SELECT * FROM g;',
    'implicit_values_narrow': 'INSERT INTO g VALUES(1);SELECT * FROM g;',
    'explicit_values_narrow': 'INSERT INTO g(a) VALUES(1);SELECT * FROM g;',
    'implicit_default': 'INSERT INTO g DEFAULT VALUES;SELECT * FROM g;',
    'explicit_default': 'INSERT INTO g(a) DEFAULT VALUES;',
    'empty_bad_function': 'INSERT INTO g SELECT absent(1),2 WHERE 0;',
    'empty_bad_column': 'INSERT INTO g SELECT missing,2 WHERE 0;',
    'bad_function_values': 'INSERT INTO g VALUES(absent(1),2);',
    'unequal_values': 'INSERT INTO g VALUES(1),(2,3);',
    'duplicate_explicit': 'INSERT INTO g(a,a) VALUES(1,2);SELECT * FROM g;',
    'explicit_generated': 'INSERT INTO g(b) SELECT 1;',
    'explicit_rowid': 'INSERT INTO g(rowid,a) SELECT 9,2;SELECT rowid,* FROM g;',
}
for name,sql in QUERIES.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(GeneratedInsertTargets,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
EXTRA={
    'middle_implicit': ('CREATE TABLE g(a,b AS(a+1) STORED,c);','INSERT INTO g SELECT 1,2;SELECT * FROM g;'),
    'middle_implicit_wide': ('CREATE TABLE g(a,b AS(a+1) STORED,c);','INSERT INTO g SELECT 1,2,3;'),
    'auto_implicit_wide': ('CREATE TABLE g(id INTEGER PRIMARY KEY AUTOINCREMENT,b AS(id+1) STORED);','INSERT INTO g SELECT 1,2;'),
    'auto_explicit_wide': ('CREATE TABLE g(id INTEGER PRIMARY KEY AUTOINCREMENT,b AS(id+1) STORED);','INSERT INTO g(id) SELECT 1,2;'),
    'upsert_implicit_wide': ('CREATE TABLE g(a UNIQUE,b AS(a+1) STORED);','INSERT INTO g SELECT 1,2 WHERE 1 ON CONFLICT(a) DO NOTHING;'),
    'upsert_explicit_wide': ('CREATE TABLE g(a UNIQUE,b AS(a+1) STORED);','INSERT INTO g(a) SELECT 1,2 WHERE 1 ON CONFLICT(a) DO NOTHING;'),
    'returning_implicit_wide': (SETUP,'INSERT INTO g SELECT 1,2 RETURNING *;'),
    'returning_explicit_wide': (SETUP,'INSERT INTO g(a) SELECT 1,2 RETURNING *;'),
    'source_table_implicit': (SETUP+'CREATE TABLE s(x,y);INSERT INTO s VALUES(1,2);','INSERT INTO g SELECT * FROM s;'),
    'source_table_explicit': (SETUP+'CREATE TABLE s(x,y);INSERT INTO s VALUES(1,2);','INSERT INTO g(a) SELECT * FROM s;'),
    'source_function_implicit': (SETUP,"INSERT INTO g SELECT key,value FROM json_each('[1,2]');"),
    'ordinary_explicit': ('CREATE TABLE g(a);','INSERT INTO g(a) SELECT 1,2;'),
    'bound_value_not_public': (SETUP,"INSERT INTO g SELECT __sqlean_bound_value(1,'INTEGER');"),
    'ignored_scalar_order': (SETUP,'INSERT INTO g SELECT char(ORDER BY missing);SELECT * FROM g;'),
    'register_implicit': (SETUP+'CREATE TABLE s(x,y);INSERT INTO s VALUES(1,2);','INSERT INTO g SELECT last_insert_rowid(),x FROM s;'),
}
for name,(setup,sql) in EXTRA.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(GeneratedInsertTargets,'test_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_GENERATED_TARGETS_SEED','368401')))
for i in range(8):
    values=[rng.randrange(-10000,10000) for _ in range(rng.randrange(2,6))]
    sql='INSERT INTO g SELECT '+','.join(map(str,values))+';'
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(GeneratedInsertTargets,f'test_fresh_{i}_{suffix}',case(sql,mode,SETUP))
if __name__=='__main__':
    unittest.main()
