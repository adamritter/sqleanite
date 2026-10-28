#!/usr/bin/env python3
"""Generated-column ALTER validation, unchanged catalogs and diagnostic order."""
import os
import random
import unittest
from test_check_add_column import case

class GeneratedColumnDDL(unittest.TestCase):
    pass

CASES = {
    'populated_notnull': ('CREATE TABLE g(a);INSERT INTO g VALUES(1);', 'ALTER TABLE g ADD b AS(a+1) STORED NOT NULL;'),
    'populated_unique': ('CREATE TABLE g(a);INSERT INTO g VALUES(1);', 'ALTER TABLE g ADD b AS(a+1) STORED UNIQUE;'),
    'empty_unique': ('CREATE TABLE g(a);', 'ALTER TABLE g ADD b AS(a+1) STORED UNIQUE;'),
    'empty_primary': ('CREATE TABLE g(a);', 'ALTER TABLE g ADD b AS(a+1) STORED PRIMARY KEY;'),
    'populated_primary': ('CREATE TABLE g(a);INSERT INTO g VALUES(1);', 'ALTER TABLE g ADD b AS(a+1) STORED PRIMARY KEY;'),
    'primary_before_as': ('CREATE TABLE g(a);', 'ALTER TABLE g ADD b PRIMARY KEY AS(a+1) STORED;'),
    'populated_unknown_notnull': ('CREATE TABLE g(a);INSERT INTO g VALUES(1);', 'ALTER TABLE g ADD b AS(missing) STORED NOT NULL;'),
    'populated_random': ('CREATE TABLE g(a);INSERT INTO g VALUES(1);', 'ALTER TABLE g ADD b AS(random()) STORED;'),
    'empty_random': ('CREATE TABLE g(a);', 'ALTER TABLE g ADD b AS(random()) STORED;'),
    'empty_notnull': ('CREATE TABLE g(a);', 'ALTER TABLE g ADD b AS(a+1) STORED NOT NULL;INSERT INTO g(a) VALUES(3);SELECT * FROM g;'),
    'populated_duplicate': ('CREATE TABLE g(a);INSERT INTO g VALUES(1);', 'ALTER TABLE g ADD a AS(a+1) STORED NOT NULL;'),
    'duplicate_primary': ('CREATE TABLE g(a);', 'ALTER TABLE g ADD a AS(a+1) STORED PRIMARY KEY;'),
    'drop_last_ordinary': ('CREATE TABLE g(a,b AS(1) STORED);', 'ALTER TABLE g DROP a;'),
    'drop_last_ordinary_chain': ('CREATE TABLE g(a,b AS(1) STORED,c AS(b+1) STORED);INSERT INTO g(a)VALUES(2);', 'ALTER TABLE g DROP a;'),
    'drop_last_primary': ('CREATE TABLE g(a INTEGER PRIMARY KEY,b AS(1) STORED);', 'ALTER TABLE g DROP a;'),
    'drop_referenced': ('CREATE TABLE g(a,b AS(a+1) STORED);', 'ALTER TABLE g DROP a;'),
    'drop_generated': ('CREATE TABLE g(a,b AS(1) STORED);INSERT INTO g(a)VALUES(2);', 'ALTER TABLE g DROP b;INSERT INTO g VALUES(3);SELECT * FROM g;'),
    'rollback_add': ('CREATE TABLE g(a);', 'BEGIN;ALTER TABLE g ADD b AS(a+1) STORED;ROLLBACK;INSERT INTO g VALUES(3);SELECT * FROM g;'),
    'savepoint_add': ('CREATE TABLE g(a);', 'SAVEPOINT s;ALTER TABLE g ADD b AS(a+1) STORED;ROLLBACK TO s;RELEASE s;INSERT INTO g VALUES(3);SELECT * FROM g;'),
    'quoted_column': ('CREATE TABLE "odd table"("source name");INSERT INTO "odd table" VALUES(1);', 'ALTER TABLE "odd table" ADD "gen name" AS("source name"+1) STORED NOT NULL;'),
}
for name,(setup,sql) in CASES.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(GeneratedColumnDDL,'test_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_GENERATED_DDL_SEED','368201')))
for i in range(8):
    value=rng.randrange(-10000,10000);increment=rng.randrange(1,100)
    setup=f'CREATE TABLE g(a);INSERT INTO g VALUES({value});'
    sql=f'ALTER TABLE g ADD b AS(a+{increment}) STORED NOT NULL;'
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(GeneratedColumnDDL,f'test_fresh_{i}_{suffix}',case(sql,mode,setup))
if __name__=='__main__':
    unittest.main()
