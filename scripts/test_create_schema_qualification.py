#!/usr/bin/env python3
"""CREATE's explicit main qualifier, literal periods and retained names."""
import os
import random
import unittest
from test_check_add_column import case

class CreateSchemaQualification(unittest.TestCase):
    pass

QUERIES = {
    'ordinary': "CREATE TABLE main.t(id INTEGER PRIMARY KEY,x TEXT);INSERT INTO t VALUES(1,'v');PRAGMA table_info(t);",
    'strict': "CREATE TABLE main.t(id INTEGER PRIMARY KEY,x ANY) STRICT;INSERT INTO t VALUES(1,'003');SELECT x,typeof(x) FROM t;PRAGMA table_list(t);",
    'ctas': "CREATE TABLE main.t AS SELECT 3 AS x,'003' AS y;SELECT * FROM t;PRAGMA table_info(t);",
    'quoted_schema': 'CREATE TABLE "main".t(x);PRAGMA table_info(t);',
    'uppercase_schema': 'CREATE TABLE MAIN.t(x);PRAGMA table_info(t);',
    'quoted_target': 'CREATE TABLE main."a.b"(x);INSERT INTO "a.b" VALUES(3);SELECT * FROM "a.b";',
    'single_quoted_schema': "CREATE TABLE 'main'.t(x);PRAGMA table_info(t);",
    'single_quoted_target': "CREATE TABLE main.'a.b'(x);PRAGMA table_info('a.b');",
    'trivia': 'CREATE /* a */ TABLE /* b */ "main" /* c */ . /* d */ "T" (x);PRAGMA table_info(T);',
    'if_not_exists': 'CREATE TABLE t(x);CREATE TABLE IF NOT EXISTS main.t(y);PRAGMA table_info(t);',
    'strict_if_not_exists': 'CREATE TABLE t(x);CREATE TABLE IF NOT EXISTS main.t(y FLOAT) STRICT;PRAGMA table_info(t);',
    'ctas_if_not_exists': 'CREATE TABLE t(x);CREATE TABLE IF NOT EXISTS main.t AS SELECT missing_function();PRAGMA table_info(t);',
    'duplicate': 'CREATE TABLE t(x);CREATE TABLE main.t(y);',
    'duplicate_quoted': 'CREATE TABLE t(x);CREATE TABLE main."t"(y);',
    'literal_period': 'CREATE TABLE "main.t"(x);INSERT INTO "main.t" VALUES(3);SELECT * FROM "main.t";',
    'literal_distinct': 'CREATE TABLE "main.t"(x);CREATE TABLE main.t(y);INSERT INTO "main.t" VALUES(3);INSERT INTO t VALUES(4);SELECT name FROM sqlite_schema WHERE type=\'table\' ORDER BY name;',
    'literal_main': 'CREATE TABLE main(x);CREATE TABLE main.t(y);PRAGMA table_info(main);PRAGMA table_info(t);',
    'foreign_key': 'CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);PRAGMA foreign_keys=ON;CREATE TABLE main.t(x REFERENCES p(id));INSERT INTO t VALUES(1);PRAGMA foreign_key_list(t);',
    'foreign_key_bad': 'CREATE TABLE p(id INTEGER PRIMARY KEY);PRAGMA foreign_keys=ON;CREATE TABLE main.t(x REFERENCES p(id));INSERT INTO t VALUES(99);',
    'table_foreign_key': 'CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE main.t(x,FOREIGN KEY(x) REFERENCES p(id));PRAGMA foreign_key_list(t);',
    'check': 'CREATE TABLE main.t(x CHECK(x>0));INSERT INTO t VALUES(-1);',
    'unique': 'CREATE TABLE main.t(x UNIQUE);INSERT INTO t VALUES(1);INSERT INTO t VALUES(1);',
    'auto': 'CREATE TABLE main.t(id INTEGER PRIMARY KEY AUTOINCREMENT,x);INSERT INTO t(x) VALUES(3);PRAGMA table_list;',
    'alter_after_create': 'CREATE TABLE main.t(x);ALTER TABLE main.t RENAME TO renamed;PRAGMA table_info(renamed);',
    'unknown_schema': 'CREATE TABLE missing.t(x);',
    'unknown_quoted_schema': 'CREATE TABLE "missing".t(x);',
    'unknown_single_schema': "CREATE TABLE 'missing'.t(x);",
    'unknown_strict_schema': 'CREATE TABLE missing.t(x INT) STRICT;',
}
for name,sql in QUERIES.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(CreateSchemaQualification,'test_'+name+'_'+suffix,case(sql,mode,''))
rng=random.Random(int(os.environ.get('SQLEANITE_CREATE_SCHEMA_SEED','367001')))
for i in range(12):
    value=rng.randrange(1,100000)
    name='table_'+str(rng.randrange(100000))
    sql=f'CREATE TABLE "main"."{name}"(x INTEGER);INSERT INTO "{name}" VALUES({value});SELECT * FROM "{name}";'
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(CreateSchemaQualification,f'test_fresh_{i}_{suffix}',case(sql,mode,''))
if __name__=='__main__':
    unittest.main()
