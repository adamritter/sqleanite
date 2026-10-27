#!/usr/bin/env python3
"""Foreign-key inspection PRAGMAs and their SQL table functions."""
import os
import random
import unittest
from test_check_add_column import case

class ForeignKeyPragmas(unittest.TestCase):
    pass

SETUP = '''CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1),(2);
CREATE TABLE c(id INTEGER PRIMARY KEY,a REFERENCES p(id),b REFERENCES p);
INSERT INTO c VALUES(1,1,2),(2,99,NULL),(3,NULL,88),(4,77,66);CREATE TABLE empty(x);'''
QUERIES = {
    'list': 'PRAGMA foreign_key_list(c);',
    'list_main': 'PRAGMA main.foreign_key_list(c);',
    'list_temp': 'PRAGMA temp.foreign_key_list(c);',
    'list_empty': 'PRAGMA foreign_key_list(empty);',
    'list_missing': 'PRAGMA foreign_key_list(missing);',
    'list_noarg': 'PRAGMA foreign_key_list;',
    'list_unknown_schema': 'PRAGMA missing.foreign_key_list(c);',
    'list_function': "SELECT * FROM pragma_foreign_key_list('c');",
    'list_function_main': "SELECT * FROM pragma_foreign_key_list('c','main');",
    'list_function_temp': "SELECT * FROM pragma_foreign_key_list('c','temp');",
    'list_function_missing_schema': "SELECT * FROM pragma_foreign_key_list('c','missing');",
    'list_function_null': 'SELECT * FROM pragma_foreign_key_list(NULL);',
    'list_function_noarg': 'SELECT * FROM pragma_foreign_key_list();',
    'list_function_hidden': "SELECT id,arg,schema,_rowid_ FROM pragma_foreign_key_list('c') ORDER BY id;",
    'list_function_fields': "SELECT id,\"table\",\"from\",\"to\",on_update,on_delete,\"match\" FROM pragma_foreign_key_list('c') ORDER BY id;",
    'list_join': "SELECT f.\"from\",i.name FROM pragma_foreign_key_list('c') f JOIN pragma_table_info('c') i ON f.\"from\"=i.name ORDER BY f.id;",
    'list_derived': "WITH f AS (SELECT * FROM pragma_foreign_key_list('c')) SELECT count(*) FROM f;",
    'list_arity': "SELECT * FROM pragma_foreign_key_list('c','main',0);",
    'check': 'PRAGMA foreign_key_check;',
    'check_table': 'PRAGMA foreign_key_check(c);',
    'check_parent': 'PRAGMA foreign_key_check(p);',
    'check_empty': 'PRAGMA foreign_key_check(empty);',
    'check_missing': 'PRAGMA foreign_key_check(missing);',
    'check_main': 'PRAGMA main.foreign_key_check(c);',
    'check_temp': 'PRAGMA temp.foreign_key_check;',
    'check_temp_missing': 'PRAGMA temp.foreign_key_check(c);',
    'check_enabled': 'PRAGMA foreign_keys=ON;PRAGMA foreign_key_check(c);',
    'check_function': "SELECT * FROM pragma_foreign_key_check('c');",
    'check_function_all': 'SELECT * FROM pragma_foreign_key_check();',
    'check_function_null': 'SELECT * FROM pragma_foreign_key_check(NULL);',
    'check_function_main': "SELECT * FROM pragma_foreign_key_check('c','main');",
    'check_function_hidden': "SELECT rowid,_rowid_,arg,schema FROM pragma_foreign_key_check('c');",
    'check_filter': "SELECT rowid,\"parent\" FROM pragma_foreign_key_check('c') WHERE fkid=1 ORDER BY rowid DESC;",
    'check_aggregate': "SELECT count(*),sum(rowid) FROM pragma_foreign_key_check('c');",
    'check_arity': "SELECT * FROM pragma_foreign_key_check('c','main',0);",
}
for name, sql in QUERIES.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(ForeignKeyPragmas, 'test_' + name + '_' + suffix, case(sql, mode, SETUP))
EXTRA = {
    'create_then_check': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c0(x REFERENCES p(id));INSERT INTO c0 VALUES(1);CREATE TABLE c1(x REFERENCES p(id));INSERT INTO c1 VALUES(2);CREATE TABLE c2(x REFERENCES p(id));INSERT INTO c2 VALUES(3);', 'CREATE TABLE c3(x REFERENCES p(id));INSERT INTO c3 VALUES(99);PRAGMA foreign_key_check;'),
    'drop_then_check': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c0(x REFERENCES p(id));INSERT INTO c0 VALUES(1);CREATE TABLE c1(x REFERENCES p(id));INSERT INTO c1 VALUES(2);CREATE TABLE c2(x REFERENCES p(id));INSERT INTO c2 VALUES(3);', 'DROP TABLE c0;PRAGMA foreign_key_check;'),
    'transaction_create': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c0(x REFERENCES p(id));INSERT INTO c0 VALUES(1);CREATE TABLE c1(x REFERENCES p(id));INSERT INTO c1 VALUES(2);CREATE TABLE c2(x REFERENCES p(id));INSERT INTO c2 VALUES(3);', 'BEGIN;CREATE TABLE c3(x REFERENCES p(id));INSERT INTO c3 VALUES(99);PRAGMA foreign_key_check;ROLLBACK;PRAGMA foreign_key_check;'),
    'drop_create': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c0(x REFERENCES p(id));INSERT INTO c0 VALUES(1);CREATE TABLE c1(x REFERENCES p(id));INSERT INTO c1 VALUES(2);CREATE TABLE c2(x REFERENCES p(id));INSERT INTO c2 VALUES(3);', 'DROP TABLE c0;CREATE TABLE c4(x REFERENCES p(id));INSERT INTO c4 VALUES(44);PRAGMA foreign_key_check;'),
    'unicode_names': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE "Ä"(x REFERENCES p(id));INSERT INTO "Ä" VALUES(1);CREATE TABLE "ä"(x REFERENCES p(id));INSERT INTO "ä" VALUES(2);', 'PRAGMA foreign_key_check;'),
    'missing_parent_list': ('CREATE TABLE c(x REFERENCES missing(id));', 'PRAGMA foreign_key_list(c);'),
    'missing_parent_check': ('CREATE TABLE c(x REFERENCES missing(id));INSERT INTO c VALUES(1),(NULL);', 'PRAGMA foreign_key_check(c);'),
    'mismatch_list': ('CREATE TABLE p(x);CREATE TABLE c(y REFERENCES p(x));', 'PRAGMA foreign_key_list(c);'),
    'mismatch_check': ('CREATE TABLE p(x);CREATE TABLE c(y REFERENCES p(x));', 'PRAGMA foreign_key_check(c);'),
    'negative_rowid': ('CREATE TABLE p(x INTEGER PRIMARY KEY);CREATE TABLE c(y REFERENCES p(x));INSERT INTO c(rowid,y) VALUES(-7,99),(0,88);', 'PRAGMA foreign_key_check(c);'),
    'quoted_names': ('CREATE TABLE "P P"("X X" INTEGER PRIMARY KEY);CREATE TABLE "C C"("Y Y" REFERENCES "P P"("X X"));INSERT INTO "C C" VALUES(9);', 'PRAGMA foreign_key_list("C C");PRAGMA foreign_key_check("C C");'),
    'text_affinity': ("CREATE TABLE p(x TEXT PRIMARY KEY);INSERT INTO p VALUES('1');CREATE TABLE c(y REFERENCES p(x));INSERT INTO c VALUES(1),('01');", 'PRAGMA foreign_key_check(c);'),
    'self': ('CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES c(id));INSERT INTO c VALUES(1,1),(2,99);', 'PRAGMA foreign_key_check(c);'),
}
def orphan_tables(count):
    return 'CREATE TABLE p(id INTEGER PRIMARY KEY);' + ''.join(
        f'CREATE TABLE c{i}(x REFERENCES p(id));INSERT INTO c{i} VALUES({i + 1});'
        for i in range(count))

for count in [3, 20, 50, 140]:
    EXTRA[f'many_tables_{count}'] = (orphan_tables(count), 'PRAGMA foreign_key_check;')
for name, sql in {
    'savepoint_create': 'SAVEPOINT a;CREATE TABLE c3(x REFERENCES p(id));INSERT INTO c3 VALUES(9);PRAGMA foreign_key_check;ROLLBACK TO a;PRAGMA foreign_key_check;RELEASE a;PRAGMA foreign_key_check;',
    'nested_savepoint': 'BEGIN;SAVEPOINT a;CREATE TABLE c3(x REFERENCES p(id));INSERT INTO c3 VALUES(9);SAVEPOINT b;DROP TABLE c1;PRAGMA foreign_key_check;ROLLBACK TO b;PRAGMA foreign_key_check;ROLLBACK TO a;PRAGMA foreign_key_check;COMMIT;',
    'commit_create': 'BEGIN;CREATE TABLE c3(x REFERENCES p(id));INSERT INTO c3 VALUES(9);COMMIT;PRAGMA foreign_key_check;',
    'rollback_after_drop': 'DROP TABLE c1;BEGIN;CREATE TABLE c3(x REFERENCES p(id));INSERT INTO c3 VALUES(9);ROLLBACK;PRAGMA foreign_key_check;',
    'rollback_no_ddl': 'DROP TABLE c1;BEGIN;INSERT INTO c0 VALUES(99);ROLLBACK;PRAGMA foreign_key_check;',
    'rename_child': 'ALTER TABLE c1 RENAME TO renamed;PRAGMA foreign_key_list(renamed);PRAGMA foreign_key_check;',
    'rename_column': 'ALTER TABLE c1 RENAME COLUMN x TO renamed;PRAGMA foreign_key_list(c1);PRAGMA foreign_key_check;',
    'add_column': 'ALTER TABLE c1 ADD COLUMN z;PRAGMA foreign_key_check;',
    'joined_check_functions': 'SELECT a.\"table\",a.rowid,b.fkid FROM pragma_foreign_key_check() a JOIN pragma_foreign_key_check() b ON a.rowid=b.rowid ORDER BY a.\"table\",b.\"table\";',
}.items():
    EXTRA[name] = (orphan_tables(3), sql)
EXTRA['drop_after_rehash'] = (orphan_tables(50), ''.join(f'DROP TABLE c{i};' for i in range(0, 50, 3)) + 'CREATE TABLE fresh(x REFERENCES p(id));INSERT INTO fresh VALUES(99);PRAGMA foreign_key_check;')

for name, (setup, sql) in EXTRA.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(ForeignKeyPragmas, 'test_' + name + '_' + suffix, case(sql, mode, setup))
rng = random.Random(int(os.environ.get('SQLEANITE_FOREIGN_PRAGMA_SEED', '365901')))
for i in range(12):
    keys = rng.sample(range(1, 1000), rng.randrange(1, 8))
    children = [rng.choice(keys + [None, 2001, 2002]) for _ in range(rng.randrange(1, 10))]
    setup = 'CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES' + ','.join(f'({v})' for v in keys) + ';CREATE TABLE c(x REFERENCES p(id));INSERT INTO c VALUES' + ','.join('(NULL)' if v is None else f'({v})' for v in children) + ';'
    sql = 'PRAGMA foreign_key_list(c);PRAGMA foreign_key_check(c);'
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(ForeignKeyPragmas, f'test_fresh_{i}_{suffix}', case(sql, mode, setup))
if __name__ == '__main__':
    unittest.main()
