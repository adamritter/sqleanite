#!/usr/bin/env python3
"""Foreign-key catalog updates and enforcement after parent/child renames."""
import os
import random
import unittest
from test_check_add_column import case

class ForeignKeyRename(unittest.TestCase):
    pass

SETUP = '''CREATE TABLE p(id INTEGER PRIMARY KEY,x TEXT UNIQUE);INSERT INTO p VALUES(1,'a'),(2,'b');
CREATE TABLE c(id INTEGER PRIMARY KEY,a REFERENCES p(id),b REFERENCES p(x));INSERT INTO c VALUES(1,1,'a');'''
QUERIES = {
    'table': 'ALTER TABLE p RENAME TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;',
    'table_main': 'ALTER TABLE main.p RENAME TO renamed;PRAGMA foreign_key_list(c);',
    'table_case': 'ALTER TABLE P RENAME TO renamed;PRAGMA foreign_key_list(c);',
    'table_case_only': 'ALTER TABLE p RENAME TO P;PRAGMA foreign_key_list(c);',
    'table_quoted': 'ALTER TABLE p RENAME TO "new parent";PRAGMA foreign_key_list(c);',
    'table_repeated': 'ALTER TABLE p RENAME TO first;ALTER TABLE first RENAME TO second;PRAGMA foreign_key_list(c);',
    'column_main': 'ALTER TABLE main.p RENAME COLUMN id TO renamed;PRAGMA foreign_key_list(c);',
    'column': 'ALTER TABLE p RENAME COLUMN id TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;',
    'column_case': 'ALTER TABLE P RENAME COLUMN ID TO renamed;PRAGMA foreign_key_list(c);',
    'column_case_only': 'ALTER TABLE p RENAME COLUMN id TO ID;PRAGMA foreign_key_list(c);',
    'column_unique': 'ALTER TABLE p RENAME COLUMN x TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;',
    'column_quoted': 'ALTER TABLE p RENAME COLUMN id TO "new id";PRAGMA foreign_key_list(c);',
    'column_repeated': 'ALTER TABLE p RENAME COLUMN id TO first;ALTER TABLE p RENAME COLUMN first TO second;PRAGMA foreign_key_list(c);',
    'child_table': 'ALTER TABLE c RENAME TO child;PRAGMA foreign_key_list(child);PRAGMA foreign_key_check;',
    'child_column': 'ALTER TABLE c RENAME COLUMN a TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;',
    'table_rollback': 'BEGIN;ALTER TABLE p RENAME TO renamed;PRAGMA foreign_key_list(c);ROLLBACK;PRAGMA foreign_key_list(c);',
    'column_savepoint': 'SAVEPOINT a;ALTER TABLE p RENAME COLUMN id TO renamed;PRAGMA foreign_key_list(c);ROLLBACK TO a;PRAGMA foreign_key_list(c);RELEASE a;',
    'table_valid_write': 'ALTER TABLE p RENAME TO renamed;PRAGMA foreign_keys=ON;INSERT INTO c VALUES(2,2,\'b\');PRAGMA foreign_key_check;',
    'table_invalid_write': 'ALTER TABLE p RENAME TO renamed;PRAGMA foreign_keys=ON;INSERT INTO c VALUES(2,99,\'b\');',
    'column_valid_write': 'ALTER TABLE p RENAME COLUMN id TO renamed;PRAGMA foreign_keys=ON;INSERT INTO c VALUES(2,2,\'b\');PRAGMA foreign_key_check;',
    'column_invalid_write': 'ALTER TABLE p RENAME COLUMN id TO renamed;PRAGMA foreign_keys=ON;INSERT INTO c VALUES(2,99,\'b\');',
    'table_delete_parent': 'ALTER TABLE p RENAME TO renamed;PRAGMA foreign_keys=ON;DELETE FROM renamed WHERE id=1;',
    'column_update_parent': 'ALTER TABLE p RENAME COLUMN id TO renamed;PRAGMA foreign_keys=ON;UPDATE p SET renamed=99 WHERE renamed=1;',
}
for name, sql in QUERIES.items():
    for flag in ['OFF', 'ON']:
        for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
            setattr(ForeignKeyRename, 'test_' + name + '_' + flag + '_' + suffix,
                    case('PRAGMA foreign_keys=' + flag + ';' + sql, mode, SETUP))
EXTRA = {
    'self_table': ('CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES c(id));INSERT INTO c VALUES(1,1);', 'ALTER TABLE c RENAME TO renamed;PRAGMA foreign_key_list(renamed);PRAGMA foreign_key_check;'),
    'self_column': ('CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES c(id));INSERT INTO c VALUES(1,1);', 'ALTER TABLE c RENAME COLUMN id TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;'),
    'self_implicit': ('CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES c);INSERT INTO c VALUES(1,1);', 'ALTER TABLE c RENAME COLUMN id TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;'),
    'omitted_parent_column': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES p);', 'ALTER TABLE p RENAME COLUMN id TO renamed;PRAGMA foreign_key_list(c);'),
    'multiple_children': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE a(x REFERENCES p(id));CREATE TABLE b(y REFERENCES p);CREATE TABLE c(z REFERENCES p(id));', 'ALTER TABLE p RENAME TO renamed;PRAGMA foreign_key_list(a);PRAGMA foreign_key_list(b);PRAGMA foreign_key_list(c);'),
    'other_parent': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE q(id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES p(id),y REFERENCES q(id));', 'ALTER TABLE p RENAME TO renamed;PRAGMA foreign_key_list(c);'),
    'quoted_original': ('CREATE TABLE [P P]([ID ID] INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES [P P]([ID ID]));', 'ALTER TABLE [P P] RENAME COLUMN [ID ID] TO renamed;PRAGMA foreign_key_list(c);'),
    'quoted_parent': ('CREATE TABLE [P P](id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES [P P](id));', 'ALTER TABLE [P P] RENAME TO renamed;PRAGMA foreign_key_list(c);'),
    'comment': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES /* p(id) */ p /* p(id) */ (id));', 'ALTER TABLE p RENAME TO renamed;PRAGMA foreign_key_list(c);'),
    'literal_untouched': ("CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES p(id),v TEXT DEFAULT 'REFERENCES p(id)' CHECK(v<>'REFERENCES p(x)'));", 'ALTER TABLE p RENAME TO renamed;PRAGMA foreign_key_list(c);'),
    'missing_parent_table': ('CREATE TABLE c(id INTEGER PRIMARY KEY,x REFERENCES missing(id));', 'ALTER TABLE c RENAME TO renamed;PRAGMA foreign_key_list(renamed);'),
    'quoted_period': ('CREATE TABLE "p.q"(id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES "p.q"(id));', 'ALTER TABLE "p.q" RENAME TO renamed;PRAGMA foreign_key_list(c);'),
    'main_quoted_period': ('CREATE TABLE "p.q"(id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES "p.q"(id));', 'ALTER TABLE main."p.q" RENAME TO renamed;PRAGMA foreign_key_list(c);'),
    'main_literal_distinct': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE "main.p"(z);CREATE TABLE c(x REFERENCES p(id));', 'ALTER TABLE main.p RENAME TO renamed;SELECT name FROM sqlite_schema WHERE type=\'table\' ORDER BY name;PRAGMA foreign_key_list(c);'),
    'unknown_schema': ('CREATE TABLE p(id INTEGER PRIMARY KEY);', 'ALTER TABLE missing.p RENAME TO renamed;'),
    'temp_schema': ('CREATE TABLE p(id INTEGER PRIMARY KEY);', 'ALTER TABLE temp.p RENAME TO renamed;'),
    'quoted_new_double': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES p(id));', 'ALTER TABLE p RENAME TO "n""ew";PRAGMA foreign_key_list(c);'),
    'unicode_parent': ('CREATE TABLE "szülő"(id INTEGER PRIMARY KEY);CREATE TABLE c(x REFERENCES /* árvíz */ "szülő"(id));', 'ALTER TABLE "szülő" RENAME TO "új szülő";PRAGMA foreign_key_list(c);'),
    'unrelated_column': ('CREATE TABLE p(id INTEGER PRIMARY KEY,z);CREATE TABLE c(x REFERENCES p(id));', 'ALTER TABLE p RENAME COLUMN z TO renamed;PRAGMA foreign_key_list(c);'),
}
for name, (setup, sql) in EXTRA.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(ForeignKeyRename, 'test_' + name + '_' + suffix, case(sql, mode, setup))
rng = random.Random(int(os.environ.get('SQLEANITE_FOREIGN_RENAME_SEED', '366001')))
for i in range(12):
    value = rng.randrange(1, 10000)
    setup = f'CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES({value});CREATE TABLE c(x REFERENCES p(id));INSERT INTO c VALUES({value});'
    new = 'renamed_' + str(rng.randrange(1000000))
    sql = (f'ALTER TABLE p RENAME TO "{new}";PRAGMA foreign_keys=ON;INSERT INTO c VALUES({value});'
           f'ALTER TABLE "{new}" RENAME COLUMN id TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;')
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(ForeignKeyRename, f'test_fresh_{i}_{suffix}', case(sql, mode, setup))
if __name__ == '__main__':
    unittest.main()
