#!/usr/bin/env python3
"""Retained single-column table FOREIGN KEY constraints and their row effects."""
import os
import random
import unittest
from test_check_add_column import case

class TableForeignKeys(unittest.TestCase):
    pass

PARENTS = "CREATE TABLE p(id INTEGER PRIMARY KEY,s TEXT UNIQUE);INSERT INTO p VALUES(1,'a'),(2,'b');CREATE TABLE q(id INTEGER PRIMARY KEY);INSERT INTO q VALUES(1),(3);"
SETUP = PARENTS + 'CREATE TABLE c(id INTEGER PRIMARY KEY,x,y,FOREIGN KEY(x) REFERENCES p(id));INSERT INTO c VALUES(1,1,0);'
QUERIES = {
    'list': 'PRAGMA foreign_key_list(c);',
    'check': 'PRAGMA foreign_key_check;',
    'table_function': "SELECT * FROM pragma_foreign_key_list('c');",
    'valid_insert': 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(2,2,0);SELECT * FROM c;',
    'bad_insert': 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(2,99,0);',
    'null_insert': 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(2,NULL,0);PRAGMA foreign_key_check;',
    'ignore_bad': 'PRAGMA foreign_keys=ON;INSERT OR IGNORE INTO c VALUES(2,99,0);',
    'replace_bad': 'PRAGMA foreign_keys=ON;INSERT OR REPLACE INTO c VALUES(1,99,0);',
    'insert_select': 'PRAGMA foreign_keys=ON;INSERT INTO c SELECT id+10,id,0 FROM p;SELECT * FROM c;',
    'update_child': 'PRAGMA foreign_keys=ON;UPDATE c SET x=99;',
    'update_unrelated': 'PRAGMA foreign_keys=ON;UPDATE c SET y=99;SELECT * FROM c;',
    'update_parent': 'PRAGMA foreign_keys=ON;UPDATE p SET id=99 WHERE id=1;',
    'delete_parent': 'PRAGMA foreign_keys=ON;DELETE FROM p WHERE id=1;',
    'delete_child': 'PRAGMA foreign_keys=ON;DELETE FROM c;DELETE FROM p;PRAGMA foreign_key_check;',
    'drop_parent': 'PRAGMA foreign_keys=ON;DROP TABLE p;',
    'drop_child': 'PRAGMA foreign_keys=ON;DROP TABLE c;DROP TABLE p;',
    'upsert_valid': 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,2,8) ON CONFLICT(id) DO UPDATE SET x=excluded.x;SELECT * FROM c;',
    'upsert_bad': 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,99,8) ON CONFLICT(id) DO UPDATE SET x=excluded.x;',
    'rename_parent': 'ALTER TABLE p RENAME TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;',
    'rename_parent_column': 'ALTER TABLE p RENAME COLUMN id TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;',
    'rename_child_column': 'ALTER TABLE c RENAME COLUMN x TO renamed;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;',
    'rename_child': 'ALTER TABLE c RENAME TO renamed;PRAGMA foreign_key_list(renamed);PRAGMA foreign_key_check;',
    'add_column': 'ALTER TABLE c ADD COLUMN z INTEGER DEFAULT 9;PRAGMA foreign_key_list(c);SELECT * FROM c;',
    'drop_other_column': 'ALTER TABLE c DROP COLUMN y;PRAGMA foreign_key_list(c);SELECT * FROM c;',
    'drop_child_column': 'ALTER TABLE c DROP COLUMN x;',
    'rollback': 'BEGIN;ALTER TABLE c RENAME COLUMN x TO renamed;PRAGMA foreign_key_list(c);ROLLBACK;PRAGMA foreign_key_list(c);',
}
for name, sql in QUERIES.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(TableForeignKeys, 'test_' + name + '_' + suffix, case(sql, mode, SETUP))
CREATES = {
    'simple': 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id));',
    'named': 'CREATE TABLE c(x,CONSTRAINT fk FOREIGN KEY(x) REFERENCES p(id));',
    'implicit_parent': 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p);',
    'no_action': 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id) ON DELETE NO ACTION ON UPDATE NO ACTION);',
    'quoted': 'CREATE TABLE c("x x",CONSTRAINT "fk fk" FOREIGN KEY("x x") REFERENCES "p"("id"));',
    'comment': 'CREATE TABLE c(x,FOREIGN /* key */ KEY /* target */ (x) REFERENCES /* parent */ p(id));',
    'unique_parent': 'CREATE TABLE c(x TEXT,FOREIGN KEY(x) REFERENCES p(s));',
    'mixed_unique': 'CREATE TABLE c(x,y,UNIQUE(y),FOREIGN KEY(x) REFERENCES p(id));',
    'mixed_primary': 'CREATE TABLE c(x,y,PRIMARY KEY(y),FOREIGN KEY(x) REFERENCES p(id));',
    'mixed_check': 'CREATE TABLE c(x,y CHECK(y>0),FOREIGN KEY(x) REFERENCES p(id),CHECK(x>=0));',
    'two_table_keys': 'CREATE TABLE c(x,y,FOREIGN KEY(x) REFERENCES p(id),FOREIGN KEY(y) REFERENCES q(id));',
    'mixed_column_key': 'CREATE TABLE c(x REFERENCES q(id),y,FOREIGN KEY(y) REFERENCES p(id));',
    'same_column_keys': 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id),FOREIGN KEY(x) REFERENCES q(id));',
    'column_and_table_same': 'CREATE TABLE c(x REFERENCES q(id),FOREIGN KEY(x) REFERENCES p(id));',
}
for name, ddl in CREATES.items():
    sql = ddl + "PRAGMA foreign_key_list(c);SELECT * FROM pragma_foreign_key_list('c');PRAGMA foreign_key_check;"
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(TableForeignKeys, 'test_create_' + name + '_' + suffix, case(sql, mode, PARENTS))
EXTRA = {
    'unknown_child': (PARENTS, 'CREATE TABLE c(x,FOREIGN KEY(missing) REFERENCES p(id));'),
    'orphan_check': (PARENTS + 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id));INSERT INTO c VALUES(99),(NULL);', 'PRAGMA foreign_key_check;'),
    'missing_parent': ('CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES missing(id));', 'PRAGMA foreign_key_check;PRAGMA foreign_keys=ON;INSERT INTO c VALUES(NULL);'),
    'mismatch': ('CREATE TABLE p(x);CREATE TABLE c(y,FOREIGN KEY(y) REFERENCES p(x));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(NULL);'),
    'self': ('CREATE TABLE c(id INTEGER PRIMARY KEY,x,FOREIGN KEY(x) REFERENCES c(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1);PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;'),
    'two_keys_insert_bad': (PARENTS + 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id),FOREIGN KEY(x) REFERENCES q(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(2);'),
    'two_keys_insert_valid': (PARENTS + 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id),FOREIGN KEY(x) REFERENCES q(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1);PRAGMA foreign_key_check;'),
    'two_keys_inspect': (PARENTS + 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id),FOREIGN KEY(x) REFERENCES q(id));INSERT INTO c VALUES(1),(2),(3),(99);', 'PRAGMA foreign_key_list(c);PRAGMA foreign_key_check(c);'),
}
EXTRA.update({
    'no_op_invalid_child': (PARENTS + 'CREATE TABLE c(x);', 'CREATE TABLE IF NOT EXISTS c(x,FOREIGN KEY(missing) REFERENCES missing(id));PRAGMA foreign_key_list(c);'),
    'create_existing_error': (PARENTS + 'CREATE TABLE c(x);', 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id));'),
    'drop_last_constraint_comments': ('CREATE TABLE c (id INTEGER, /* before x */ x TEXT, /* before y */ y BLOB, CONSTRAINT key PRIMARY KEY(id));', 'ALTER TABLE c DROP COLUMN y;'),
    'drop_last_preserves_check': ('CREATE TABLE c(x,y,CHECK(x>0));INSERT INTO c VALUES(1,2);', 'ALTER TABLE c DROP COLUMN y;SELECT * FROM c;'),
    'drop_last_preserves_unique': ('CREATE TABLE c(x,y,UNIQUE(x));INSERT INTO c VALUES(1,2);', 'ALTER TABLE c DROP COLUMN y;PRAGMA index_list(c);SELECT * FROM c;'),
    'rowid_alias_valid': (PARENTS, 'CREATE TABLE c(id INTEGER PRIMARY KEY,FOREIGN KEY(id) REFERENCES p(id));PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1);PRAGMA foreign_key_list(c);'),
    'rowid_alias_invalid': (PARENTS, 'CREATE TABLE c(id INTEGER PRIMARY KEY,FOREIGN KEY(id) REFERENCES p(id));PRAGMA foreign_keys=ON;INSERT INTO c VALUES(99);'),
    'cycle': ('CREATE TABLE a(id INTEGER PRIMARY KEY,x,FOREIGN KEY(x) REFERENCES b(id));CREATE TABLE b(id INTEGER PRIMARY KEY,x,FOREIGN KEY(x) REFERENCES a(id));', 'INSERT INTO a VALUES(1,1);INSERT INTO b VALUES(1,1);PRAGMA foreign_keys=ON;PRAGMA foreign_key_check;'),
    'self_rename': ('CREATE TABLE c(id INTEGER PRIMARY KEY,x,FOREIGN KEY(x) REFERENCES c(id));INSERT INTO c VALUES(1,1);', 'ALTER TABLE c RENAME TO renamed;ALTER TABLE renamed RENAME COLUMN id TO key;PRAGMA foreign_key_list(renamed);PRAGMA foreign_key_check;'),
    'other_missing_parent_update': ('CREATE TABLE c(id INTEGER PRIMARY KEY,x,y,FOREIGN KEY(x) REFERENCES missing(id));INSERT INTO c VALUES(1,99,0);', 'PRAGMA foreign_keys=ON;UPDATE c SET y=1;SELECT * FROM c;'),
    'orphan_same_value_update': (PARENTS + 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id));INSERT INTO c VALUES(99);', 'PRAGMA foreign_keys=ON;UPDATE c SET x=x;'),
    'orphan_ignored_row': (PARENTS + 'CREATE TABLE c(id INTEGER PRIMARY KEY,x,FOREIGN KEY(x) REFERENCES p(id));INSERT INTO c VALUES(1,99);', 'PRAGMA foreign_keys=ON;INSERT OR IGNORE INTO c VALUES(1,99);SELECT * FROM c;'),
    'two_keys_parent_update': (PARENTS + 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id),FOREIGN KEY(x) REFERENCES q(id));INSERT INTO c VALUES(1);', 'PRAGMA foreign_keys=ON;UPDATE p SET id=99 WHERE id=1;'),
    'same_key_duplicate': (PARENTS + 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id),FOREIGN KEY(x) REFERENCES p(id));INSERT INTO c VALUES(99);', 'PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;'),
    'text_primary': ("CREATE TABLE p(x TEXT PRIMARY KEY);INSERT INTO p VALUES('1');CREATE TABLE c(y,FOREIGN KEY(y) REFERENCES p);INSERT INTO c VALUES(1),('01');", 'PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;'),
    'quoted_child_rename': (PARENTS + 'CREATE TABLE c("from",CONSTRAINT "references" FOREIGN KEY("from") REFERENCES p("id"));', 'ALTER TABLE c RENAME COLUMN "from" TO "to";PRAGMA foreign_key_list(c);'),
    'drop_first_child_column': (PARENTS + 'CREATE TABLE c(x,y,FOREIGN KEY(x) REFERENCES p(id));', 'ALTER TABLE c DROP COLUMN x;'),
    'drop_shifted_child_column': (PARENTS + 'CREATE TABLE c(y,x,FOREIGN KEY(x) REFERENCES p(id));INSERT INTO c VALUES(9,99);', 'ALTER TABLE c DROP COLUMN y;PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;'),
    'repeat_no_action': (PARENTS, 'CREATE TABLE c(x,FOREIGN KEY(x) REFERENCES p(id) ON DELETE NO ACTION ON UPDATE NO ACTION ON DELETE NO ACTION);PRAGMA foreign_key_list(c);'),
})
for name, (setup, sql) in EXTRA.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(TableForeignKeys, 'test_' + name + '_' + suffix, case(sql, mode, setup))
rng=random.Random(int(os.environ.get('SQLEANITE_TABLE_FOREIGN_KEY_SEED','366101')))
for i in range(12):
    value=rng.randrange(1,100000)
    setup=f'CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES({value});'
    sql=f'CREATE TABLE c(x,CONSTRAINT fk_{i} FOREIGN KEY(x) REFERENCES p(id));PRAGMA foreign_keys=ON;INSERT INTO c VALUES({value});PRAGMA foreign_key_list(c);PRAGMA foreign_key_check;'
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(TableForeignKeys,f'test_fresh_{i}_{suffix}',case(sql,mode,setup))
if __name__=='__main__':
    unittest.main()
