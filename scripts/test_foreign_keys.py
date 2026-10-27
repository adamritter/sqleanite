#!/usr/bin/env python3
"""Foreign-key declarations, connection flags and immediate NO ACTION checks."""
import os
import random
import unittest
os.environ.setdefault('SQLEANITE_LASTID_SEED', os.environ.get('SQLEANITE_FOREIGN_KEY_SEED', '365701'))
from test_check_add_column import case
from test_last_insert_rowid import SCRIPTS as CONNECTION_SCRIPTS

class ForeignKeys(unittest.TestCase):
    pass

SETUP = 'CREATE TABLE p(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO p VALUES(1,\'a\'),(2,\'b\');CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id),v TEXT);'
QUERIES = {
    'flag_negative': 'PRAGMA foreign_keys=-1;PRAGMA foreign_keys;',
    'flag_wrap_zero': 'PRAGMA foreign_keys=256;PRAGMA foreign_keys;',
    'flag_wrap_one': 'PRAGMA foreign_keys=257;PRAGMA foreign_keys;',
    'flag_yes': "PRAGMA foreign_keys='YeS';PRAGMA foreign_keys;",
    'flag_unknown': "PRAGMA foreign_keys='other';PRAGMA foreign_keys;",
    'flag_main': 'PRAGMA main.foreign_keys=ON;PRAGMA foreign_keys;',
    'flag_missing_schema': 'PRAGMA missing.foreign_keys=ON;',
    'flag_empty': "PRAGMA foreign_keys='';PRAGMA foreign_keys;",
    'default_flag': 'PRAGMA foreign_keys;',
    'flag_on': 'PRAGMA foreign_keys=ON;PRAGMA foreign_keys;',
    'flag_off': 'PRAGMA foreign_keys=ON;PRAGMA foreign_keys=OFF;PRAGMA foreign_keys;',
    'off_allows': "INSERT INTO c VALUES(1,99,'x');SELECT * FROM c;",
    'insert_valid': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');SELECT * FROM c;",
    'insert_null': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,NULL,'x');SELECT * FROM c;",
    'insert_bad': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,99,'x');",
    'insert_ignore_bad': "PRAGMA foreign_keys=ON;INSERT OR IGNORE INTO c VALUES(1,99,'x');",
    'insert_replace_bad': "PRAGMA foreign_keys=ON;INSERT OR REPLACE INTO c VALUES(1,99,'x');",
    'insert_multi_abort': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x'),(2,99,'y');",
    'insert_select': "PRAGMA foreign_keys=ON;INSERT INTO c SELECT id,id,v FROM p;SELECT * FROM c;",
    'insert_select_bad': "PRAGMA foreign_keys=ON;INSERT INTO c SELECT id,id+100,v FROM p;",
    'insert_empty': 'PRAGMA foreign_keys=ON;INSERT INTO c SELECT 1,99,NULL WHERE 0;SELECT count(*) FROM c;',
    'returning': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x') RETURNING *;",
    'returning_bad': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,99,'x') RETURNING *;",
    'delete_parent': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');DELETE FROM p WHERE id=1;",
    'delete_other_parent': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');DELETE FROM p WHERE id=2;SELECT * FROM p;",
    'delete_child': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');DELETE FROM c;DELETE FROM p WHERE id=1;SELECT count(*) FROM p;",
    'update_child_bad': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');UPDATE c SET pid=99;",
    'update_child_good': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');UPDATE c SET pid=2;SELECT * FROM c;",
    'update_child_null': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');UPDATE c SET pid=NULL;SELECT * FROM c;",
    'update_child_unrelated': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');UPDATE c SET v='y';SELECT * FROM c;",
    'update_parent_bad': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');UPDATE p SET id=3 WHERE id=1;",
    'update_parent_unrelated': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');UPDATE p SET v='y';SELECT * FROM c;",
    'replace_parent_same': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');INSERT OR REPLACE INTO p VALUES(1,'new');SELECT * FROM c;",
    'upsert_bad': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');INSERT INTO c VALUES(1,2,'x') ON CONFLICT(id) DO UPDATE SET pid=99;",
    'upsert_good': "PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,'x');INSERT INTO c VALUES(1,2,'x') ON CONFLICT(id) DO UPDATE SET pid=excluded.pid;SELECT * FROM c;",
    'rollback': "PRAGMA foreign_keys=ON;BEGIN;INSERT INTO c VALUES(1,1,'x');ROLLBACK;PRAGMA foreign_keys;SELECT count(*) FROM c;",
    'savepoint': "PRAGMA foreign_keys=ON;SAVEPOINT s;INSERT INTO c VALUES(1,1,'x');ROLLBACK TO s;RELEASE s;PRAGMA foreign_keys;",
    'on_inside_transaction': "BEGIN;PRAGMA foreign_keys=ON;PRAGMA foreign_keys;INSERT INTO c VALUES(1,99,'x');COMMIT;SELECT * FROM c;",
    'off_inside_transaction': "PRAGMA foreign_keys=ON;BEGIN;PRAGMA foreign_keys=OFF;PRAGMA foreign_keys;INSERT INTO c VALUES(1,99,'x');",
    'on_inside_savepoint': 'SAVEPOINT s;PRAGMA foreign_keys=ON;PRAGMA foreign_keys;RELEASE s;',
    'create_from_lean': "PRAGMA foreign_keys=ON;CREATE TABLE d(x REFERENCES p(id));INSERT INTO d VALUES(1);SELECT * FROM d;",
}
for name, sql in QUERIES.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(ForeignKeys, 'test_' + name + '_' + suffix, case(sql, mode, SETUP))
EXTRA = {
    'old_orphan_unselected': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id),v);INSERT INTO c VALUES(1,99,0),(2,1,0);', 'PRAGMA foreign_keys=ON;UPDATE c SET pid=1 WHERE id=2;SELECT * FROM c;'),
    'old_orphan_rekey': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id));INSERT INTO c VALUES(1,99);', 'PRAGMA foreign_keys=ON;UPDATE c SET id=2;SELECT * FROM c;'),
    'old_orphan_replace': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id));INSERT INTO c VALUES(1,99);', 'PRAGMA foreign_keys=ON;INSERT OR REPLACE INTO c VALUES(1,99);'),
    'old_orphan_upsert_same': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id));INSERT INTO c VALUES(1,99);', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1) ON CONFLICT(id) DO UPDATE SET pid=c.pid;'),
    'old_orphan_upsert_other': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id),v);INSERT INTO c VALUES(1,99,0);', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1,1) ON CONFLICT(id) DO UPDATE SET v=1;SELECT * FROM c;'),
    'ignore_existing_bad': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id));INSERT INTO c VALUES(1,99);', 'PRAGMA foreign_keys=ON;INSERT OR IGNORE INTO c VALUES(1,99);SELECT * FROM c;'),
    'update_ignore_skipped': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id),v UNIQUE);INSERT INTO c VALUES(1,99,1),(2,1,2);', 'PRAGMA foreign_keys=ON;UPDATE OR IGNORE c SET pid=pid,v=2 WHERE id=1;SELECT * FROM c;'),
    'multi_foreign_keys': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1),(2);CREATE TABLE c(a REFERENCES p(id),b REFERENCES p(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,2);INSERT INTO c VALUES(1,99);'),
    'explicit_no_action': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(x REFERENCES p(id) ON DELETE NO ACTION ON UPDATE NO ACTION);', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1);DELETE FROM p;'),
    'drop_child_missing': ('CREATE TABLE c(x REFERENCES missing(id));INSERT INTO c VALUES(99);', 'PRAGMA foreign_keys=ON;DROP TABLE c;'),
    'drop_missing_noop': ('CREATE TABLE c(x REFERENCES missing(id));INSERT INTO c VALUES(99);', 'PRAGMA foreign_keys=ON;DROP TABLE IF EXISTS missing;'),
    'parent_unrelated_mismatch': ('CREATE TABLE p(id,v);INSERT INTO p VALUES(1,0);CREATE TABLE c(x REFERENCES p(id));', 'PRAGMA foreign_keys=ON;UPDATE p SET v=1;SELECT * FROM p;'),
    'parent_drop': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(x REFERENCES p(id));INSERT INTO c VALUES(1);', 'PRAGMA foreign_keys=ON;DROP TABLE p;'),
    'add_reference_on_null': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(x);INSERT INTO c VALUES(1);', 'PRAGMA foreign_keys=ON;ALTER TABLE c ADD pid REFERENCES p(id);SELECT * FROM c;INSERT INTO c VALUES(2,99);'),
    'add_reference_on_default': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(x);INSERT INTO c VALUES(1);', 'PRAGMA foreign_keys=ON;ALTER TABLE c ADD pid DEFAULT 1 REFERENCES p(id);'),
    'add_reference_off_default': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(x);INSERT INTO c VALUES(1);', 'ALTER TABLE c ADD pid DEFAULT 99 REFERENCES p(id);SELECT * FROM c;'),
    'add_reference_empty': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(x);', 'PRAGMA foreign_keys=ON;ALTER TABLE c ADD pid DEFAULT 1 REFERENCES p(id);INSERT INTO c(x) VALUES(1);SELECT * FROM c;'),
    'add_reference_check': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(x);INSERT INTO c VALUES(1);', 'PRAGMA foreign_keys=ON;ALTER TABLE c ADD pid REFERENCES p(id) CHECK(pid IS NULL);SELECT * FROM c;'),
    'missing_parent_order': ('CREATE TABLE c(a REFERENCES missing_a(id),b REFERENCES missing_b(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,2);'),
    'implicit_parent_key': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(x REFERENCES p);', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1);SELECT * FROM c;'),
    'text_affinity': ("CREATE TABLE p(id TEXT PRIMARY KEY);INSERT INTO p VALUES('1');CREATE TABLE c(x REFERENCES p(id));", 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1);SELECT typeof(x),x FROM c;'),
    'integer_affinity': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(x TEXT REFERENCES p(id));', "PRAGMA foreign_keys=ON;INSERT INTO c VALUES('01');SELECT typeof(x),x FROM c;"),
    'unique_parent': ('CREATE TABLE p(id UNIQUE);INSERT INTO p VALUES(1);CREATE TABLE c(x REFERENCES p(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1);SELECT * FROM c;'),
    'bad_parent_key': ('CREATE TABLE p(id);INSERT INTO p VALUES(1);CREATE TABLE c(x REFERENCES p(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1);'),
    'missing_parent': ('CREATE TABLE c(x REFERENCES missing(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1);'),
    'missing_parent_null': ('CREATE TABLE c(x REFERENCES missing(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(NULL);'),
    'self_reference': ('CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES c(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,1);SELECT * FROM c;'),
    'self_multi': ('CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES c(id));', 'PRAGMA foreign_keys=ON;INSERT INTO c VALUES(1,2),(2,1);SELECT * FROM c;'),
    'existing_violation_unrelated': ("CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id),v);INSERT INTO c VALUES(1,99,0);", 'PRAGMA foreign_keys=ON;UPDATE c SET v=1;SELECT * FROM c;'),
    'existing_violation_same': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id));INSERT INTO c VALUES(1,99);', 'PRAGMA foreign_keys=ON;UPDATE c SET pid=pid;SELECT * FROM c;'),
    'existing_violation_delete': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id));INSERT INTO c VALUES(1,99);', 'PRAGMA foreign_keys=ON;DELETE FROM c;SELECT count(*) FROM c;'),
}
for name, (setup, sql) in EXTRA.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(ForeignKeys, 'test_' + name + '_' + suffix, case(sql, mode, setup))
# Enabling FK checking also selects the row-effect path for ordinary writes.
# Keep the established connection-register regressions under that flag too.
for name, sql in CONNECTION_SCRIPTS.items():
    setup = 'CREATE TABLE t(id INTEGER PRIMARY KEY,v INTEGER);'
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(ForeignKeys, 'test_connection_' + name + '_' + suffix,
                case('PRAGMA foreign_keys=ON;' + sql, mode, setup))
rng = random.Random(int(os.environ.get('SQLEANITE_FOREIGN_KEY_SEED', '365701')))
for i in range(12):
    keys = rng.sample(range(1, 1000), rng.randrange(1, 8))
    key = rng.choice(keys) if i % 2 else 1000 + rng.randrange(1000)
    setup = 'CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES' + ','.join(f'({k})' for k in keys) + ';CREATE TABLE c(x REFERENCES p(id));'
    sql = f'PRAGMA foreign_keys=ON;INSERT INTO c VALUES({key});SELECT * FROM c;'
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(ForeignKeys, f'test_fresh_{i}_{suffix}', case(sql, mode, setup))
if __name__ == '__main__':
    unittest.main()
