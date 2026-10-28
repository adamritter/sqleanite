#!/usr/bin/env python3
"""Stored generated-column programs, DML calculation and file compatibility."""
import os
import random
import unittest
from test_check_add_column import case

class StoredGeneratedColumns(unittest.TestCase):
    pass

SETUP='CREATE TABLE t(id INTEGER PRIMARY KEY,a INTEGER,b INTEGER GENERATED ALWAYS AS (a+1) STORED);INSERT INTO t(id,a) VALUES(1,2);'
QUERIES={
    'read': 'SELECT * FROM t;',
    'table_info': 'PRAGMA table_info(t);PRAGMA table_xinfo(t);',
    'table_functions': "SELECT * FROM pragma_table_xinfo('t');",
    'table_list': 'PRAGMA table_list(t);',
    'insert': 'INSERT INTO t VALUES(2,5);SELECT * FROM t ORDER BY id;',
    'insert_explicit': 'INSERT INTO t(id,a) VALUES(2,5);SELECT * FROM t ORDER BY id;',
    'insert_auto': 'INSERT INTO t(a) VALUES(5);SELECT * FROM t ORDER BY id;',
    'insert_default': 'INSERT INTO t DEFAULT VALUES;SELECT * FROM t ORDER BY id;',
    'insert_null': 'INSERT INTO t VALUES(2,NULL);SELECT * FROM t ORDER BY id;',
    'insert_wrong_width': 'INSERT INTO t VALUES(2,5,6);',
    'insert_generated': 'INSERT INTO t(id,a,b) VALUES(2,5,6);',
    'insert_select': 'INSERT INTO t SELECT 2,5;SELECT * FROM t ORDER BY id;',
    'insert_select_derived': 'INSERT INTO t SELECT * FROM (VALUES(2,5));SELECT * FROM t ORDER BY id;',
    'insert_returning': 'INSERT INTO t(a) VALUES(5) RETURNING id,a,b;',
    'update': 'UPDATE t SET a=5;SELECT * FROM t;',
    'update_old_generated': 'UPDATE t SET a=b;SELECT * FROM t;',
    'update_id': 'UPDATE t SET id=5;SELECT * FROM t;',
    'update_returning': 'UPDATE t SET a=5 RETURNING id,a,b;',
    'update_generated': 'UPDATE t SET b=9;',
    'update_generated_empty': 'UPDATE t SET b=9 WHERE 0;',
    'upsert': 'INSERT INTO t VALUES(1,5) ON CONFLICT(id) DO UPDATE SET a=excluded.a;SELECT * FROM t;',
    'upsert_generated': 'INSERT INTO t VALUES(1,5) ON CONFLICT(id) DO UPDATE SET b=9;',
    'upsert_returning': 'INSERT INTO t VALUES(1,5) ON CONFLICT(id) DO UPDATE SET a=excluded.a RETURNING id,a,b;',
    'delete_returning': 'DELETE FROM t RETURNING id,a,b;',
    'where': 'SELECT a,b FROM t WHERE b=3;',
    'ctas': 'CREATE TABLE c AS SELECT * FROM t;SELECT * FROM c;PRAGMA table_info(c);',
    'rename_base': 'ALTER TABLE t RENAME COLUMN a TO renamed;SELECT * FROM t;PRAGMA table_xinfo(t);',
    'rename_generated': 'ALTER TABLE t RENAME COLUMN b TO renamed;SELECT * FROM t;PRAGMA table_xinfo(t);',
    'rename_table': 'ALTER TABLE t RENAME TO renamed;INSERT INTO renamed VALUES(2,5);SELECT * FROM renamed ORDER BY id;',
    'drop_base': 'ALTER TABLE t DROP COLUMN a;',
    'drop_generated': 'ALTER TABLE t DROP COLUMN b;SELECT * FROM t;',
    'add_stored_populated': 'ALTER TABLE t ADD c INTEGER AS(a+2) STORED;',
    'rollback': 'BEGIN;UPDATE t SET a=9;ROLLBACK;SELECT * FROM t;',
    'savepoint': 'SAVEPOINT s;INSERT INTO t VALUES(2,9);ROLLBACK TO s;RELEASE s;SELECT * FROM t;',
}
for name,sql in QUERIES.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(StoredGeneratedColumns,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
CREATES={
    'basic': 'CREATE TABLE g(a INTEGER,b INTEGER AS(a+1) STORED);INSERT INTO g(a) VALUES(2);SELECT * FROM g;',
    'chain': 'CREATE TABLE g(a,b AS(c+1) STORED,c AS(a+1) STORED);INSERT INTO g(a) VALUES(2);SELECT * FROM g;',
    'auto_id': 'CREATE TABLE g(id INTEGER PRIMARY KEY,b AS(id+1) STORED);INSERT INTO g DEFAULT VALUES;SELECT * FROM g;',
    'auto_increment': 'CREATE TABLE g(id INTEGER PRIMARY KEY AUTOINCREMENT,b AS(id+1) STORED);INSERT INTO g DEFAULT VALUES;INSERT INTO g DEFAULT VALUES;SELECT * FROM g;',
    'only_generated': 'CREATE TABLE g(a AS(1) STORED);',
    'missing_name': 'CREATE TABLE g(a,b AS(missing+1) STORED);',
    'qualified_name': 'CREATE TABLE g(a,b AS(g.a+1) STORED);',
    'implicit_rowid': 'CREATE TABLE g(a,b AS(rowid+1) STORED);',
    'primary': 'CREATE TABLE g(a,b AS(a+1) STORED PRIMARY KEY);',
    'default': 'CREATE TABLE g(a,b DEFAULT 3 AS(a+1) STORED);',
    'random': 'CREATE TABLE g(a,b AS(random()) STORED);',
    'subquery': 'CREATE TABLE g(a,b AS((SELECT 1)) STORED);',
    'aggregate': 'CREATE TABLE g(a,b AS(sum(a)) STORED);',
    'missing_function': 'CREATE TABLE g(a,b AS(missing_function(a)) STORED);',
    'unique': 'CREATE TABLE g(a,b AS(a+1) STORED UNIQUE);INSERT INTO g(a) VALUES(2);INSERT INTO g(a) VALUES(2);',
    'check': 'CREATE TABLE g(a,b AS(a+1) STORED CHECK(b>0));INSERT INTO g(a) VALUES(-2);',
    'not_null': 'CREATE TABLE g(a,b AS(a+1) STORED NOT NULL);INSERT INTO g(a) VALUES(NULL);',
    'strict': "CREATE TABLE g(a ANY,b TEXT AS(a) STORED) STRICT;INSERT INTO g(a) VALUES('003');SELECT *,typeof(a),typeof(b) FROM g;",
    'strict_type_error': "CREATE TABLE g(a ANY,b INT AS(a) STORED) STRICT;INSERT INTO g(a) VALUES('bad');",
    'stored_untyped': "CREATE TABLE g(a,b AS(a) STORED);INSERT INTO g(a) VALUES('003');SELECT *,typeof(b) FROM g;",
    'stored_text': 'CREATE TABLE g(a,b TEXT AS(a+1) STORED);INSERT INTO g(a) VALUES(2);SELECT *,typeof(b) FROM g;',
    'loop_create': 'CREATE TABLE g(a,b AS(b+1) STORED);PRAGMA table_xinfo(g);',
    'loop_insert': 'CREATE TABLE g(a,b AS(b+1) STORED);INSERT INTO g(a) VALUES(2);',
    'cycle_create': 'CREATE TABLE g(a,b AS(c+1) STORED,c AS(b+1) STORED);PRAGMA table_xinfo(g);',
    'cycle_insert': 'CREATE TABLE g(a,b AS(c+1) STORED,c AS(b+1) STORED);INSERT INTO g(a) VALUES(2);',
    'add_stored_empty': 'CREATE TABLE g(a);ALTER TABLE g ADD b AS(a+1) STORED;INSERT INTO g(a) VALUES(2);SELECT * FROM g;',
}
for name,sql in CREATES.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(StoredGeneratedColumns,'test_create_'+name+'_'+suffix,case(sql,mode,''))
EXTRA={
    'middle_metadata': ('CREATE TABLE g(a,b AS(a+1) STORED,c);INSERT INTO g(a,c) VALUES(2,9);','PRAGMA table_info(g);PRAGMA table_xinfo(g);SELECT * FROM g;'),
    'boolean_dependency': ('CREATE TABLE g(a,b AS(true+1) STORED,true AS(a+1) STORED);','INSERT INTO g(a) VALUES(2);SELECT * FROM g;'),
    'unique_update': ('CREATE TABLE g(a,b AS(a+1) STORED UNIQUE);INSERT INTO g(a) VALUES(1),(2);','UPDATE g SET a=1 WHERE a=2;'),
    'unique_upsert': ('CREATE TABLE g(a,b AS(a+1) STORED UNIQUE);INSERT INTO g(a) VALUES(1);','INSERT INTO g(a) VALUES(1) ON CONFLICT(b) DO UPDATE SET a=excluded.a+1;SELECT * FROM g;'),
    'foreign_child': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(3);CREATE TABLE g(a,b AS(a+1) STORED REFERENCES p(id));','PRAGMA foreign_keys=ON;INSERT INTO g(a) VALUES(2);PRAGMA foreign_key_check;'),
    'foreign_child_bad': ('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE g(a,b AS(a+1) STORED REFERENCES p(id));','PRAGMA foreign_keys=ON;INSERT INTO g(a) VALUES(2);'),
    'foreign_child_update': ('CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(3);CREATE TABLE g(a,b AS(a+1) STORED REFERENCES p(id));INSERT INTO g(a) VALUES(2);','PRAGMA foreign_keys=ON;UPDATE g SET a=9;'),
    'foreign_parent_update': ('CREATE TABLE g(a,b AS(a+1) STORED UNIQUE);INSERT INTO g(a) VALUES(2);CREATE TABLE c(x REFERENCES g(b));INSERT INTO c VALUES(3);','PRAGMA foreign_keys=ON;UPDATE g SET a=9;'),
    'loop_empty_insert': ('CREATE TABLE g(a,b AS(b+1) STORED);','INSERT INTO g(a) SELECT 1 WHERE 0;'),
    'loop_empty_update': ('CREATE TABLE g(a,b AS(b+1) STORED);','UPDATE g SET a=1 WHERE 0;'),
    'loop_delete': ('CREATE TABLE g(a,b AS(b+1) STORED);','DELETE FROM g;'),
    'drop_other': ('CREATE TABLE g(a,b AS(a+1) STORED,c);INSERT INTO g(a,c) VALUES(2,9);','ALTER TABLE g DROP c;SELECT * FROM g;'),
}
EXTRA.update({
    'json_returning': ('CREATE TABLE g(a,b AS(json_array(a)) STORED);', "INSERT INTO g(a) VALUES(json('[]')) RETURNING a,b,json_array(b);"),
    'json_chain': ('CREATE TABLE g(a,b AS(json_array(a)) STORED,c AS(json_array(b)) STORED);', "INSERT INTO g(a) VALUES(json('[]')) RETURNING a,b,c,json_array(c);"),
    'real_affinity': ('CREATE TABLE g(a REAL,b AS(typeof(a)) STORED);', "INSERT INTO g(a) VALUES('003') RETURNING a,typeof(a),b;UPDATE g SET a='004' RETURNING a,typeof(a),b;"),
    'text_affinity': ('CREATE TABLE g(a TEXT,b AS(typeof(a)) STORED);', 'INSERT INTO g(a) VALUES(3) RETURNING a,typeof(a),b;'),
    'null_replace_default': ('CREATE TABLE g(a INT NOT NULL ON CONFLICT REPLACE DEFAULT 5,b AS(a+1) STORED);', 'INSERT INTO g(a) VALUES(NULL) RETURNING *;'),
    'null_replace_update': ('CREATE TABLE g(a INT NOT NULL ON CONFLICT REPLACE DEFAULT 5,b AS(a+1) STORED);INSERT INTO g(a) VALUES(2);', 'UPDATE g SET a=NULL RETURNING *;'),
    'null_replace_override': ('CREATE TABLE g(a INT NOT NULL DEFAULT 5,b AS(a+1) STORED);', 'INSERT OR REPLACE INTO g(a) VALUES(NULL) RETURNING *;'),
    'null_ignore_override': ('CREATE TABLE g(a NOT NULL,b AS(a+1) STORED);', 'INSERT OR IGNORE INTO g(a) VALUES(NULL) RETURNING *;SELECT * FROM g;'),
    'null_generated_ignore': ('CREATE TABLE g(a,b AS(a+1) STORED NOT NULL ON CONFLICT IGNORE);', 'INSERT INTO g(a) VALUES(NULL) RETURNING *;'),
    'null_generated_abort_first_pass': ('CREATE TABLE g(b AS(a+1) STORED NOT NULL ON CONFLICT IGNORE,a NOT NULL);', 'INSERT INTO g(a) VALUES(NULL);'),
    'null_generated_replace': ('CREATE TABLE g(a,b AS(a+1) STORED NOT NULL);', 'INSERT OR REPLACE INTO g(a) VALUES(NULL);'),
    'null_generated_recomputed': ('CREATE TABLE g(b AS(a+1) STORED NOT NULL,a NOT NULL ON CONFLICT REPLACE DEFAULT 2);', 'INSERT INTO g(a) VALUES(NULL) RETURNING *;'),
    'upsert_affinity_excluded': ('CREATE TABLE g(id INTEGER PRIMARY KEY,a REAL,b AS(typeof(a)) STORED);INSERT INTO g(id,a)VALUES(1,2);', "INSERT INTO g(id,a) VALUES(1,'003') ON CONFLICT(id) DO UPDATE SET a=typeof(excluded.a) RETURNING *;"),
    'upsert_generated_excluded': ('CREATE TABLE g(id INTEGER PRIMARY KEY,a INT,b AS(a+1) STORED);INSERT INTO g VALUES(1,2);', 'INSERT INTO g VALUES(1,5) ON CONFLICT(id) DO UPDATE SET a=excluded.b RETURNING *;'),
    'upsert_ignore_generated_notnull': ('CREATE TABLE g(id INTEGER PRIMARY KEY,a,b AS(a+1) STORED NOT NULL);INSERT INTO g VALUES(1,2);', 'INSERT OR IGNORE INTO g VALUES(1,NULL) ON CONFLICT(id) DO UPDATE SET a=9 RETURNING *;SELECT * FROM g;'),
    'upsert_abort_update': ('CREATE TABLE g(id INTEGER PRIMARY KEY,a,b AS(a+1) STORED NOT NULL);INSERT INTO g VALUES(1,2);', 'INSERT OR IGNORE INTO g VALUES(1,5) ON CONFLICT(id) DO UPDATE SET a=NULL RETURNING *;'),
    'upsert_generated_target': ('CREATE TABLE g(a,b AS(a+1) STORED UNIQUE);INSERT INTO g(a)VALUES(1);', 'INSERT INTO g(a) VALUES(1) ON CONFLICT(b) DO UPDATE SET a=excluded.b RETURNING *;'),
    'generated_check_update': ('CREATE TABLE g(a,b AS(a+1) STORED CHECK(b>0));INSERT INTO g(a)VALUES(1);', 'UPDATE g SET a=-2;'),
    'generated_check_ignore': ('CREATE TABLE g(a,b AS(a+1) STORED CHECK(b>0));INSERT INTO g(a)VALUES(1);', 'UPDATE OR IGNORE g SET a=-2 RETURNING *;SELECT * FROM g;'),
    'generated_check_unrelated': ('CREATE TABLE g(a,b AS(a+1) STORED CHECK(b>0),c);INSERT INTO g(a,c)VALUES(1,2);', 'UPDATE g SET c=9 RETURNING *;'),
    'stored_select_mutation': ('CREATE TABLE g(a,b AS(a+1) STORED);INSERT INTO g(a)VALUES(1),(2);', 'INSERT INTO g SELECT a+10 FROM g;SELECT * FROM g ORDER BY a;'),
    'stored_default_multi': ('CREATE TABLE g(a DEFAULT 3,b AS(a+1) STORED,c);', 'INSERT INTO g(c) VALUES(1),(2);SELECT * FROM g;'),
    'rename_chain': ('CREATE TABLE g(a,b AS(a+1) STORED,c AS(b+1) STORED);INSERT INTO g(a)VALUES(1);', 'ALTER TABLE g RENAME b TO renamed;UPDATE g SET a=3 RETURNING *;'),
    'rename_cast': ('CREATE TABLE g(a,b AS(CAST(a AS TEXT)) STORED);INSERT INTO g(a)VALUES(1);', 'ALTER TABLE g RENAME a TO renamed;UPDATE g SET renamed=3 RETURNING *;'),
    'drop_chain': ('CREATE TABLE g(a,b AS(a+1) STORED,c AS(b+1) STORED);', 'ALTER TABLE g DROP b;'),
    'add_stored_unknown': ('CREATE TABLE g(a);', 'ALTER TABLE g ADD b AS(missing+1) STORED;'),
    'add_stored_loop': ('CREATE TABLE g(a);', 'ALTER TABLE g ADD b AS(b+1) STORED;INSERT INTO g(a)VALUES(1);'),
    'strict_generated_update': ('CREATE TABLE g(a ANY,b INT AS(a) STORED) STRICT;INSERT INTO g(a)VALUES(1);', "UPDATE OR IGNORE g SET a='bad';"),
})
EXTRA.update({
    'eval_order_independent': ('CREATE TABLE g(a,b AS(abs(a)) STORED,c AS(json(a)) STORED);', 'INSERT INTO g(a) VALUES(-9223372036854775808);'),
    'eval_order_deferred': ('CREATE TABLE g(a,b AS(c+1) STORED,c AS(abs(a)) STORED,d AS(json(a)) STORED);', 'INSERT INTO g(a) VALUES(-9223372036854775808);'),
    'loop_indirect': ('CREATE TABLE g(a,b AS(c) STORED,c AS(c) STORED);', 'INSERT INTO g(a) VALUES(1);'),
    'insert_generated_case': (SETUP, 'INSERT INTO t(ID,A,B) VALUES(2,5,6);'),
    'update_generated_case': (SETUP, 'UPDATE t SET B=9;'),
    'default_explicit': ('CREATE TABLE g(a DEFAULT 3,b AS(a+1) STORED);', 'INSERT INTO g(a) DEFAULT VALUES;'),
    'default_generated_explicit': ('CREATE TABLE g(a DEFAULT 3,b AS(a+1) STORED);', 'INSERT INTO g(b) DEFAULT VALUES;'),
    'default_after_as': ('', 'CREATE TABLE g(a,b AS(a+1) STORED DEFAULT 3);'),
    'double_as': ('', 'CREATE TABLE g(a,b AS(a+1) STORED AS(a+2) STORED);'),
    'date_clock_literal': ("CREATE TABLE g(a,b AS(date('now')) STORED);", 'INSERT INTO g(a)VALUES(1);'),
    'date_clock_column': ('CREATE TABLE g(a,b AS(datetime(a)) STORED);', "INSERT INTO g(a)VALUES('now');"),
    'date_clock_empty': ('CREATE TABLE g(a,b AS(date()) STORED);', 'INSERT INTO g(a)VALUES(1);'),
    'date_timezone': ("CREATE TABLE g(a,b AS(date(a,'localtime')) STORED);", "INSERT INTO g(a)VALUES('2026-10-28');"),
    'date_invalid_prefix': ("CREATE TABLE g(a,b AS(date(a,'localtime')) STORED);", "INSERT INTO g(a)VALUES('invalid');SELECT * FROM g;"),
    'date_lazy': ("CREATE TABLE g(a,b AS(CASE WHEN a=0 THEN 1 ELSE date('now') END) STORED);", 'INSERT INTO g(a)VALUES(0)RETURNING *;'),
    'date_deterministic': ("CREATE TABLE g(a,b AS(date(a,'+1 day')) STORED);", "INSERT INTO g(a)VALUES('2026-10-28')RETURNING *;"),
    'strict_early_type': ('CREATE TABLE g(a INT,b INT AS(abs(-9223372036854775808)) STORED) STRICT;', "INSERT INTO g(a)VALUES('bad');"),
    'strict_null_before_generated_type': ("CREATE TABLE g(a INT NOT NULL,b INT AS('bad') STORED) STRICT;", 'INSERT INTO g(a)VALUES(NULL);'),
    'add_empty_notnull': ('CREATE TABLE g(a);', 'ALTER TABLE g ADD b AS(a+1) STORED NOT NULL;INSERT INTO g(a)VALUES(1)RETURNING *;'),
    'add_populated_unknown': ('CREATE TABLE g(a);INSERT INTO g VALUES(1);', 'ALTER TABLE g ADD b AS(missing+1) STORED;'),
})
EXTRA.update({
    'eval_order_error_priority': ("CREATE TABLE g(a,b AS(abs(a)) STORED,c AS(json(a||'x')) STORED);", 'INSERT INTO g(a)VALUES(-9223372036854775808);'),
    'eval_order_dependency_error': ("CREATE TABLE g(a,b AS(c+1) STORED,c AS(abs(a)) STORED,d AS(json(a||'x')) STORED);", 'INSERT INTO g(a)VALUES(-9223372036854775808);'),
})
for name,(setup,sql) in EXTRA.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(StoredGeneratedColumns,'test_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_STORED_GENERATED_SEED','368001')))
for i in range(12):
    value=rng.randrange(-10000,10000);offset=rng.randrange(1,100)
    setup=f'CREATE TABLE g(a INTEGER,b INTEGER AS(a+{offset}) STORED);'
    sql=f'INSERT INTO g(a) VALUES({value});SELECT * FROM g;UPDATE g SET a=a+1 RETURNING a,b;'
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(StoredGeneratedColumns,f'test_fresh_{i}_{suffix}',case(sql,mode,setup))
if __name__=='__main__':
    unittest.main()
