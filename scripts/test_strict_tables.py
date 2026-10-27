#!/usr/bin/env python3
"""STRICT table schema admission, lossless typing, ANY affinity and persistence."""
import os
import random
import unittest
from test_check_add_column import case

class StrictTables(unittest.TestCase):
    pass

SETUP = 'CREATE TABLE t(id INTEGER PRIMARY KEY,i INT,r REAL,s TEXT,b BLOB,a ANY) STRICT;'
QUERIES = {
    'empty_metadata': 'PRAGMA table_info(t);PRAGMA table_xinfo(t);',
    'valid': "INSERT INTO t VALUES(1,'12','2.5',23,x'0102','000123');SELECT *,typeof(i),typeof(r),typeof(s),typeof(b),typeof(a) FROM t;",
    'any_text': "INSERT INTO t(id,a) VALUES(1,'000123');SELECT a,typeof(a),a=123 FROM t;",
    'any_integer': 'INSERT INTO t(id,a) VALUES(1,123);SELECT a,typeof(a) FROM t;',
    'any_real': 'INSERT INTO t(id,a) VALUES(1,1.5);SELECT a,typeof(a) FROM t;',
    'any_blob': "INSERT INTO t(id,a) VALUES(1,x'3132');SELECT hex(a),typeof(a) FROM t;",
    'nulls': 'INSERT INTO t VALUES(NULL,NULL,NULL,NULL,NULL,NULL);SELECT * FROM t;',
    'int_real_lossless': 'INSERT INTO t(id,i) VALUES(1,1.0);SELECT i,typeof(i) FROM t;',
    'int_real_lossy': 'INSERT INTO t(id,i) VALUES(1,1.5);',
    'int_text_numeric': "INSERT INTO t(id,i) VALUES(1,'  +001.0 ');SELECT i,typeof(i) FROM t;",
    'int_text_bad': "INSERT INTO t(id,i) VALUES(1,'one');",
    'int_blob_bad': "INSERT INTO t(id,i) VALUES(1,x'31');",
    'real_text_bad': "INSERT INTO t(id,r) VALUES(1,'one');",
    'real_int': 'INSERT INTO t(id,r) VALUES(1,9223372036854775807);SELECT r,typeof(r) FROM t;',
    'text_real': 'INSERT INTO t(id,s) VALUES(1,1.5);SELECT s,typeof(s) FROM t;',
    'text_blob_bad': "INSERT INTO t(id,s) VALUES(1,x'31');",
    'blob_text_bad': "INSERT INTO t(id,b) VALUES(1,'one');",
    'blob_integer_bad': 'INSERT INTO t(id,b) VALUES(1,1);',
    'ignore_datatype': "INSERT OR IGNORE INTO t(id,i) VALUES(1,'one');SELECT count(*) FROM t;",
    'replace_datatype': "INSERT OR REPLACE INTO t(id,i) VALUES(1,'one');",
    'multi_abort': "INSERT INTO t(id,i) VALUES(1,1),(2,'bad');",
    'update_bad': "INSERT INTO t(id,i) VALUES(1,1);UPDATE t SET i='bad';",
    'update_valid': "INSERT INTO t(id,i,a) VALUES(1,1,0);UPDATE t SET i='002',a='002';SELECT i,a,typeof(i),typeof(a) FROM t;",
    'upsert_bad': "INSERT INTO t(id,i) VALUES(1,1);INSERT INTO t(id,i) VALUES(1,'bad') ON CONFLICT(id) DO UPDATE SET i=excluded.i;",
    'upsert_update_bad': "INSERT INTO t(id,i) VALUES(1,1);INSERT INTO t(id,i) VALUES(1,2) ON CONFLICT(id) DO UPDATE SET i='bad';",
    'upsert_valid': "INSERT INTO t(id,i,a) VALUES(1,1,1);INSERT INTO t(id,i,a) VALUES(1,'2','002') ON CONFLICT(id) DO UPDATE SET i=excluded.i,a=excluded.a;SELECT i,a,typeof(a) FROM t;",
    'insert_select': "INSERT INTO t(id,i,a) SELECT 1,'003','003';SELECT i,a,typeof(a) FROM t;",
    'insert_select_bad': "INSERT INTO t(id,i) SELECT 1,'bad';",
    'ctas_from_any': "INSERT INTO t(id,a) VALUES(1,'003');CREATE TABLE c AS SELECT a FROM t;SELECT a,typeof(a) FROM c;PRAGMA table_info(c);",
    'any_comparison': "INSERT INTO t(id,a) VALUES(1,'003'),(2,3);SELECT id,a='003',a=3,3=a FROM t ORDER BY id;",
    'rename': 'ALTER TABLE t RENAME TO renamed;PRAGMA table_info(renamed);',
    'rename_column': 'ALTER TABLE t RENAME COLUMN a TO renamed;PRAGMA table_info(t);',
    'drop_column': 'ALTER TABLE t DROP COLUMN a;PRAGMA table_info(t);',
    'add_column': 'ALTER TABLE t ADD COLUMN z INT DEFAULT 3;PRAGMA table_info(t);',
    'add_untyped': 'ALTER TABLE t ADD COLUMN z;',
    'add_bad_type': 'ALTER TABLE t ADD COLUMN z FLOAT;',
    'add_any': "ALTER TABLE t ADD COLUMN z ANY DEFAULT '003';INSERT INTO t(id) VALUES(1);SELECT z,typeof(z) FROM t;",
    'transaction': "BEGIN;INSERT INTO t(id,a) VALUES(1,'003');ROLLBACK;SELECT count(*) FROM t;",
}
QUERIES.update({
    'table_list': 'PRAGMA table_list;',
    'table_list_main': 'PRAGMA main.table_list;',
    'table_list_temp': 'PRAGMA temp.table_list;',
    'table_list_target': 'PRAGMA table_list(t);',
    'table_list_case': 'PRAGMA table_list(T);',
    'table_list_catalog_legacy': 'PRAGMA table_list(sqlite_master);',
    'table_list_catalog_preferred': 'PRAGMA table_list(sqlite_schema);',
    'table_list_temp_legacy': 'PRAGMA table_list(sqlite_temp_master);',
    'table_list_function': 'SELECT * FROM pragma_table_list();',
    'table_list_function_null': 'SELECT * FROM pragma_table_list(NULL);',
    'table_list_function_target': "SELECT * FROM pragma_table_list('t');",
    'table_list_function_arity': "SELECT * FROM pragma_table_list('t','main');",
    'table_list_function_hidden': "SELECT schema,name,strict,arg FROM pragma_table_list('t');",
    'table_list_function_filter': 'SELECT name,ncol FROM pragma_table_list() WHERE strict=1;',
    'table_list_after_create': 'CREATE TABLE ordinary(x);PRAGMA table_list;',
    'table_list_after_alter': 'ALTER TABLE t RENAME TO renamed;PRAGMA table_list;',
    'table_list_after_drop': 'DROP TABLE t;PRAGMA table_list;',
})
for name, sql in QUERIES.items():
    for suffix, mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(StrictTables,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
CREATES = {
    'basic': 'CREATE TABLE s(x TEXT) STRICT;',
    'all_types': 'CREATE TABLE s(a ANY,b BLOB,c INT,d INTEGER,e REAL,f TEXT) STRICT;',
    'quoted_type': 'CREATE TABLE s(x "iNt") STRICT;',
    'missing_type': 'CREATE TABLE s(x) STRICT;',
    'unknown_type': 'CREATE TABLE s(x FLOAT) STRICT;',
    'type_precision': 'CREATE TABLE s(x INT(5)) STRICT;',
    'not_null': 'CREATE TABLE s(x INT NOT NULL) STRICT;INSERT INTO s VALUES(NULL);',
    'text_primary_null': 'CREATE TABLE s(x TEXT PRIMARY KEY) STRICT;PRAGMA table_info(s);INSERT INTO s VALUES(NULL);',
    'int_primary_null': 'CREATE TABLE s(x INT PRIMARY KEY) STRICT;PRAGMA table_info(s);INSERT INTO s VALUES(NULL);',
    'integer_primary_null': 'CREATE TABLE s(x INTEGER PRIMARY KEY) STRICT;INSERT INTO s VALUES(NULL);SELECT * FROM s;',
    'table_primary': 'CREATE TABLE s(x TEXT,PRIMARY KEY(x)) STRICT;PRAGMA table_info(s);INSERT INTO s VALUES(NULL);',
    'default_bad': "CREATE TABLE s(x INT DEFAULT 'bad') STRICT;INSERT INTO s DEFAULT VALUES;",
    'default_any': "CREATE TABLE s(x ANY DEFAULT '003') STRICT;INSERT INTO s DEFAULT VALUES;SELECT x,typeof(x) FROM s;",
    'unique_any': "CREATE TABLE s(x ANY UNIQUE) STRICT;INSERT INTO s VALUES('003'),(3);SELECT x,typeof(x) FROM s ORDER BY rowid;",
    'check_any': "CREATE TABLE s(x ANY CHECK(typeof(x)='text')) STRICT;INSERT INTO s VALUES('003');SELECT x,typeof(x) FROM s;",
    'foreign_any': "PRAGMA foreign_keys=ON;CREATE TABLE p(x TEXT PRIMARY KEY);INSERT INTO p VALUES('003');CREATE TABLE s(x ANY REFERENCES p(x)) STRICT;INSERT INTO s VALUES('003');PRAGMA foreign_key_check;",
    'if_not_exists': 'CREATE TABLE s(x);CREATE TABLE IF NOT EXISTS s(x INT) STRICT;PRAGMA table_info(s);',
}
CREATES.update({
    'ordinary_any_control': "CREATE TABLE s(x ANY);INSERT INTO s VALUES('003');SELECT x,typeof(x) FROM s;",
    'ordinary_after_strict': "CREATE TABLE c(x ANY) STRICT;CREATE TABLE s(x ANY);INSERT INTO c VALUES('003');INSERT INTO s VALUES('003');SELECT typeof(x) FROM c UNION ALL SELECT typeof(x) FROM s;",
    'notnull_type_priority': "CREATE TABLE s(x INT NOT NULL,y INT) STRICT;INSERT INTO s VALUES(NULL,'bad');",
    'type_check_priority': "CREATE TABLE s(x INT CHECK(x=0)) STRICT;INSERT INTO s VALUES('bad');",
    'update_ignore_type': "CREATE TABLE s(x INT) STRICT;INSERT INTO s VALUES(1);UPDATE OR IGNORE s SET x='bad';",
    'update_notnull_type_priority': "CREATE TABLE s(x INT NOT NULL,y INT) STRICT;INSERT INTO s VALUES(1,2);UPDATE s SET x=NULL,y='bad';",
    'default_ignore_type': "CREATE TABLE s(x INT DEFAULT 'bad') STRICT;INSERT OR IGNORE INTO s DEFAULT VALUES;",
    'if_not_exists_invalid_type': 'CREATE TABLE s(x);CREATE TABLE IF NOT EXISTS s(x FLOAT) STRICT;PRAGMA table_info(s);',
    'if_not_exists_untyped': 'CREATE TABLE s(x);CREATE TABLE IF NOT EXISTS s(x) STRICT;PRAGMA table_info(s);',
    'any_parent_key': "PRAGMA foreign_keys=ON;CREATE TABLE p(x ANY PRIMARY KEY) STRICT;INSERT INTO p VALUES('003');CREATE TABLE s(x REFERENCES p(x));INSERT INTO s VALUES('003');PRAGMA foreign_key_check;",
    'any_subquery': "CREATE TABLE s(x ANY) STRICT;INSERT INTO s VALUES('003'),(3);SELECT x,x IN (SELECT 3),x IN (SELECT '003') FROM s ORDER BY rowid;",
    'any_derived': "CREATE TABLE s(x ANY) STRICT;INSERT INTO s VALUES('003'),(3);WITH c AS MATERIALIZED (SELECT x FROM s) SELECT x,typeof(x),x=3 FROM c ORDER BY x;",
    'add_bad_default': "CREATE TABLE s(x INT) STRICT;INSERT INTO s VALUES(1);ALTER TABLE s ADD y INT DEFAULT 'bad';SELECT x,y,typeof(y) FROM s;",
    'strict_table_foreign_drop': 'CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE s(x INT,y INT,FOREIGN KEY(x) REFERENCES p(id)) STRICT;ALTER TABLE s DROP x;',
    'strict_table_foreign_rename': 'CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE s(x INT,y INT,FOREIGN KEY(x) REFERENCES p(id)) STRICT;ALTER TABLE s RENAME COLUMN x TO renamed;PRAGMA foreign_key_list(s);',
    'any_returning': "CREATE TABLE s(x ANY) STRICT;INSERT INTO s VALUES('003') RETURNING x,typeof(x);",
})
CREATES['table_list_autoincrement'] = 'CREATE TABLE s(id INTEGER PRIMARY KEY AUTOINCREMENT,x ANY) STRICT;PRAGMA table_list;'
CREATES.update({
    'table_list_auto_alter': 'CREATE TABLE s(id INTEGER PRIMARY KEY AUTOINCREMENT,x ANY) STRICT;ALTER TABLE s ADD y INT;PRAGMA table_list;',
    'table_list_auto_rename': 'CREATE TABLE s(id INTEGER PRIMARY KEY AUTOINCREMENT,x ANY) STRICT;ALTER TABLE s RENAME TO renamed;PRAGMA table_list;',
    'table_list_auto_drop': 'CREATE TABLE s(id INTEGER PRIMARY KEY AUTOINCREMENT,x ANY) STRICT;DROP TABLE s;PRAGMA table_list;',
    'table_list_auto_second': 'CREATE TABLE s(id INTEGER PRIMARY KEY AUTOINCREMENT,x ANY) STRICT;CREATE TABLE q(id INTEGER PRIMARY KEY AUTOINCREMENT) STRICT;PRAGMA table_list;',
    'table_list_auto_rollback': 'BEGIN;CREATE TABLE s(id INTEGER PRIMARY KEY AUTOINCREMENT,x ANY) STRICT;ROLLBACK;PRAGMA table_list;',
})
for name, sql in CREATES.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(StrictTables,'test_create_'+name+'_'+suffix,case(sql,mode,''))
EXTRA = {
    'strict_add_existing_bad_check': ('CREATE TABLE s(x INT CHECK(x>0)) STRICT;PRAGMA ignore_check_constraints=ON;INSERT INTO s VALUES(-1);', 'ALTER TABLE s ADD y INT DEFAULT 3;'),
    'strict_add_existing_bad_type': (".dbconfig defensive off\nCREATE TABLE s(x INT);INSERT INTO s VALUES('bad');PRAGMA writable_schema=ON;UPDATE sqlite_schema SET sql=sql||' STRICT' WHERE name='s';", 'ALTER TABLE s ADD y ANY;'),
}
EXTRA.update({
    'table_list_auto_reopened': ('CREATE TABLE s(id INTEGER PRIMARY KEY AUTOINCREMENT,x ANY) STRICT;', 'PRAGMA table_list;'),
    'table_list_auto_rehash': ('CREATE TABLE a(x);CREATE TABLE b(x);CREATE TABLE c(x);', 'CREATE TABLE s(id INTEGER PRIMARY KEY AUTOINCREMENT) STRICT;PRAGMA table_list;'),
    'table_list_many': (''.join(f'CREATE TABLE n{i}(x);' for i in range(20)) + 'CREATE TABLE s(x ANY) STRICT;', 'SELECT * FROM pragma_table_list();'),
})
for name,(setup,sql) in EXTRA.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(StrictTables,'test_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_STRICT_SEED','366501')))
for i in range(12):
    n=rng.randrange(1,100000)
    sql=f"INSERT INTO t(id,i,a) VALUES(1,'00{n}','00{n}');SELECT i,a,typeof(i),typeof(a) FROM t;"
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(StrictTables,f'test_fresh_{i}_{suffix}',case(sql,mode,SETUP))
if __name__=='__main__':
    unittest.main()
