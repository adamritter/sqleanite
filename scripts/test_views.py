#!/usr/bin/env python3
"""Persistent VIEW SQL, source/catalog identity and source-aware reads."""
import os
import random
import unittest
from test_check_add_column import case

class Views(unittest.TestCase):
    pass

SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'a',2),(2,'A',4),(3,'b',6);"
CREATE={
 'simple': 'CREATE VIEW q AS SELECT id,v,n FROM t;SELECT * FROM q ORDER BY id;',
 'filter': 'CREATE VIEW q AS SELECT id,v,n FROM t WHERE n>2;SELECT id FROM q WHERE n<6 ORDER BY id;',
 'aliases': 'CREATE VIEW q(a,b) AS SELECT id,v FROM t;SELECT a,b FROM q ORDER BY a;',
 'quoted': 'CREATE VIEW "odd view"("a a","b b") AS SELECT id,v FROM t;SELECT "a a","b b" FROM "odd view" ORDER BY "a a";',
 'if_not_exists': 'CREATE VIEW IF NOT EXISTS q AS SELECT id FROM t;CREATE VIEW IF NOT EXISTS q AS SELECT missing;SELECT * FROM q ORDER BY id;',
 'duplicate': 'CREATE VIEW q AS SELECT id FROM t;CREATE VIEW q AS SELECT id FROM t;',
 'table_collision': 'CREATE VIEW t AS SELECT 1;',
 'index_collision': 'CREATE INDEX q ON t(n);CREATE VIEW q AS SELECT 1;',
 'deferred_missing_table': 'CREATE VIEW q AS SELECT * FROM missing;SELECT 17;',
 'deferred_missing_column': 'CREATE VIEW q AS SELECT missing FROM t;SELECT 17;',
 'missing_table_read': 'CREATE VIEW q AS SELECT * FROM missing;SELECT * FROM q;',
 'missing_column_read': 'CREATE VIEW q AS SELECT missing FROM t;SELECT * FROM q;',
 'alias_width_deferred': 'CREATE VIEW q(a,b) AS SELECT id FROM t;SELECT 17;',
 'alias_width_read': 'CREATE VIEW q(a,b) AS SELECT id FROM t;SELECT * FROM q;',
 'union': "CREATE VIEW q AS SELECT v FROM t UNION SELECT 'A';SELECT * FROM q ORDER BY v;",
 'group': 'CREATE VIEW q AS SELECT v,count(*) AS c FROM t GROUP BY v;SELECT * FROM q ORDER BY v;',
 'nested': 'CREATE VIEW q AS SELECT id,v FROM t;CREATE VIEW r AS SELECT * FROM q;SELECT * FROM r ORDER BY id;',
 'self_cycle': 'CREATE VIEW q AS SELECT * FROM q;SELECT * FROM q;',
 'mutual_cycle': 'CREATE VIEW q AS SELECT * FROM r;CREATE VIEW r AS SELECT * FROM q;SELECT * FROM q;',
 'drop': 'CREATE VIEW q AS SELECT * FROM t;DROP VIEW q;SELECT * FROM t ORDER BY id;',
 'drop_if_missing': 'DROP VIEW IF EXISTS missing;SELECT 17;',
 'drop_missing': 'DROP VIEW missing;',
 'drop_table_as_view': 'DROP VIEW t;',
 'drop_view_as_table': 'CREATE VIEW q AS SELECT * FROM t;DROP TABLE q;',
 'write_view_insert': "CREATE VIEW q AS SELECT * FROM t;INSERT INTO q VALUES(4,'d',8);",
 'write_view_update': "CREATE VIEW q AS SELECT * FROM t;UPDATE q SET v='c';",
 'write_view_delete': 'CREATE VIEW q AS SELECT * FROM t;DELETE FROM q;',
 'index_view': 'CREATE VIEW q AS SELECT * FROM t;CREATE INDEX i ON q(n);',
 'catalog': 'CREATE VIEW q AS SELECT id,v FROM t;SELECT type,name,tbl_name,rootpage,sql FROM sqlite_schema ORDER BY name;',
 'table_info': 'CREATE VIEW q AS SELECT id,v,n FROM t;PRAGMA table_info(q);PRAGMA table_xinfo(q);',
 'pragma_function': "CREATE VIEW q AS SELECT id,v FROM t;SELECT cid,name,type,pk FROM pragma_table_info('q') ORDER BY cid;",
 'table_list': "CREATE VIEW q AS SELECT id,v FROM t;SELECT name,type,ncol,wr,strict FROM pragma_table_list WHERE name='q';",
 'begin_commit': 'BEGIN;CREATE VIEW q AS SELECT id,v FROM t;SELECT * FROM q ORDER BY id;COMMIT;SELECT * FROM q ORDER BY id;',
 'begin_rollback': 'BEGIN;CREATE VIEW q AS SELECT * FROM t;ROLLBACK;SELECT count(*) FROM t;',
 'savepoint': 'SAVEPOINT a;CREATE VIEW q AS SELECT * FROM t;SAVEPOINT b;DROP VIEW q;ROLLBACK TO b;RELEASE a;SELECT * FROM q ORDER BY id;',
 'rollback_drop': 'CREATE VIEW q AS SELECT * FROM t;BEGIN;DROP VIEW q;ROLLBACK;SELECT * FROM q ORDER BY id;',
 'counters': 'SELECT last_insert_rowid(),changes(),total_changes();CREATE VIEW q AS SELECT * FROM t;SELECT last_insert_rowid(),changes(),total_changes();DROP VIEW q;SELECT last_insert_rowid(),changes(),total_changes();',
}
READ={
 'star': 'SELECT * FROM q ORDER BY id;',
 'qualified': 'SELECT q.id,q.v FROM q WHERE q.n>2 ORDER BY q.id;',
 'alias': 'SELECT x.id,x.v FROM q AS x ORDER BY x.id;',
 'main': 'SELECT id FROM main.q ORDER BY id;',
 'expression': "SELECT upper(v),n*2 FROM q ORDER BY id;",
 'join': 'SELECT q.id,t.n FROM q JOIN t ON q.id=t.id ORDER BY q.id;',
 'derived': 'SELECT * FROM (SELECT id,v FROM q) AS d ORDER BY id;',
 'cte': 'WITH c AS (SELECT id,v FROM q) SELECT * FROM c ORDER BY id;',
 'scalar': 'SELECT (SELECT v FROM q WHERE id=1);',
 'correlated': 'SELECT t.id,(SELECT v FROM q WHERE q.id=t.id) FROM t ORDER BY t.id;',
 'in': 'SELECT id FROM t WHERE id IN (SELECT id FROM q WHERE n>2) ORDER BY id;',
 'rowid': 'SELECT rowid FROM q;',
 'ctas': 'CREATE TABLE c AS SELECT * FROM q;SELECT * FROM c ORDER BY id;PRAGMA table_info(c);',
 'insert_select': 'CREATE TABLE c AS SELECT * FROM t WHERE 0;INSERT INTO c SELECT * FROM q;SELECT * FROM c ORDER BY id;',
 'update_base': "UPDATE t SET v='changed' WHERE id=1;SELECT * FROM q ORDER BY id;",
 'base_insert': "INSERT INTO t VALUES(4,'d',8);SELECT * FROM q ORDER BY id;",
 'rename_base': 'ALTER TABLE t RENAME TO renamed;SELECT * FROM q ORDER BY id;',
 'rename_column': 'ALTER TABLE t RENAME COLUMN n TO amount;SELECT * FROM q ORDER BY id;',
 'drop_base': 'DROP TABLE t;SELECT * FROM q;',
 'table_info': 'PRAGMA table_info(q);PRAGMA table_xinfo(q);',
}
for name,sql in CREATE.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(Views,'test_create_'+name+'_'+suffix,case(sql,mode,SETUP))
for name,sql in READ.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(Views,'test_imported_'+name+'_'+suffix,case(sql,mode,SETUP+'CREATE VIEW q AS SELECT id,v,n FROM t;'))
EXTRA={
 'declared_collation': ("CREATE TABLE t(v TEXT COLLATE NOCASE);INSERT INTO t VALUES('a'),('A');", "CREATE VIEW q AS SELECT v FROM t;SELECT count(*) FROM q WHERE v='A';"),
 'declared_type': ('CREATE TABLE t(v VARCHAR(20),n DECIMAL(10,2));', 'CREATE VIEW q AS SELECT v,n,CAST(v AS TEXT) AS c,1 AS x FROM t;PRAGMA table_info(q);'),
 'first_projection': (SETUP, "CREATE VIEW q AS SELECT 'a' AS x UNION ALL SELECT v COLLATE NOCASE FROM t;SELECT x='A' FROM q;"),
 'with_body': (SETUP, 'CREATE VIEW q AS WITH c AS (SELECT id,v FROM t) SELECT * FROM c;SELECT * FROM q ORDER BY id;'),
}
for name,(setup,sql) in EXTRA.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(Views,'test_'+name+'_'+suffix,case(sql,mode,setup))
CONTROLS={
 'alter_invalid_view': (SETUP+'CREATE VIEW q AS SELECT missing FROM t;', 'ALTER TABLE t RENAME TO renamed;'),
 'alter_nested_invalid': (SETUP+'CREATE VIEW q AS SELECT n FROM t;CREATE VIEW r AS SELECT n FROM q;', 'ALTER TABLE t RENAME COLUMN n TO amount;'),
 'drop_view_column': (SETUP+'CREATE VIEW q AS SELECT n FROM t;', 'ALTER TABLE t DROP COLUMN n;'),
 'scalar_type': ('CREATE TABLE t(v VARCHAR(20));', 'CREATE VIEW q AS SELECT (SELECT v FROM t) AS x;PRAGMA table_info(q);CREATE TABLE c AS SELECT * FROM q;PRAGMA table_info(c);'),
 'scalar_correlated_type': ('CREATE TABLE t(v VARCHAR(20));', 'CREATE VIEW q AS SELECT (SELECT t.v) AS x FROM t;PRAGMA table_info(q);'),
 'scope_cte_shadow': (SETUP+'CREATE VIEW q AS SELECT id,v,n FROM t;', "WITH t AS (SELECT 99 AS id,'wrong' AS v,0 AS n) SELECT * FROM q ORDER BY id;"),
 'scope_outer_isolation': (SETUP+'CREATE VIEW q AS SELECT outer_t.n AS value;', 'SELECT (SELECT value FROM q) FROM t AS outer_t;'),
 'table_rename_roles': (SETUP+"CREATE VIEW q AS SELECT t.id,t.v AS t,'t' AS literal FROM t /* t stays */;", 'ALTER TABLE t RENAME TO renamed;SELECT * FROM q ORDER BY id;'),
 'table_rename_alias': (SETUP+'CREATE VIEW q AS SELECT a.id,a.v FROM t AS a;', 'ALTER TABLE t RENAME TO renamed;SELECT * FROM q ORDER BY id;'),
 'column_rename_roles': (SETUP+"CREATE VIEW q AS SELECT n AS n,'n' AS literal FROM t /* n stays */ ORDER BY n;", 'ALTER TABLE t RENAME COLUMN n TO amount;SELECT * FROM q;'),
 'column_rename_qualified': (SETUP+'CREATE VIEW q AS SELECT a.id,a.n FROM t AS a;', 'ALTER TABLE t RENAME COLUMN n TO amount;SELECT * FROM q ORDER BY id;'),
 'table_rename_scalar': (SETUP+'CREATE VIEW q AS SELECT (SELECT n FROM t WHERE id=1) AS x;', 'ALTER TABLE t RENAME TO renamed;SELECT * FROM q;'),
 'column_rename_scalar': (SETUP+'CREATE VIEW q AS SELECT (SELECT n FROM t WHERE id=1) AS x;', 'ALTER TABLE t RENAME COLUMN n TO amount;SELECT * FROM q;'),
 'column_rename_correlated': (SETUP+'CREATE VIEW q AS SELECT a.id,(SELECT a.n) AS x FROM t AS a;', 'ALTER TABLE t RENAME COLUMN n TO amount;SELECT * FROM q ORDER BY id;'),
 'column_rename_shadow': (SETUP+'CREATE TABLE u(n INTEGER);INSERT INTO u VALUES(77);CREATE VIEW q AS SELECT a.id,(SELECT n FROM u) AS x FROM t AS a;', 'ALTER TABLE t RENAME COLUMN n TO amount;SELECT * FROM q ORDER BY id;'),
 'table_rename_with': (SETUP+'CREATE VIEW q AS WITH c AS (SELECT id,v FROM t) SELECT * FROM c;', 'ALTER TABLE t RENAME TO renamed;SELECT * FROM q ORDER BY id;'),
 'type_operators': ('CREATE TABLE t(v VARCHAR(20));', 'CREATE VIEW q AS SELECT v,+v AS plus,v COLLATE NOCASE AS collated,CAST(v AS TEXT) AS casted FROM t;PRAGMA table_info(q);'),
 'catalog_rowid': (SETUP, "CREATE VIEW q AS SELECT * FROM t;CREATE TABLE u(x);DROP VIEW q;CREATE VIEW r AS SELECT * FROM u;SELECT rowid,type,name,tbl_name,rootpage FROM sqlite_schema WHERE type='view' ORDER BY rowid;"),
 'rollback_rename': (SETUP+'CREATE VIEW q AS SELECT * FROM t;', 'BEGIN;ALTER TABLE t RENAME TO renamed;ROLLBACK;SELECT * FROM q ORDER BY id;'),
 'savepoint_schema': (SETUP+'CREATE VIEW q AS SELECT id,v FROM t;', 'SAVEPOINT a;DROP VIEW q;CREATE VIEW r AS SELECT n FROM t;ROLLBACK TO a;RELEASE a;SELECT * FROM q ORDER BY id;'),
}
for name,(setup,sql) in CONTROLS.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(Views,'test_control_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_VIEW_SEED','371401')))
for i in range(8):
 bound=rng.randrange(-8,8);values=[rng.randrange(-10,10) for _ in range(rng.randrange(2,9))]
 setup='CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER);'+''.join(f'INSERT INTO t VALUES({j+1},{n});' for j,n in enumerate(values))
 sql=f'CREATE VIEW q AS SELECT id,n FROM t WHERE n>{bound};SELECT count(*),sum(n) FROM q;SELECT id FROM q ORDER BY id;'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(Views,f'test_fresh_{i}_{suffix}',case(sql,mode,setup))
for page_size in [512,1024,2048,8192,65536]:
 for label,sql,view in [
   ('create', 'CREATE VIEW q AS SELECT id,v,n FROM t;UPDATE t SET n=n+1;SELECT * FROM q ORDER BY id;', ''),
   ('imported', "UPDATE t SET v='changed' WHERE id=1;SELECT * FROM q ORDER BY id;", 'CREATE VIEW q AS SELECT id,v,n FROM t;'),
   ('drop', 'DROP VIEW q;SELECT * FROM t ORDER BY id;', 'CREATE VIEW q AS SELECT id,v,n FROM t;')]:
  setup=f'PRAGMA page_size={page_size};'+SETUP+view
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(Views,f'test_geometry_{page_size}_{label}_{suffix}',case(sql,mode,setup))
if __name__=='__main__':
 unittest.main()
