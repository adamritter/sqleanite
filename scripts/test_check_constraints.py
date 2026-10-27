#!/usr/bin/env python3
"""CHECK enforcement, evaluation order, conflict policies and foreign files."""
import os,random,unittest
from test_pragma_tables import case
class CheckConstraints(unittest.TestCase): pass
SCRIPTS={
 'column_ok':'CREATE TABLE t(x INTEGER CHECK(x>0));INSERT INTO t VALUES(1),(NULL);SELECT * FROM t;',
 'column_fail':'CREATE TABLE t(x INTEGER CHECK(x>0));INSERT INTO t VALUES(-1);',
 'named':'CREATE TABLE t(x INTEGER CONSTRAINT positive CHECK(x>0));INSERT INTO t VALUES(0);',
 'table_named':'CREATE TABLE t(x,y,CONSTRAINT ordered CHECK(x<y));INSERT INTO t VALUES(2,1);',
 'multiple_table':'CREATE TABLE t(x,y,CHECK(x>0),CHECK(y>x));INSERT INTO t VALUES(1,2);INSERT INTO t VALUES(1,0);',
 'multiple_column':'CREATE TABLE t(x CHECK(x>0) CHECK(x<10));INSERT INTO t VALUES(-1);',
 'null':'CREATE TABLE t(x CHECK(NULL));INSERT INTO t VALUES(1);SELECT * FROM t;',
 'numeric_false':"CREATE TABLE t(x CHECK('abc'));INSERT INTO t VALUES(1);",
 'numeric_true':"CREATE TABLE t(x CHECK('1abc'));INSERT INTO t VALUES(1);SELECT * FROM t;",
 'affinity':"CREATE TABLE t(x INTEGER CHECK(typeof(x)='integer'));INSERT INTO t VALUES('17');SELECT * FROM t;",
 'cross_column':'CREATE TABLE t(x INTEGER,y INTEGER,CHECK(x<=y));INSERT INTO t VALUES(1,2);UPDATE t SET y=0;',
 'ignore':'CREATE TABLE t(x CHECK(x>0));INSERT OR IGNORE INTO t VALUES(1),(-1),(2);SELECT * FROM t;',
 'replace_aborts':'CREATE TABLE t(x INTEGER PRIMARY KEY,v CHECK(v>0));INSERT INTO t VALUES(1,4);INSERT OR REPLACE INTO t VALUES(1,-1);',
 'update_ignore':'CREATE TABLE t(x INTEGER PRIMARY KEY,v CHECK(v>0));INSERT INTO t VALUES(1,1),(2,2);UPDATE OR IGNORE t SET v=v-2;SELECT * FROM t;',
 'update_default':'CREATE TABLE t(x INTEGER PRIMARY KEY,v CHECK(v>0));INSERT INTO t VALUES(1,1),(2,2);UPDATE t SET v=v-2;',
 'update_unrelated':'CREATE TABLE t(x CHECK(x>0),y);INSERT INTO t VALUES(1,0);UPDATE t SET y=7;SELECT * FROM t;',
 'upsert_update':'CREATE TABLE t(x INTEGER PRIMARY KEY,v CHECK(v>0));INSERT INTO t VALUES(1,1);INSERT INTO t VALUES(1,2) ON CONFLICT(x) DO UPDATE SET v=-1;',
 'upsert_nothing':'CREATE TABLE t(x INTEGER PRIMARY KEY,v CHECK(v>0));INSERT INTO t VALUES(1,1);INSERT INTO t VALUES(1,-1) ON CONFLICT DO NOTHING;',
 'unique_order':'CREATE TABLE t(x UNIQUE,v CHECK(v>0));INSERT INTO t VALUES(1,1);INSERT INTO t VALUES(1,-1);',
 'notnull_order':'CREATE TABLE t(x NOT NULL,v CHECK(v>0));INSERT INTO t VALUES(NULL,-1);',
 'returning':'CREATE TABLE t(x CHECK(x>0));INSERT INTO t VALUES(1),(2) RETURNING x;SELECT * FROM t;',
 'transaction':'CREATE TABLE t(x CHECK(x>0));BEGIN;INSERT INTO t VALUES(1);ROLLBACK;SELECT * FROM t;',
 'rowid':'CREATE TABLE t(x CHECK(rowid>0));INSERT INTO t VALUES(1);INSERT INTO t(rowid,x) VALUES(-1,2);',
 'runtime_error':'CREATE TABLE t(x CHECK(abs(x)>0));INSERT INTO t VALUES(-9223372036854775808);',
 'unknown_column':'CREATE TABLE t(x CHECK(missing>0));',
 'subquery_forbidden':'CREATE TABLE t(x CHECK((SELECT 1)));',
 'scalar_function':'CREATE TABLE t(x TEXT CHECK(length(x)>2));INSERT INTO t VALUES(\'long\');SELECT * FROM t;',
 'case_short_circuit':'CREATE TABLE t(x CHECK(CASE WHEN x=0 THEN 1 ELSE abs(-9223372036854775808) END));INSERT INTO t VALUES(0);SELECT * FROM t;',
}
SCRIPTS.update({
 'quoted_diagnostic': 'CREATE TABLE t(x CHECK("x">0));INSERT INTO t VALUES(0);',
 'escaped_diagnostic': "CREATE TABLE t(x CHECK('ab''c'||x));INSERT INTO t VALUES(1);",
 'preceding_constraint_name': 'CREATE TABLE t(x CONSTRAINT a NOT NULL CHECK(x>0));INSERT INTO t VALUES(0);',
 'repeated_constraint_name': 'CREATE TABLE t(x CONSTRAINT a CHECK(x<10) CHECK(x>0));INSERT INTO t VALUES(0);',
 'rename_function': "CREATE TABLE t(length TEXT CHECK(length(length)>0));ALTER TABLE t RENAME COLUMN length TO val;INSERT INTO t VALUES('');",
 'rename_literal': "CREATE TABLE t(v TEXT CHECK(v<>'v'));ALTER TABLE t RENAME COLUMN v TO value;INSERT INTO t VALUES('v');",
 'rename_cast_type': "CREATE TABLE t(real INTEGER,x TEXT CHECK(CAST(x AS real)>0));ALTER TABLE t RENAME COLUMN real TO value;INSERT INTO t VALUES(1,'0');",
 'rename_collation': "CREATE TABLE t(binary TEXT CHECK(binary COLLATE binary <> 'x'));ALTER TABLE t RENAME COLUMN binary TO value;INSERT INTO t VALUES('x');",
 'rename_qualifier': 'CREATE TABLE t(t INTEGER CHECK(t.t>0));ALTER TABLE t RENAME COLUMN t TO value;INSERT INTO t VALUES(0);',
 'rename_table': 'CREATE TABLE t(x CHECK(t.x>0));ALTER TABLE t RENAME TO u;INSERT INTO u VALUES(0);',
 'rename_table_unique': 'CREATE TABLE t(x INTEGER,UNIQUE(x),CHECK(x>0));ALTER TABLE t RENAME COLUMN x TO value;INSERT INTO t VALUES(0);',
 'rename_automatic_indexes': "CREATE TABLE t(x TEXT UNIQUE,y TEXT PRIMARY KEY,CHECK(length(x)>0));INSERT INTO t VALUES('a','a');ALTER TABLE t RENAME TO u;SELECT name FROM sqlite_schema WHERE type='index' ORDER BY name;INSERT INTO u VALUES('a','b');",
 'insert_select': 'CREATE TABLE t(x CHECK(x>0));INSERT OR IGNORE INTO t SELECT column1 FROM (VALUES(1),(-1),(2));SELECT * FROM t;',
 'update_returning': 'CREATE TABLE t(id INTEGER PRIMARY KEY,v CHECK(v>0));INSERT INTO t VALUES(1,1),(2,2);UPDATE OR IGNORE t SET v=v-1 RETURNING id,v;SELECT * FROM t;',
 'update_rowid': 'CREATE TABLE t(x CHECK(rowid>0));INSERT INTO t VALUES(1);UPDATE t SET rowid=-1;',
 'upsert_update_abort': 'CREATE TABLE t(x INTEGER PRIMARY KEY,v CHECK(v>0));INSERT INTO t VALUES(1,1);INSERT OR IGNORE INTO t VALUES(1,2) ON CONFLICT(x) DO UPDATE SET v=-1;',
 'upsert_ignore': 'CREATE TABLE t(x INTEGER PRIMARY KEY,v CHECK(v>0));INSERT INTO t VALUES(1,1);INSERT OR IGNORE INTO t VALUES(1,-1) ON CONFLICT DO NOTHING;SELECT * FROM t;',
})
for name,sql in SCRIPTS.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(CheckConstraints,'test_'+name+'_'+suffix,case(sql,mode,'CREATE TABLE seed(x);'))
FOREIGN='CREATE TABLE t(id INTEGER PRIMARY KEY,v INTEGER CONSTRAINT positive CHECK(v>0));INSERT INTO t VALUES(1,10);'
for name,sql in {'read':'SELECT * FROM t;','insert':'INSERT INTO t VALUES(2,20);SELECT * FROM t;', 'reject':'INSERT INTO t VALUES(2,-1);','update':'UPDATE t SET v=20;SELECT * FROM t;','update_reject':'UPDATE t SET v=-1;','ignore':'INSERT OR IGNORE INTO t VALUES(2,-1);SELECT * FROM t;','delete':'DELETE FROM t;SELECT * FROM t;','schema':'SELECT sql FROM sqlite_schema;','add_column':'ALTER TABLE t ADD COLUMN other;INSERT INTO t(id,v) VALUES(2,-1);','rename_column':'ALTER TABLE t RENAME COLUMN v TO value;INSERT INTO t(id,value) VALUES(2,-1);'}.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(CheckConstraints,'test_foreign_'+name+'_'+suffix,case(sql,mode,FOREIGN))
for name,sql in {'read':'SELECT * FROM t;','delete':'DELETE FROM t;SELECT * FROM t;'}.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(CheckConstraints,'test_existing_violation_'+name+'_'+suffix,case(sql,mode,'CREATE TABLE t(x CHECK(x>0));PRAGMA ignore_check_constraints=ON;INSERT INTO t VALUES(-1);'))
rng=random.Random(int(os.environ.get('SQLEANITE_CHECK_SEED','360100')))
for i in range(12):
 bound=rng.randrange(-1000,1000);values=[rng.randrange(bound-8,bound+9) for _ in range(10)]
 sql=f'CREATE TABLE t(x INTEGER CHECK(x>{bound}));INSERT OR IGNORE INTO t VALUES'+','.join(f'({v})' for v in values)+';SELECT x FROM t ORDER BY rowid;'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(CheckConstraints,'test_fresh_'+str(i)+'_'+suffix,case(sql,mode,'CREATE TABLE seed(x);'))
if __name__=='__main__':unittest.main()
