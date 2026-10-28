#!/usr/bin/env python3
"""Composite PRIMARY/UNIQUE table declarations and actual automatic key files."""
import os,random,unittest
from test_check_add_column import case
class CompositeTableKeys(unittest.TestCase):pass
TABLE='CREATE TABLE t(a TEXT,b INTEGER,v,PRIMARY KEY(a,b));'
ROWS="INSERT INTO t VALUES('A',1,'one'),('A',2,'two'),('b',1,'three'),(NULL,1,'nil'),('A',NULL,'nil2');"
BASE=TABLE+ROWS
OBSERVE="SELECT rowid,* FROM t ORDER BY rowid;PRAGMA table_info(t);PRAGMA index_list(t);PRAGMA index_xinfo('sqlite_autoindex_t_1');"
Q={
 'virtual_metadata':(BASE,"SELECT * FROM pragma_table_info('t');SELECT * FROM pragma_index_list('t');SELECT * FROM pragma_index_xinfo('sqlite_autoindex_t_1');"),
 'strict':("CREATE TABLE t(a TEXT,b INTEGER,v TEXT,PRIMARY KEY(a,b)) STRICT;INSERT INTO t VALUES('A',1,'one'),('A',2,'two');",OBSERVE),
 'strict_integer_null':("CREATE TABLE t(a TEXT,b INTEGER,v TEXT,PRIMARY KEY(a,b)) STRICT;","INSERT INTO t VALUES('A',NULL,'bad');"),
 'collated_unique':(TABLE.replace('PRIMARY KEY','UNIQUE').replace('a TEXT','a TEXT COLLATE NOCASE')+ROWS,"INSERT OR IGNORE INTO t VALUES('a',1,'duplicate');"+OBSERVE),
 'explicit_collated_unique':(TABLE.replace('PRIMARY KEY(a,b)','UNIQUE(a COLLATE NOCASE,b)')+ROWS,"INSERT OR IGNORE INTO t VALUES('a',1,'duplicate');"+OBSERVE),
 'strict_null':("CREATE TABLE t(a TEXT,b INTEGER,v TEXT,PRIMARY KEY(a,b)) STRICT;","INSERT INTO t VALUES(NULL,1,'bad');"),
 'collated_primary':(TABLE.replace('a TEXT','a TEXT COLLATE NOCASE')+ROWS,"INSERT OR IGNORE INTO t VALUES('a',1,'duplicate');"+OBSERVE),
 'repeated_key':(TABLE.replace('PRIMARY KEY(a,b)','UNIQUE(a,b),PRIMARY KEY(a,b)')+ROWS,OBSERVE),
 'create_rollback':('',"BEGIN;"+BASE+"ROLLBACK;SELECT count(*) FROM sqlite_schema;"),
 'create':('',BASE+OBSERVE),
 'open':(BASE,OBSERVE),
 'prefix':(BASE,"INSERT INTO t VALUES('A',3,'new');"+OBSERVE),
 'duplicate':(BASE,"INSERT INTO t VALUES('A',1,'duplicate');"),
 'ignore':(BASE,"INSERT OR IGNORE INTO t VALUES('A',1,'duplicate');"+OBSERVE),
 'replace':(BASE,"INSERT OR REPLACE INTO t VALUES('A',1,'replaced');"+OBSERVE),
 'nulls':(BASE,"INSERT INTO t VALUES(NULL,1,'null'),('A',NULL,'null2');"+OBSERVE),
 'update':(BASE,"UPDATE t SET b=8 WHERE rowid=1;"+OBSERVE),
 'update_duplicate':(BASE,"UPDATE t SET b=1 WHERE rowid=2;"),
 'update_ignore':(BASE,"UPDATE OR IGNORE t SET b=1 WHERE rowid=2;"+OBSERVE),
 'update_replace':(BASE,"UPDATE OR REPLACE t SET b=1 WHERE rowid=2;"+OBSERVE),
 'delete':(BASE,'DELETE FROM t WHERE rowid=1;'+OBSERVE),
 'rowid':(BASE,'UPDATE t SET rowid=30 WHERE rowid=1;'+OBSERVE),
 'rollback':(BASE,"BEGIN;UPDATE t SET v='changed';ROLLBACK;"+OBSERVE),
 'drop':(BASE,'DROP TABLE t;SELECT count(*) FROM sqlite_schema;'),
 'drop_automatic':(BASE,'DROP INDEX sqlite_autoindex_t_1;'),
 'catalog_null':(BASE,"SELECT type,name,tbl_name,sql IS NULL FROM sqlite_schema ORDER BY type,name;"),
 'reversed':(TABLE.replace('KEY(a,b)','KEY(b,a)')+ROWS,OBSERVE),
 'integer_components':(TABLE.replace('a TEXT','a INTEGER'),"INSERT INTO t VALUES(1,1,'one'),(1,2,'two');"+OBSERVE),
 'unique_table':(TABLE.replace('PRIMARY KEY','UNIQUE')+ROWS,"INSERT INTO t VALUES('A',1,'duplicate');"),
 'unique_table_open':(TABLE.replace('PRIMARY KEY','UNIQUE')+ROWS,OBSERVE),
 'mixed_ordinary':(TABLE.replace('KEY(a,b)','KEY(a,b),UNIQUE(v)')+ROWS,'INSERT INTO t VALUES(\'c\',4,\'four\');'+OBSERVE),
 'unknown_column':('',TABLE.replace('KEY(a,b)','KEY(a,missing)')),
 'multiple_primary':('',TABLE.replace('KEY(a,b)','KEY(a,b),PRIMARY KEY(v)')),
}
rng=random.Random(int(os.environ.get('SQLEANITE_COMPOSITE_TABLE_SEED','1846001')))
for i in range(12):
 amount=rng.randrange(10,900)
 Q[f'fresh_{i}']=(BASE,f'UPDATE t SET b={amount} WHERE rowid={i%5+1};'+OBSERVE)
for name,(setup,sql) in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(CompositeTableKeys,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
