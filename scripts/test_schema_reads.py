#!/usr/bin/env python3
"""Read actual sqlite_schema records and root/rowid metadata through SQL."""
import os,random,unittest
from test_pragma_tables import case
SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,'a'),(2,'b');CREATE INDEX gone ON t(v);CREATE INDEX kept ON t(v);DROP INDEX gone;CREATE VIEW v AS SELECT * FROM t;CREATE TRIGGER tr AFTER INSERT ON t BEGIN SELECT 1;END;"
QUERIES={
 'all':'SELECT * FROM sqlite_schema ORDER BY rowid;',
 'rowid':'SELECT rowid,type,name,rootpage,sql FROM sqlite_schema ORDER BY rowid;',
 'master':'SELECT rowid,* FROM sqlite_master ORDER BY rowid;',
 'main':'SELECT name,rootpage FROM main.sqlite_schema ORDER BY name;',
 'alias':'SELECT s.name,s.sql FROM sqlite_schema s WHERE s.type=\'index\' ORDER BY s.rowid;',
 'aggregate':'SELECT type,count(*) FROM sqlite_schema GROUP BY type ORDER BY type;',
 'roots':'SELECT name,rootpage,typeof(rootpage) FROM sqlite_schema WHERE rootpage>0 ORDER BY rootpage;',
 'join':'SELECT s.name,t.id FROM sqlite_schema s JOIN t ON s.name=\'t\' ORDER BY t.id;',
 'self_join':'SELECT s.name,m.name FROM sqlite_schema s JOIN sqlite_master m ON s.rowid=m.rowid ORDER BY s.rowid;',
 'window':'SELECT name,row_number() OVER(ORDER BY rowid) FROM sqlite_schema ORDER BY rowid;',
 'scalar':'SELECT name,(SELECT count(*) FROM t) FROM sqlite_schema ORDER BY rowid;',
 'limit':'SELECT name FROM sqlite_schema ORDER BY name LIMIT 2 OFFSET 1;',
 'union':'SELECT name FROM sqlite_schema UNION SELECT name FROM sqlite_master ORDER BY 1;',
 'counters':'SELECT changes(),total_changes(),last_insert_rowid();SELECT count(*) FROM sqlite_schema;SELECT changes(),total_changes(),last_insert_rowid();',
 'transaction':'BEGIN;SELECT name FROM sqlite_schema ORDER BY rowid;ROLLBACK;',
}
class SchemaReads(unittest.TestCase):pass
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(SchemaReads,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
rng=random.Random(int(os.environ.get('SQLEANITE_SCHEMA_READ_SEED','358650')))
for i in range(12):
 name='fresh_'+str(rng.randrange(1000000));setup=f'CREATE TABLE "{name}"(x INTEGER PRIMARY KEY,v TEXT);CREATE INDEX "index {name}" ON "{name}"(v);'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(SchemaReads,'test_generated_'+str(i)+'_'+suffix,case('SELECT rowid,* FROM sqlite_schema ORDER BY rowid;',mode,setup))
if __name__=='__main__':unittest.main()
