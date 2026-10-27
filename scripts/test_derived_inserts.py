#!/usr/bin/env python3
"""Derived SELECT inputs must use ordinary INSERT behavior and retain only user tables."""
import os,random,unittest
from test_pragma_tables import case
class DerivedInserts(unittest.TestCase):pass
SETUP='CREATE TABLE src(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO src VALUES(1,\'a\'),(2,\'b\'),(3,\'c\');CREATE TABLE dst(id INTEGER PRIMARY KEY,v TEXT);'
QUERIES={
 'values':"INSERT INTO dst SELECT * FROM (VALUES(5,'x'),(6,'y'));SELECT * FROM dst;",
 'table':'INSERT INTO dst SELECT * FROM (SELECT * FROM src);SELECT * FROM dst;',
 'nested':'INSERT INTO dst SELECT * FROM (SELECT * FROM (SELECT * FROM src));SELECT * FROM dst;',
 'filter':'INSERT INTO dst SELECT id,v FROM (SELECT * FROM src) WHERE id>1 ORDER BY id DESC;SELECT * FROM dst;',
 'self':'INSERT INTO src SELECT id+10,v FROM (SELECT * FROM src);SELECT * FROM src ORDER BY id;',
 'returning':'INSERT INTO dst SELECT * FROM (SELECT * FROM src) RETURNING id,v;SELECT * FROM dst;',
 'ignore':"INSERT INTO dst VALUES(1,'old');INSERT OR IGNORE INTO dst SELECT * FROM (SELECT * FROM src);SELECT * FROM dst;",
 'replace':"INSERT INTO dst VALUES(1,'old');INSERT OR REPLACE INTO dst SELECT * FROM (SELECT * FROM src);SELECT * FROM dst;",
 'counters':'INSERT INTO dst SELECT * FROM (SELECT * FROM src);SELECT changes(),total_changes(),last_insert_rowid();',
 'register_values':"INSERT INTO dst SELECT * FROM (VALUES(8,changes()),(9,total_changes()),(10,last_insert_rowid()));SELECT * FROM dst;",
 'register_returning':"INSERT INTO dst SELECT * FROM (VALUES(8,changes()),(9,total_changes()),(10,last_insert_rowid())) RETURNING id,v;SELECT * FROM dst;",
 'register_ordered':"INSERT INTO dst SELECT * FROM (VALUES(8,changes()),(9,total_changes()),(10,last_insert_rowid())) ORDER BY column1;SELECT * FROM dst;",
 'register_self':"INSERT INTO dst VALUES(1,'old');INSERT INTO dst SELECT * FROM (VALUES(8,last_insert_rowid()),(9,last_insert_rowid()),(10,last_insert_rowid()));SELECT * FROM dst;",
 'union':"INSERT INTO dst SELECT * FROM (SELECT * FROM src UNION ALL SELECT 4,'d');SELECT * FROM dst;",
 'limit':'INSERT INTO dst SELECT * FROM (SELECT * FROM src ORDER BY id DESC LIMIT 2);SELECT * FROM dst;',
 'empty':'INSERT INTO dst SELECT * FROM (SELECT * FROM src WHERE 0);SELECT changes(),total_changes(),last_insert_rowid();',
 'column_list':'INSERT INTO dst(v) SELECT v FROM (SELECT * FROM src);SELECT * FROM dst;',
 'transaction':'BEGIN;INSERT INTO dst SELECT * FROM (SELECT * FROM src);ROLLBACK;SELECT * FROM dst;SELECT changes(),total_changes(),last_insert_rowid();',
 'savepoint':'SAVEPOINT s;INSERT INTO dst SELECT * FROM (SELECT * FROM src);ROLLBACK TO s;RELEASE s;SELECT * FROM dst;',
 'join':'INSERT INTO dst SELECT p.id,q.v FROM (SELECT * FROM src) p JOIN src q ON p.id=q.id;SELECT * FROM dst;',
 'aggregate':'INSERT INTO dst SELECT count(*),max(v) FROM (SELECT * FROM src);SELECT * FROM dst;',
 'window':'INSERT INTO dst SELECT row_number() OVER(ORDER BY id),v FROM (SELECT * FROM src);SELECT * FROM dst;',
 'json':"INSERT INTO dst(v) SELECT value FROM json_each('[1,2,3]');SELECT * FROM dst;",
 'pragma':'INSERT INTO dst(v) SELECT name FROM pragma_table_info(\'src\');SELECT * FROM dst;',
 'width':'INSERT INTO dst SELECT id FROM (SELECT * FROM src);',
 'missing':'INSERT INTO dst SELECT * FROM (SELECT * FROM missing);',
 'default':"CREATE TABLE d(id INTEGER PRIMARY KEY,v TEXT DEFAULT 'default');INSERT INTO d(id) SELECT id FROM (SELECT * FROM src);SELECT * FROM d;",
 'affinity':"CREATE TABLE n(v INTEGER);INSERT INTO n SELECT column1 FROM (VALUES('12'),('3.5'),('abc'),(NULL));SELECT v,typeof(v) FROM n;",
}
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(DerivedInserts,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
rng=random.Random(int(os.environ.get('SQLEANITE_DERIVED_INSERT_SEED','360900')))
for i in range(12):
 keys=rng.sample(range(10,10000),rng.randrange(1,9));rows=','.join(f"({k},'v{k}')" for k in keys)
 sql=f'INSERT INTO dst SELECT * FROM (VALUES{rows}) ORDER BY column1 DESC RETURNING id,v;SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM dst;'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(DerivedInserts,'test_fresh_'+str(i)+'_'+suffix,case(sql,mode,SETUP))
if __name__=='__main__':unittest.main()
