#!/usr/bin/env python3
"""UPSERT regression cases on the production rollback and WAL paths."""
import os,random,unittest
from test_pragma_tables import case
SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'a',3),(2,'b',7),(3,'c',2);"
QUERIES={
 'insert':"INSERT INTO t VALUES(4,'d',9) ON CONFLICT(id) DO UPDATE SET n=excluded.n;SELECT * FROM t ORDER BY id;",
 'update':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=excluded.n;SELECT * FROM t ORDER BY id;",
 'nothing':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO NOTHING;SELECT * FROM t ORDER BY id;",
 'nothing_all':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT DO NOTHING;SELECT changes();",
 'update_all':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT DO UPDATE SET n=excluded.n;SELECT * FROM t ORDER BY id;",
 'existing':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=t.n+excluded.n,v=t.v||excluded.v;SELECT * FROM t ORDER BY id;",
 'alias':"INSERT INTO t AS a VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=a.n+excluded.n;SELECT * FROM t ORDER BY id;",
 'where_true':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=excluded.n WHERE t.n<excluded.n;SELECT * FROM t ORDER BY id;",
 'where_false':"INSERT INTO t VALUES(1,'d',1) ON CONFLICT(id) DO UPDATE SET n=excluded.n WHERE t.n<excluded.n;SELECT changes();SELECT * FROM t ORDER BY id;",
 'multi':"INSERT INTO t VALUES(1,'d',9),(4,'e',8),(1,'f',10) ON CONFLICT(id) DO UPDATE SET n=t.n+excluded.n;SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM t ORDER BY id;",
 'returning':"INSERT INTO t VALUES(1,'d',9),(4,'e',8) ON CONFLICT(id) DO UPDATE SET n=excluded.n RETURNING id,n;",
 'returning_nothing':"INSERT INTO t VALUES(1,'d',9),(4,'e',8) ON CONFLICT DO NOTHING RETURNING id,n;",
 'key_update':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET id=10,n=excluded.n;SELECT last_insert_rowid();SELECT * FROM t ORDER BY id;",
 'update_abort':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET id=2;",
 'ignore_priority':"INSERT OR IGNORE INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=excluded.n;SELECT * FROM t ORDER BY id;",
 'replace_priority':"INSERT OR REPLACE INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=excluded.n;SELECT * FROM t ORDER BY id;",
 'invalid_target':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT(n) DO NOTHING;",
 'missing_target_column':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT(missing) DO NOTHING;",
 'invalid_assignment':"INSERT INTO t VALUES(4,'d',9) ON CONFLICT(id) DO UPDATE SET missing=excluded.n;",
 'missing_excluded':"INSERT INTO t VALUES(4,'d',9) ON CONFLICT(id) DO UPDATE SET n=excluded.missing;",
 'returning_excluded':"INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=excluded.n RETURNING excluded.n;",
 'counters':"INSERT INTO t VALUES(1,'d',9),(4,'e',8) ON CONFLICT(id) DO UPDATE SET n=changes()+total_changes() RETURNING id,n,last_insert_rowid();SELECT changes(),total_changes(),last_insert_rowid();",
 'rollback':"BEGIN;INSERT INTO t VALUES(1,'d',9),(4,'e',8) ON CONFLICT(id) DO UPDATE SET n=excluded.n;ROLLBACK;SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM t ORDER BY id;",
}
QUERIES.update({
 'select_constant': "INSERT INTO t SELECT 1,'d',9 ON CONFLICT(id) DO UPDATE SET n=excluded.n RETURNING *;",
 'select_same': "INSERT INTO t SELECT id,v,n+1 FROM t WHERE 1 ON CONFLICT(id) DO UPDATE SET n=excluded.n;SELECT * FROM t ORDER BY id;",
 'select_empty': "INSERT INTO t SELECT 4,'d',9 WHERE 0 ON CONFLICT(id) DO UPDATE SET n=excluded.n;SELECT changes();",
 'select_union': "INSERT INTO t SELECT 1,'d',9 UNION ALL SELECT 4,'e',2 ON CONFLICT(id) DO UPDATE SET n=excluded.n RETURNING *;",
 'select_filtered': "INSERT INTO t SELECT id+3,v,n FROM t WHERE n>2 ON CONFLICT DO NOTHING;SELECT * FROM t ORDER BY id;",
 'select_autoincrement': "CREATE TABLE a(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO a SELECT id,v FROM t WHERE 1 ON CONFLICT(id) DO UPDATE SET v=excluded.v;SELECT * FROM a;SELECT * FROM sqlite_sequence;",

 'rowid_target': "INSERT INTO t VALUES(1,'d',9) ON CONFLICT(rowid) DO UPDATE SET n=excluded.n;SELECT * FROM t ORDER BY id;",
 'target_nocase': "INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id COLLATE nocase) DO NOTHING;",
 'target_binary': "INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id COLLATE binary DESC) DO NOTHING;",
 'target_predicate': "INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) WHERE n<0 DO UPDATE SET n=excluded.n;SELECT * FROM t ORDER BY id;",
 'target_predicate_missing': "INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) WHERE missing DO NOTHING;",
 'repeated_assignments': "INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=excluded.n,n=t.n+1;SELECT * FROM t ORDER BY id;",
 'tuple_assignment': "INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET (v,n)=(excluded.v,excluded.n);SELECT * FROM t ORDER BY id;",
 'nothing_missing_return': "INSERT INTO t VALUES(1,'d',9) ON CONFLICT DO NOTHING RETURNING missing;",
 'false_update_missing': "INSERT INTO t VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=missing WHERE 0;",
 'update_affinity': "INSERT INTO t VALUES(1,7,'99') ON CONFLICT(id) DO UPDATE SET v=typeof(excluded.v),n=excluded.n='99' RETURNING *;",
 'insert_default': "INSERT INTO t(id,n) VALUES(1,99),(4,33) ON CONFLICT(id) DO UPDATE SET v=excluded.v,n=excluded.n RETURNING *;",
 'excluded_alias': "INSERT INTO t AS excluded VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=excluded.n;SELECT * FROM t ORDER BY id;",
 'returning_alias': "INSERT INTO t AS a VALUES(1,'d',9) ON CONFLICT(id) DO UPDATE SET n=a.n RETURNING a.n;",
 'multiple_clauses': "INSERT INTO t VALUES(1,'d',9),(4,'e',2) ON CONFLICT(id) DO NOTHING ON CONFLICT DO UPDATE SET n=99;SELECT * FROM t ORDER BY id;",
 'abort_prior_insert': "INSERT INTO t VALUES(4,'d',9),(1,'e',2) ON CONFLICT(id) DO UPDATE SET id=2;",
 'lastid_dynamic': "INSERT INTO t VALUES(4,'d',last_insert_rowid()),(1,'e',last_insert_rowid()) ON CONFLICT(id) DO UPDATE SET n=excluded.n+last_insert_rowid();SELECT * FROM t ORDER BY id;",
 'lastid_materialized': "INSERT INTO t VALUES(4,'d',last_insert_rowid()),(1,'e',last_insert_rowid()) ON CONFLICT(id) DO UPDATE SET n=excluded.n+last_insert_rowid() RETURNING id,n,last_insert_rowid();",
})
rng=random.Random(int(os.environ.get('SQLEANITE_UPSERT_SEED','358200')))
for i in range(12):
 rows=','.join(f"({rng.randrange(1,6)},'v',{rng.randrange(-100,100)})" for _ in range(6))
 QUERIES['generated_'+str(i)]='INSERT INTO t VALUES'+rows+' ON CONFLICT(id) DO UPDATE SET n=t.n+excluded.n;SELECT changes(),last_insert_rowid();SELECT * FROM t ORDER BY id;'
class Upsert(unittest.TestCase):pass
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(Upsert,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
FIXTURES={
 'autoincrement':("CREATE TABLE a(id INTEGER PRIMARY KEY AUTOINCREMENT,v TEXT);INSERT INTO a VALUES(1,'a');",{
  'update':"INSERT INTO a VALUES(1,'b'),(NULL,'c') ON CONFLICT(id) DO UPDATE SET v=excluded.v RETURNING *;SELECT * FROM sqlite_sequence;SELECT last_insert_rowid(),changes();",
  'skip':"INSERT INTO a VALUES(1,'b'),(NULL,'c') ON CONFLICT DO NOTHING;SELECT * FROM a;SELECT * FROM sqlite_sequence;",
  'high_update':"INSERT INTO a VALUES(1,'b') ON CONFLICT(id) DO UPDATE SET id=100;INSERT INTO a(v) VALUES('c');SELECT * FROM a;SELECT * FROM sqlite_sequence;",
 }),
 'nullable_key':("CREATE TABLE a(k TEXT PRIMARY KEY,v INTEGER);INSERT INTO a VALUES('a',1);",{
  'update':"INSERT INTO a VALUES('a',3) ON CONFLICT(k) DO UPDATE SET v=a.v+excluded.v;SELECT rowid,* FROM a;",
  'nulls':"INSERT INTO a VALUES(NULL,2),(NULL,3) ON CONFLICT(k) DO NOTHING;SELECT rowid,* FROM a ORDER BY rowid;",
  'affinity':"INSERT INTO a VALUES('a','42') ON CONFLICT(k) DO UPDATE SET v=typeof(excluded.v) RETURNING *;",
 }),
 'not_null':("CREATE TABLE a(id INTEGER PRIMARY KEY,v TEXT NOT NULL DEFAULT 'd');INSERT INTO a VALUES(1,'a');",{
  'abort':"INSERT INTO a VALUES(1,NULL) ON CONFLICT(id) DO UPDATE SET v='x';",
  'ignore':"INSERT OR IGNORE INTO a VALUES(1,NULL) ON CONFLICT(id) DO UPDATE SET v='x';SELECT * FROM a;SELECT changes();",
  'replace':"INSERT OR REPLACE INTO a VALUES(1,NULL) ON CONFLICT(id) DO UPDATE SET v=excluded.v;SELECT * FROM a;",
  'update_abort':"INSERT OR IGNORE INTO a VALUES(1,'b') ON CONFLICT(id) DO UPDATE SET v=NULL;",
 }),
}
for fixture,(setup,queries) in FIXTURES.items():
 for name,sql in queries.items():
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(Upsert,'test_'+fixture+'_'+name+'_'+suffix,case(sql,mode,setup))
for typ in ['TEXT','INTEGER','NUMERIC','REAL','BLOB']:
 for val in ['7',"'7'",'7.5']:
  setup=f"CREATE TABLE a(id INTEGER PRIMARY KEY,v {typ},n);INSERT INTO a VALUES(1,0,0);"
  sql=f"INSERT INTO a VALUES(1,{val},0) ON CONFLICT(id) DO UPDATE SET n=typeof(excluded.v)||':'||quote(excluded.v);SELECT n FROM a;"
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(Upsert,'test_excluded_'+typ+'_'+str(['7',"'7'",'7.5'].index(val))+'_'+suffix,case(sql,mode,setup))
# Explicit index conflicts also retain the complete on-disk catalog on both paths.
INDEX_SETUP="CREATE TABLE a(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);CREATE UNIQUE INDEX uv ON a(v);CREATE UNIQUE INDEX un ON a(n);INSERT INTO a VALUES(1,'a',10),(2,'b',20);"
INDEX_QUERIES={
 'update':"INSERT INTO a VALUES(9,'a',30) ON CONFLICT(v) DO UPDATE SET n=excluded.n RETURNING *;",
 'nothing':"INSERT INTO a VALUES(9,'a',30) ON CONFLICT(v) DO NOTHING;SELECT * FROM a;",
 'targetless':"INSERT INTO a VALUES(9,'a',30) ON CONFLICT DO UPDATE SET n=excluded.n RETURNING *;",
 'rowid_priority':"INSERT INTO a VALUES(1,'b',30) ON CONFLICT(id) DO UPDATE SET n=excluded.n ON CONFLICT(v) DO NOTHING RETURNING *;",
 'index_priority':"INSERT INTO a VALUES(1,'b',30) ON CONFLICT(v) DO UPDATE SET n=excluded.n ON CONFLICT(id) DO NOTHING RETURNING *;",
 'index_order':"INSERT INTO a VALUES(9,'a',20) ON CONFLICT DO UPDATE SET n=excluded.n+1 RETURNING *;",
 'clause_order':"INSERT INTO a VALUES(9,'a',20) ON CONFLICT(v) DO UPDATE SET n=excluded.n+1 ON CONFLICT(n) DO NOTHING RETURNING *;",
 'abort_update':"INSERT INTO a VALUES(9,'a',20) ON CONFLICT(v) DO UPDATE SET n=excluded.n;",
 'binary':"INSERT INTO a VALUES(9,'a',30) ON CONFLICT(v COLLATE binary) DO NOTHING;SELECT * FROM a;",
 'nocase':"INSERT INTO a VALUES(9,'a',30) ON CONFLICT(v COLLATE nocase) DO NOTHING;",
 'affinity':"INSERT INTO a VALUES(9,'a','30') ON CONFLICT(v) DO UPDATE SET v=typeof(excluded.n),n=excluded.n RETURNING *;",
 'nulls':"INSERT INTO a VALUES(3,NULL,30),(4,NULL,40) ON CONFLICT(v) DO NOTHING;SELECT * FROM a ORDER BY id;",
}
for name,sql in INDEX_QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(Upsert,'test_index_'+name+'_'+suffix,case(sql,mode,INDEX_SETUP))
if __name__=='__main__':unittest.main()
