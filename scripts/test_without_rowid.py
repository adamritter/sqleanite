#!/usr/bin/env python3
"""WITHOUT ROWID SQL and independent complete typed table snapshots."""
import json,os,random,re,subprocess,tempfile,unittest
from pathlib import Path
from test_pragma_tables import BINARY,SQLITE
from test_check_add_column import statement_lines
class WithoutRowid(unittest.TestCase):pass

def quote(name):return '"'+name.replace('"','""')+'"'
def snapshot(path):
 def query(sql):
  p=subprocess.run([SQLITE,str(path),sql],text=True,capture_output=True,timeout=30)
  return p.returncode,p.stdout,p.stderr
 catalog=query('SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;')
 names=query("SELECT json_quote(name) FROM sqlite_schema WHERE type='table' ORDER BY name;")
 tables=[]
 for line in names[1].splitlines():
  name=json.loads(line);table=quote(name)
  columns=[json.loads(line) for line in query('SELECT json_quote(name) FROM pragma_table_xinfo('+"'"+name.replace("'","''")+"'"+') WHERE hidden<>1 ORDER BY cid;')[1].splitlines()]
  fields=','.join('typeof('+quote(c)+'),quote('+quote(c)+'),hex('+quote(c)+')' for c in columns)
  order=','.join(quote(c) for c in columns)
  tables.append((name,query('PRAGMA table_xinfo('+table+');'),query('SELECT '+fields+' FROM '+table+' ORDER BY '+order+';')))
 return catalog,names,query('PRAGMA integrity_check;'),tables

def case(setup,sql,mode):
 def test(self):
  with tempfile.TemporaryDirectory(prefix='sqleanite-without-rowid-') as directory:
   left=Path(directory)/'lean.db';right=Path(directory)/'sqlite.db'
   for path in (left,right):subprocess.run([SQLITE,str(path)],input=setup,text=True,capture_output=True,check=True)
   lean=subprocess.run([str(BINARY),mode,str(left)],input=statement_lines(sql),text=True,capture_output=True,timeout=30)
   native=subprocess.run([SQLITE,'-batch','-bail',str(right)],input=statement_lines(sql),text=True,capture_output=True,timeout=30)
   self.assertEqual(lean.returncode,native.returncode,lean.stderr+' / '+native.stderr)
   self.assertEqual(lean.stdout,native.stdout,lean.stderr)
   if native.returncode:
    def error(p):return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?','',p.stderr.splitlines()[0])
    self.assertEqual(error(lean),error(native))
   self.assertEqual(snapshot(left),snapshot(right))
 return test
TABLE='CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n) WITHOUT ROWID;'
ROWS="INSERT INTO t VALUES(5,'five',5),(1,'one',1),(3,'three',3);"
BASE=TABLE+ROWS
OBSERVE="SELECT * FROM t ORDER BY id;PRAGMA table_info(t);PRAGMA table_list(t);PRAGMA index_list(t);PRAGMA index_xinfo('sqlite_autoindex_t_1');"
Q={
 'create':('',BASE+OBSERVE),
 'open':(BASE,OBSERVE),
 'insert':(BASE,"INSERT INTO t VALUES(2,'two',2);"+OBSERVE),
 'update':(BASE,"UPDATE t SET id=8,v='changed' WHERE id=1;"+OBSERVE),
 'delete':(BASE,'DELETE FROM t WHERE id=1;'+OBSERVE),
 'duplicate':(BASE,"INSERT INTO t VALUES(1,'duplicate',9);"),
 'ignore':(BASE,"INSERT OR IGNORE INTO t VALUES(1,'duplicate',9);"+OBSERVE),
 'replace':(BASE,"INSERT OR REPLACE INTO t VALUES(1,'replaced',9);"+OBSERVE),
 'null_key':(BASE,"INSERT INTO t VALUES(NULL,'bad',9);"),
 'missing_key':(BASE,"INSERT INTO t(v,n) VALUES('bad',9);"),
 'rowid_error':(BASE,'SELECT rowid FROM t;'),
 'oid_error':(BASE,'SELECT oid FROM t;'),
 'rowid_update_error':(BASE,'UPDATE t SET rowid=9;'),
 'scan_order':(BASE,'SELECT * FROM t;'),
 'text_integer_key':(BASE,"INSERT INTO t VALUES('text','text',9);"+OBSERVE),
 'last_id':(BASE,"CREATE TABLE ordinary(id INTEGER PRIMARY KEY);INSERT INTO ordinary VALUES(42);INSERT INTO t VALUES(2,'two',2);SELECT last_insert_rowid(),changes();"+OBSERVE),
 'rollback':(BASE,"BEGIN;UPDATE t SET v='changed';ROLLBACK;"+OBSERVE),
 'drop':(BASE,'DROP TABLE t;SELECT count(*) FROM sqlite_schema;'),
 'text_primary':("CREATE TABLE t(id TEXT PRIMARY KEY,v,n) WITHOUT ROWID;INSERT INTO t VALUES('b','bee',2),('a','aye',1);",OBSERVE),
 'composite_primary':("CREATE TABLE t(id TEXT,v TEXT,n,PRIMARY KEY(id,v)) WITHOUT ROWID;INSERT INTO t VALUES('A','one',1),('A','two',2),('B','one',3);",OBSERVE),
 'secondary':(BASE+'CREATE INDEX by_v ON t(v);',"SELECT v FROM t ORDER BY v;PRAGMA index_xinfo(by_v);"+OBSERVE),
 'unique_secondary':(BASE+'CREATE UNIQUE INDEX by_v ON t(v);',"INSERT OR REPLACE INTO t VALUES(9,'one',9);"+OBSERVE),
 'ordinary_rowid_name':("CREATE TABLE t(rowid TEXT PRIMARY KEY,v) WITHOUT ROWID;INSERT INTO t VALUES('a','aye');",'SELECT rowid,v FROM t;'),
 'virtual':(BASE,"SELECT * FROM pragma_table_info('t');SELECT * FROM pragma_index_list('t');SELECT * FROM pragma_index_xinfo('sqlite_autoindex_t_1');"),
}
Q.update({
 'create_empty':('',TABLE+'SELECT * FROM t;'),
 'create_if_exists':(BASE,'CREATE TABLE IF NOT EXISTS t(id INTEGER PRIMARY KEY) WITHOUT ROWID;'+OBSERVE),
 'table_primary_info':(BASE,'PRAGMA index_info(t);PRAGMA index_xinfo(t);'),
 'no_primary':('','CREATE TABLE t(a,b) WITHOUT ROWID;'),
 'autoincrement':('','CREATE TABLE t(a INTEGER PRIMARY KEY AUTOINCREMENT,b) WITHOUT ROWID;'),
 'key_not_first':("CREATE TABLE t(v TEXT,id TEXT,n,PRIMARY KEY(id,v)) WITHOUT ROWID;INSERT INTO t VALUES('b','a',1),('a','b',2),('a','a',3);",'UPDATE t SET n=n+1;SELECT * FROM t;PRAGMA index_xinfo(t);'),
 'declared_collations':("CREATE TABLE t(id TEXT COLLATE NOCASE PRIMARY KEY,v TEXT COLLATE RTRIM,n) WITHOUT ROWID;INSERT INTO t VALUES('A','a',1),('b','b',2);",'PRAGMA index_xinfo(t);UPDATE t SET n=n+1;'+OBSERVE),
 'composite_secondary':("CREATE TABLE t(id TEXT,v TEXT,n,PRIMARY KEY(id,v)) WITHOUT ROWID;INSERT INTO t VALUES('a','a',1),('a','b',2),('b','a',3);CREATE INDEX by_n ON t(n);","UPDATE t SET n=n+10 WHERE id='a';PRAGMA index_xinfo(by_n);"+OBSERVE),
 'secondary_shared_primary':(BASE+'CREATE INDEX by_id ON t(v,id);','PRAGMA index_xinfo(by_id);UPDATE t SET n=n+1;'+OBSERVE),
 'expression_secondary':(BASE+'CREATE INDEX expr ON t(lower(v),n+1);','UPDATE t SET v=upper(v);PRAGMA index_xinfo(expr);'+OBSERVE),
 'partial_secondary':(BASE+'CREATE INDEX part ON t(v) WHERE n>2;','UPDATE t SET n=10-n;PRAGMA index_xinfo(part);'+OBSERVE),
 'unique_constraint':(BASE.replace('n) WITHOUT','n UNIQUE) WITHOUT'),"INSERT OR REPLACE INTO t VALUES(9,'nine',1);"+OBSERVE),
 'real_aliases':("CREATE TABLE t(rowid TEXT PRIMARY KEY,oid TEXT,_rowid_ TEXT) WITHOUT ROWID;INSERT INTO t VALUES('a','b','c');","SELECT rowid,oid,_rowid_ FROM t;UPDATE t SET rowid='d';SELECT * FROM t;"),
 'rowid_dead':(BASE,'SELECT rowid FROM t WHERE 0;'),
 'rowid_join':(BASE+'CREATE TABLE other(x);INSERT INTO other VALUES(1);','SELECT t.rowid FROM t,other;'),
 'strict':('',"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n ANY) WITHOUT ROWID,STRICT;INSERT INTO t VALUES(1,2,'0003');"+OBSERVE),
})
rng=random.Random(int(os.environ.get('SQLEANITE_WITHOUT_ROWID_SEED','1849001')))
for i in range(12):
 value=rng.randrange(20,900)
 Q[f'fresh_{i}']=(BASE,f'UPDATE t SET n={value} WHERE id={[1,3,5][i%3]};'+OBSERVE)
for name,(setup,sql) in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(WithoutRowid,'test_'+name+'_'+suffix,case(setup,sql,mode))
if __name__=='__main__':unittest.main()
