#!/usr/bin/env python3
"""Real UTF-16 database/WAL read regressions, including encoding-dependent SQL.
Each read compares outputs/errors and confirms persisted catalog/rows/integrity.
"""
import os,random,unittest
from test_check_add_column import case
class UTF16Reads(unittest.TestCase):pass
DATA="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'Árvíztűrő',2),(2,'你好',4),(3,'😀𝄞',6),(4,'ASCII',8),(5,'',10),(6,NULL,12);"
READS={
 'computed_bytes': "SELECT id,hex(upper(v)),octet_length(upper(v)),hex(substr(v,1,2)),octet_length(substr(v,1,2)),hex(v||'') FROM t ORDER BY id;",
 'branch_bytes': "SELECT id,hex(CASE WHEN id=1 THEN upper(v) ELSE v END),octet_length(coalesce(v,upper('é'))) FROM t ORDER BY id;",
 'cast_types': "SELECT typeof(CAST(42 AS TEXT)),hex(CAST(42 AS TEXT)),hex(CAST(CAST(X'41' AS TEXT) AS BLOB));",
 'plain':'SELECT * FROM t ORDER BY id;',
 'length':'SELECT id,length(v),unicode(v),typeof(v) FROM t ORDER BY id;',
 'encoding_bytes':"SELECT id,hex(v),hex(CAST(v AS BLOB)),octet_length(v) FROM t ORDER BY id;",
 'literal_bytes':"SELECT hex('Á😀'),hex(CAST('Á😀' AS BLOB)),octet_length('Á😀'),hex(42),octet_length(42);",
 'casts':"SELECT hex(CAST(X'41000000E900' AS TEXT)),length(CAST(X'41000000E900' AS TEXT)),hex(CAST(X'41' AS TEXT));",
 'functions':"SELECT id,upper(v),lower(v),substr(v,2,2),quote(v),v||'é' FROM t ORDER BY id;",
 'filter':"SELECT id FROM t WHERE v='你好' OR v LIKE 'ASCII%' ORDER BY id;",
 'sort':'SELECT id,v FROM t ORDER BY v,id;',
 'group':'SELECT length(v),count(*) FROM t GROUP BY length(v) ORDER BY length(v);',
 'scalar':'SELECT a.id,(SELECT b.v FROM t b WHERE b.id=a.id) FROM t a ORDER BY a.id;',
 'derived':'SELECT id,hex(v),octet_length(v) FROM (SELECT id,v FROM t) d ORDER BY id;',
 'cte':'WITH c AS (SELECT id,v FROM t) SELECT id,hex(v) FROM c ORDER BY id;',
 'join':'SELECT a.id,a.v,b.n FROM t a JOIN t b ON a.id=b.id ORDER BY a.id;',
 'pragma':'PRAGMA encoding;PRAGMA table_info(t);',
 'catalog':'SELECT type,name,tbl_name,sql FROM sqlite_schema ORDER BY rowid;',
 'index':"SELECT id,v FROM t WHERE v>='ASCII' ORDER BY v,id;",
}
for enc in ['UTF-16le','UTF-16be']:
 setup=f"PRAGMA encoding='{enc}';"+DATA+'CREATE INDEX lookup ON t(v);'
 for name,sql in READS.items():
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(UTF16Reads,'test_'+enc.replace('-','_')+'_'+name+'_'+suffix,case(sql,mode,setup))
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(UTF16Reads,'test_'+enc.replace('-','_')+'_declared_'+suffix,case("SELECT count(*) FROM c WHERE v='A';SELECT hex(v COLLATE NOCASE) FROM c ORDER BY rowid;",mode,f"PRAGMA encoding='{enc}';CREATE TABLE c(v TEXT COLLATE NOCASE);INSERT INTO c VALUES('a'),('A');"))
 for page_size in [512,1024,8192,65536]:
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(UTF16Reads,f'test_{enc.replace("-","_")}_page_{page_size}_{suffix}',case('SELECT * FROM t ORDER BY id;',mode,f"PRAGMA page_size={page_size};"+setup))
 for label,extra,sql in [
  ('view','CREATE VIEW q AS SELECT id,v,n FROM t;','SELECT * FROM q ORDER BY id;'),
  ('view_bytes','CREATE VIEW q AS SELECT id,v FROM t;','SELECT id,hex(v),octet_length(v) FROM q ORDER BY id;'),
  ('overflow',"INSERT INTO t VALUES(7,replace(hex(zeroblob(6000)),'00','é😀'),14);",'SELECT id,length(v),octet_length(v) FROM t ORDER BY id;'),
  ('schema_overflow','CREATE TABLE "'+('Á'*2200)+'"(x);',"SELECT length(name) FROM sqlite_schema WHERE type='table' ORDER BY rowid;"),
 ]:
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(UTF16Reads,f'test_{enc.replace("-","_")}_{label}_{suffix}',case(sql,mode,setup+extra))
 rng=random.Random(int(os.environ.get('SQLEANITE_UTF16_SEED','373401')))
 for i in range(6):
  values=[''.join(rng.choice('aAéŐ中😀𝄞') for _ in range(rng.randrange(0,10))) for _ in range(5)]
  extra=''.join(f"INSERT INTO t VALUES({j+7},'{v}',{j});" for j,v in enumerate(values))
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(UTF16Reads,f'test_{enc.replace("-","_")}_fresh_{i}_{suffix}',case('SELECT id,v,length(v),hex(v),octet_length(v) FROM t ORDER BY id;',mode,setup+extra))
class UTF16CommittedWAL(unittest.TestCase):
 """Keep the pinned SQLite writer open so new schema/data remain in the WAL."""
 pass

def live_wal_case(encoding,query):
 def test(self):
  import subprocess,tempfile,time
  from pathlib import Path
  from test_check_add_column import observe,SQLITE,BINARY
  with tempfile.TemporaryDirectory(prefix='sqleanite-utf16-wal-') as folder:
   path=Path(folder)/'data.db';ready=Path(folder)/'ready'
   writer=subprocess.Popen([SQLITE,str(path)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
   try:
    script=f"PRAGMA encoding='{encoding}';CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);PRAGMA journal_mode=WAL;INSERT INTO t VALUES(1,'ő😀'),(2,'你好');CREATE VIEW q AS SELECT * FROM t;\n.output {ready}\n.print ready\n.output stdout\n"
    writer.stdin.write(script);writer.stdin.flush();deadline=time.monotonic()+10
    while not (ready.exists() and ready.read_bytes()==b'ready\n'):
     if writer.poll() is not None:raise AssertionError(writer.stderr.read())
     if time.monotonic()>deadline:raise AssertionError('pinned SQLite writer did not publish its WAL')
     time.sleep(.01)
    self.assertGreater(Path(str(path)+'-wal').stat().st_size,32)
    before=observe(path)
    lean=subprocess.run([str(BINARY),'--verified-wal-file',str(path)],input=query,text=True,capture_output=True,timeout=30)
    ref=subprocess.run([SQLITE,'-batch','-bail',str(path)],input=query,text=True,capture_output=True,timeout=30)
    self.assertEqual(lean.returncode,ref.returncode,lean.stderr+' / '+ref.stderr)
    self.assertEqual(lean.stdout,ref.stdout,lean.stderr)
    self.assertEqual(observe(path),before)
   finally:
    if writer.poll() is None:
     writer.communicate('.quit\n',timeout=10)
 return test
for enc in ['UTF-16le','UTF-16be']:
 for name,query in [
   ('table','SELECT * FROM t ORDER BY id;'),
   ('bytes','SELECT id,hex(v),octet_length(v) FROM t ORDER BY id;PRAGMA encoding;'),
   ('view','SELECT * FROM q ORDER BY id;SELECT type,name,sql FROM sqlite_schema ORDER BY name;')]:
  setattr(UTF16CommittedWAL,'test_'+enc.replace('-','_')+'_'+name,live_wal_case(enc,query))

if __name__=='__main__':unittest.main()
