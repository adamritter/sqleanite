#!/usr/bin/env python3
"""A small, explicit compatibility-gap survey, not a global coverage percentage.

Each named feature has one deterministic SQL probe on seeded C-created data.
Both public file modes compare query results and normalized SQL errors plus
complete C-observed catalog text, stored base rows and integrity. All probes,
including failures, are retained. Parser, execution and file failures are not
silently accepted or filtered. A pass covers only that probe, not its feature.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('position',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  try:
   q=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=10);return dict(code=q.returncode,stdout=q.stdout.decode('latin1'),stderr=q.stderr.decode('latin1'))
  except subprocess.TimeoutExpired as expired:
   return dict(code=124,stdout=(expired.stdout or b'').decode('latin1'),stderr=(expired.stderr or b'').decode('latin1'),timed_out=True,timeout_seconds=10)
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 probes=[
 ('cte','WITH c AS (SELECT n FROM t) SELECT sum(n) FROM c;'),
 ('recursive-cte','WITH RECURSIVE c(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM c WHERE x<8) SELECT sum(x) FROM c;'),
 ('scalar-subquery','SELECT id,(SELECT max(n) FROM t) FROM t ORDER BY id;'),
 ('correlated-subquery','SELECT a.id,(SELECT sum(b.n) FROM t b WHERE b.id<=a.id) FROM t a ORDER BY a.id;'),
 ('from-subquery','SELECT sum(n) FROM (SELECT n FROM t WHERE id>1);'),
 ('view','CREATE VIEW visible AS SELECT id,n FROM t;\nSELECT * FROM visible ORDER BY id;'),
 ('trigger','CREATE TRIGGER update_note AFTER UPDATE ON t BEGIN UPDATE t SET v=\'triggered\' WHERE id=new.id; END;\nUPDATE t SET n=n+1 WHERE id=1;\nSELECT v FROM t WHERE id=1;'),
 ('window-row-number','SELECT id,row_number() OVER (ORDER BY n,id) FROM t ORDER BY id;'),
 ('window-aggregate','SELECT id,sum(n) OVER (ORDER BY id ROWS BETWEEN 1 PRECEDING AND CURRENT ROW) FROM t ORDER BY id;'),
 ('strict-table','CREATE TABLE strict_tab(id INTEGER PRIMARY KEY,v TEXT) STRICT;\nINSERT INTO strict_tab VALUES(1,23);\nSELECT typeof(v),v FROM strict_tab;'),
 ('without-rowid','CREATE TABLE no_rowid(id TEXT PRIMARY KEY,v INTEGER) WITHOUT ROWID;\nINSERT INTO no_rowid VALUES(\'a\',2);\nSELECT * FROM no_rowid;'),
 ('composite-primary-key','CREATE TABLE composite(a INTEGER,b INTEGER,PRIMARY KEY(a,b));\nINSERT INTO composite VALUES(1,2);\nSELECT * FROM composite;'),
 ('unique-constraint','CREATE TABLE uq(id INTEGER PRIMARY KEY,v TEXT UNIQUE);\nINSERT INTO uq VALUES(1,\'same\');\nINSERT INTO uq VALUES(2,\'same\');'),
 ('check-constraint','CREATE TABLE ck(v INTEGER CHECK(v>0));\nINSERT INTO ck VALUES(-1);'),
 ('foreign-key','PRAGMA foreign_keys=ON;\nCREATE TABLE fk(id INTEGER PRIMARY KEY,parent INTEGER REFERENCES t(id));\nINSERT INTO fk VALUES(1,999);'),
 ('generated-column','CREATE TABLE gen(a INTEGER,b INTEGER GENERATED ALWAYS AS (a+1) STORED);\nINSERT INTO gen(a) VALUES(3);\nSELECT * FROM gen;'),
 ('declared-nocase','CREATE TABLE coll(v TEXT COLLATE NOCASE);\nINSERT INTO coll VALUES(\'a\'),(\'A\');\nSELECT count(*) FROM coll WHERE v=\'a\';'),
 ('named-index-catalog','CREATE INDEX ix ON t(v);\nSELECT id FROM t ORDER BY v,id;'),
 ('unique-index-catalog','CREATE UNIQUE INDEX ui ON t(n);\nSELECT n FROM t ORDER BY n;'),
 ('partial-index','CREATE INDEX pi ON t(n) WHERE n>0;\nSELECT n FROM t WHERE n>0 ORDER BY n;'),
 ('expression-index','CREATE INDEX ei ON t(lower(v));\nSELECT id FROM t WHERE lower(v)=\'missing\';'),
 ('alter-add','ALTER TABLE t ADD added TEXT DEFAULT \'new\';\nSELECT added FROM t ORDER BY id;'),
 ('alter-add-line-comment','ALTER TABLE t ADD added TEXT -- retained line comment\n;'),
 ('alter-rename-table','ALTER TABLE t RENAME TO renamed;\nSELECT * FROM renamed ORDER BY id;'),
 ('alter-rename-column','ALTER TABLE t RENAME COLUMN n TO renamed;\nSELECT renamed FROM t ORDER BY id;'),
 ('alter-drop-column','ALTER TABLE t DROP COLUMN n;\nSELECT * FROM t ORDER BY id;'),
 ('upsert','INSERT INTO t(id,v,n) VALUES(1,\'changed\',4) ON CONFLICT(id) DO UPDATE SET n=excluded.n;\nSELECT n FROM t WHERE id=1;'),
 ('returning','UPDATE t SET n=n+1 WHERE id=1 RETURNING id,n;'),
 ('json-type',"SELECT json_type('{\"a\":[1]}','$.a');"),
 ('json-array-length',"SELECT json_array_length('[1,2,3]');"),
 ('json-each',"SELECT key,type,value FROM json_each('[1,2,3]') ORDER BY key;"),
 ('json-tree',"SELECT fullkey,type FROM json_tree('{\"a\":[1]}') ORDER BY id;"),
 ('json-insert',"SELECT json_insert('{\"a\":1}','$.b',2);"),
 ('date-function',"SELECT date('2001-02-03','+1 day');"),
 ('strftime',"SELECT strftime('%Y-%m-%d %H:%M:%S','2001-02-03 04:05:06');"),
 ('changes','UPDATE t SET n=n+1 WHERE id<=2;\nSELECT changes();'),
 ('total-changes','UPDATE t SET n=n+1 WHERE id<=2;\nSELECT total_changes();'),
 ('last-insert-rowid',"INSERT INTO t(v,n) VALUES('extra',4);\nSELECT last_insert_rowid();"),
 ('sqlite-version','SELECT sqlite_version();'),
 ('sqlite-source-id','SELECT sqlite_source_id();'),
 ('pragma-table-valued',"SELECT name,type FROM pragma_table_info('t') ORDER BY cid;"),
 ('pragma-user-version','PRAGMA user_version=17;\nPRAGMA user_version;'),
 ('utf16-reading','SELECT id,v,n FROM t ORDER BY id;'),
 ('savepoint-after-read','SELECT count(*) FROM t;\nSAVEPOINT s;\nUPDATE t SET n=n+1;\nROLLBACK TO s;\nRELEASE s;\nSELECT n FROM t ORDER BY id;'),
 ]
 values=[rng.randrange(1,10000) for _ in range(3)];assert len(set(values))==len(values)
 setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);'+''.join("INSERT INTO t VALUES("+str(i+1)+",'value "+str(rng.randrange(1000000))+"',"+str(n)+");" for i,n in enumerate(values))
 # Observe all surviving user tables through C, including an ALTER RENAME target.
 def observe(path):
  schema=csql(path,'PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;')
  names=csql(path,"SELECT hex(name) FROM sqlite_schema WHERE type='table' ORDER BY name;");rows=[]
  if names['code']==0:
   for raw in names['stdout'].splitlines():
    name=bytes.fromhex(raw).decode();quoted='"'+name.replace('"','""')+'"';rows.append(dict(table=name,result=csql(path,'SELECT * FROM '+quoted+' ORDER BY 1;')))
  return dict(schema=schema,names=names,rows=rows)
 cases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-gap-survey-') as tmp:
  folder=Path(tmp)
  for i,(feature,sql) in enumerate(probes):
   base=folder/(str(i)+'-base.db');prefix="PRAGMA encoding='UTF-16le';" if feature=='utf16-reading' else '';made=csql(base,prefix+setup);assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db');shutil.copyfile(base,left);shutil.copyfile(base,right);l,c=run([str(binary),mode,str(left)],sql),csql(right,sql);lo,co=observe(left),observe(right)
    matched=not l.get('timed_out',False) and not c.get('timed_out',False) and helpers.same(l,c) and lo==co and lo['schema']['code']==0 and lo['schema']['stdout'].startswith('ok\n')
    cases.append(dict(feature=feature,sql=sql,mode=mode,lean=l,sqlite=c,normalized_lean_error=helpers.error(l),normalized_sqlite_error=helpers.error(c),observation_lean=lo,observation_sqlite=co,matched=matched))
    a.output.write_text(json.dumps(dict(complete=False,seed=a.seed,implementation_sha256=source,executable_sha256=exe,cases=cases,failures=sum(not c['matched'] for c in cases)),indent=2)+'\n')
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 report=dict(complete=True,seed=a.seed,setup=setup,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),cases=cases,failures=sum(not c['matched'] for c in cases));a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(features=len(probes),cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
