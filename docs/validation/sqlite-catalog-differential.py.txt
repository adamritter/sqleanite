#!/usr/bin/env python3
"""Compare exact catalog SQL and persisted rows after data writes and CTAS.

Fixed SQL families mix with fresh seeded values and declaration spelling. Both
file modes start from independent C-created files. Compare complete output,
first diagnostics, all schema SQL bytes, typed rows, C integrity, Lean reopen
and an independent subsequent C write. Geometry is recorded separately. The
explicit-index family is separately selectable to retain evidence for that
distinct catalog object type, not to filter cases by observed outcomes.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('json_position',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
spec=importlib.util.spec_from_file_location('writer',ROOT/'scripts/run-json-insert-write-differential.py');writer=importlib.util.module_from_spec(spec);spec.loader.exec_module(writer)

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--fixtures',type=int,default=8);p.add_argument('--family',choices=['tables','indexes'],default='tables');p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 binary=ROOT/'.lake/build/bin/sqleanite';sqlite=os.environ.get('SQLITE3_BIN','sqlite3');source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=180)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 def declaration(name,variant,tag):
  bodies=[name+'(id INTEGER PRIMARY KEY,v TEXT,n NUMERIC,b BLOB)',
    '['+name+'] ( [id] integer primary key , [v] text , n numeric , b blob )',
    '"'+name+'" (id INTEGER PRIMARY KEY, v /* '+tag+' */ TEXT, n NUMERIC, b BLOB)',
    "'"+name+"'(id integer primary key,v TEXT DEFAULT ('a;''b'),n NUMERIC,b BLOB)",
    name+'(\n id INTEGER PRIMARY KEY,\n v TEXT,\n n NUMERIC,\n b BLOB\n)',
    name+'(id INTEGER, v TEXT,n NUMERIC,b BLOB, PRIMARY KEY(id DESC))',
    name+'(id INTEGER PRIMARY KEY,v VARCHAR(17),n DECIMAL(10,2),b BLOB)',
    name+'(id INTEGER PRIMARY KEY,v TEXT COLLATE BINARY,n NUMERIC,b BLOB)']
  return 'CREATE TABLE '+bodies[variant%len(bodies)]+';'
 scripts=[('update',"UPDATE t SET v=v||' suffix',n=n+1 WHERE id%3=0 RETURNING id,typeof(v),hex(v);",''),
  ('insert',"INSERT INTO t VALUES(1001,'extra',1.25,X'00FF');",''),
  ('delete','DELETE FROM t WHERE id%4=0 RETURNING id;',''),
  ('insert-select','INSERT INTO out SELECT id,v,n,b FROM t;',''),
  ('replace',"REPLACE INTO t VALUES(1,'replaced',-2,X'FF00');",''),
  ('transaction',"BEGIN;UPDATE t SET v='committed' WHERE id=1;COMMIT;",''),
  ('rollback',"SELECT count(*) FROM t;SAVEPOINT c;UPDATE t SET v='rolled back';ROLLBACK TO c;RELEASE c;",''),
  ('ctas','CREATE TABLE made AS SELECT id,v,n,b FROM t;','SELECT id,typeof(v),hex(v),typeof(n),hex(n),typeof(b),hex(b) FROM made ORDER BY id;'),
  ('ctas-empty','CREATE TABLE made AS SELECT id,v,n,b FROM t WHERE 0;','SELECT id,typeof(v),hex(v),typeof(n),hex(n),typeof(b),hex(b) FROM made ORDER BY id;'),
  ('ctas-quoted','CREATE TABLE "made odd" AS SELECT id AS "select",v AS "a b",n AS "very long numeric column name",b AS "é中" FROM t;','SELECT "select",typeof("a b"),hex("a b"),typeof("very long numeric column name"),hex("very long numeric column name"),typeof("é中"),hex("é中") FROM "made odd" ORDER BY "select";'),
  ('atomic-error','UPDATE t SET n=abs(-9223372036854775808);','')]
 rows='SELECT id,typeof(v),hex(v),typeof(n),hex(n),typeof(b),hex(b) FROM t ORDER BY id;SELECT id,typeof(v),hex(v),typeof(n),hex(n),typeof(b),hex(b) FROM out ORDER BY id;'
 observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),typeof(sql),hex(sql) FROM sqlite_schema ORDER BY type,name;'+rows
 cases=[];fixtures=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-catalog-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=512<<(fixture%8)
   tag=''.join(rng.choice('abcXYZ019') for _ in range(24))
   setup=f'PRAGMA page_size={page};'+declaration('t',fixture,tag)+declaration('out',fixture+1,tag)
   if a.family=='indexes':setup+='CREATE INDEX [t n index] ON t(n);CREATE INDEX "t_v" ON t (v);'
   setup+='BEGIN;'
   for i in range(1,24):
    text=''.join(rng.choice('abé中😀\0') for _ in range(rng.randrange(1,80)))
    number=rng.choice(['NULL',str(rng.randrange(-100000,100000)),str(rng.randrange(-10000,10000)/8)])
    value=helpers.literal(text);blob="X'"+rng.randbytes(rng.randrange(1,80)).hex()+"'"
    setup+=f'INSERT INTO t VALUES({i},{value},{number},{blob});'
   setup+='COMMIT;';created=csql(base,setup);assert created['code']==0,created
   fixtures.append(dict(fixture=fixture,page_size=page,setup=setup))
   for mode in ['--verified-file','--verified-wal-file']:
    for i,(group,template,extra) in enumerate(scripts):
     case=folder/(mode+str(i));case.mkdir();left=case/'lean.db';right=case/'sqlite.db';shutil.copyfile(base,left);shutil.copyfile(base,right)
     bl,br=snapshot(left),snapshot(right);sql=writer.statement_lines(template)
     l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);al,ar=snapshot(left),snapshot(right)
     lo,co=csql(left,observe+extra),csql(right,observe+extra)
     lr,cr=run([str(binary),mode,str(left)],writer.statement_lines(rows+extra)),csql(right,rows+extra)
     geometry=dict(lean=csql(left,'PRAGMA page_size;'),sqlite=csql(right,'PRAGMA page_size;'))
     follow="INSERT INTO t VALUES(2001,'follow',4,X'8000');PRAGMA integrity_check;"+rows+extra
     lw,cw=csql(left,follow),csql(right,follow)
     matched=helpers.same(l,c) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and helpers.same(lr,cr) and lw['code']==cw['code']==0 and lw['stdout']==cw['stdout'] and (ar!=br or al==bl)
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,group=group,template_sql=template,sql=sql,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,reopen_lean=lr,reopen_sqlite=cr,follow_lean=lw,follow_sqlite=cw,geometry=geometry,lean_unchanged=al==bl,sqlite_unchanged=ar==br,matched=matched))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 report=dict(seed=a.seed,family=a.family,fixtures=fixtures,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),statement_lines_helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-insert-write-differential.py').read_bytes()).hexdigest(),comparison=__doc__.strip(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
