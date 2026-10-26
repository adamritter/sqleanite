#!/usr/bin/env python3
"""Persist ordinary median/percentile aggregate results and failures in both public Core file engines.

Pinned C supplies page geometry. Newly seeded numeric and mixed-type data and SQL
variants mix with fixed transaction/INSERT/UPDATE/DELETE/RETURNING/CTAS
templates. Compare full stdout, normalized first-line error, post-statement
C typed rows/catalog/integrity, Lean reopen, and a subsequent independent C
write. Preserve unchanged files when C leaves its input unchanged. Page size
is recorded separately because the current writer may convert it to 4096.
"""
import argparse,hashlib,json,os,random,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def literal(s):
 data=s.encode() if isinstance(s,str) else s
 return "CAST(X'"+data.hex()+"' AS TEXT)"
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354893);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=16);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=120)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def error(r):
  if not r['code']:return ''
  line=r['stderr'].splitlines()[0] if r['stderr'] else ''
  return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',line)
 def snapshot(path):
  return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 def same(l,r):return bool(l['code'])==bool(r['code']) and l['stdout']==r['stdout'] and error(l)==error(r)
 inputs=['NULL','0','-0.0','1','1.25','-1.25','9223372036854775807','-9223372036854775808','1e308','-1e308','1e999','-1e999',literal('1'),literal('x'),"X'31'"]
 generated=[]
 for _ in range(a.random_cases):
  value=rng.choice([str(rng.randrange(-10**18,10**18)),repr(rng.uniform(-1e20,1e20)),rng.choice(['NULL','0','1.5','-1.5'])]);inputs.append(value);generated.append(value)
 scripts=[]
 def add(group,sql):scripts.append(dict(group=group,sql=sql))
 functions=['median','percentile','percentile_cont','percentile_disc']
 for fn in functions:
  parameter='50' if fn=='percentile' else '.5'
  for argument in ['v','v+0.0']:
   expr=fn+'('+argument+('' if fn=='median' else ','+parameter)+')'
   for where in ['', ' WHERE id<=10', ' WHERE id>15', ' WHERE 0']:
    add('insert-select',f'INSERT INTO out SELECT 1,{expr} FROM t'+where+';')
    add('ctas',f'CREATE TABLE made AS SELECT 1 AS id,{expr} AS valid FROM t'+where+';')
   add('insert-grouped',f'INSERT INTO out SELECT id%3,{expr} FROM t WHERE id<=10 GROUP BY id%3;')
   add('ctas-grouped',f'CREATE TABLE made AS SELECT id%3 AS id,{expr} AS valid FROM t WHERE id<=10 GROUP BY id%3;')
  args='v' if fn=='median' else 'v,flags'
  add('dynamic-fraction','INSERT INTO out SELECT 1,'+fn+'('+args+') FROM t;')
 for suffix in ['ROLLBACK;','COMMIT;']:
  add('transaction','BEGIN;\nINSERT INTO out SELECT 1,median(v) FROM t WHERE id<=10;\n'+suffix+'\nSELECT * FROM out ORDER BY id;')
 add('savepoint','SAVEPOINT p;\nINSERT INTO out SELECT 1,percentile_cont(v,.5) FROM t WHERE id<=10;\nROLLBACK TO p;\nRELEASE p;\nSELECT * FROM out ORDER BY id;')
 add('atomic-error','INSERT INTO out SELECT id%3,median(v) FROM t GROUP BY id%3;')
 add('transaction-error','BEGIN;\nINSERT INTO out SELECT 1,median(v) FROM t WHERE id<=10;\nINSERT INTO out SELECT 2,percentile(v,NULL) FROM t;\nCOMMIT;')
 add('admission-error','INSERT INTO out SELECT 1,median() FROM t WHERE 0;')
 add('admission-error','CREATE TABLE made AS SELECT 1 AS id,percentile_cont(v) AS valid FROM t WHERE 0;')
 add('misuse-error','UPDATE t SET valid=median(v) WHERE 0;')
 for _ in range(a.random_cases):
  fn=rng.choice(functions);parameter=repr(rng.uniform(-.05,1.05)*(100 if fn=='percentile' else 1));lo=rng.randrange(len(inputs)+1);hi=lo+rng.randrange(1,10)
  expr=fn+'(v'+('' if fn=='median' else ','+parameter)+')'
  add('seeded-write',f'INSERT INTO out SELECT 1,{expr} FROM t WHERE id BETWEEN {lo} AND {hi};')
 observation='PRAGMA integrity_check;PRAGMA user_version;PRAGMA application_id;PRAGMA table_info(t);PRAGMA table_info(out);PRAGMA table_info(made);SELECT id,typeof(v),hex(v),typeof(flags),quote(flags),typeof(valid),quote(valid) FROM t ORDER BY id;SELECT id,typeof(valid),quote(valid) FROM out ORDER BY id;'
 read='SELECT id,typeof(v),hex(v),typeof(flags),quote(flags),typeof(valid),quote(valid) FROM t ORDER BY id;SELECT id,typeof(valid),quote(valid) FROM out ORDER BY id;'
 cases=[];fixtures=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-write-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=512<<(fixture%8)
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v,flags,valid);CREATE TABLE out(id INTEGER PRIMARY KEY,valid);'
   for i,value in enumerate(inputs):
    flags=repr(.5+rng.uniform(-.0004,.0004))
    setup+=f'INSERT INTO t VALUES({i+1},{value},{flags},NULL);'
   created=csql(base,setup);assert created['code']==0,created
   fixtures.append(dict(fixture=fixture,page_size=page,setup=setup))
   for mode in ['--verified-file','--verified-wal-file']:
    for index,script in enumerate(scripts):
     case_dir=folder/(mode+str(index));case_dir.mkdir();left=case_dir/'lean.db';right=case_dir/'sqlite.db';shutil.copyfile(base,left);shutil.copyfile(base,right)
     bl,br=snapshot(left),snapshot(right)
     l=run([str(binary),mode,str(left)],script['sql']);c=csql(right,script['sql']);al,ar=snapshot(left),snapshot(right)
     lo,co=csql(left,observation),csql(right,observation)
     made=csql(right,"SELECT count(*) FROM sqlite_schema WHERE name='made';")['stdout']=='1\n'
     extra='SELECT id,typeof(valid),quote(valid) FROM made ORDER BY id;' if made else ''
     lr=run([str(binary),mode,str(left)],read+extra);cr=csql(right,read+extra)
     geometry=dict(lean=csql(left,'PRAGMA page_size;'),sqlite=csql(right,'PRAGMA page_size;'))
     follow="INSERT INTO t VALUES(100000,'{}',1,1);SELECT id,typeof(v),hex(v),typeof(valid),quote(valid) FROM t ORDER BY id;PRAGMA integrity_check;"
     lw,cw=csql(left,follow),csql(right,follow)
     matched=same(l,c) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and same(lr,cr) and lw['code']==cw['code']==0 and lw['stdout']==cw['stdout'] and (ar!=br or al==bl)
     cases.append(dict(script,fixture=fixture,page_size=page,mode=mode,lean=l,sqlite=c,lean_error=error(l),sqlite_error=error(c),observation_lean=lo,observation_sqlite=co,reopen_lean=lr,reopen_sqlite=cr,subsequent_c_write_lean=lw,subsequent_c_write_sqlite=cw,geometry=geometry,lean_unchanged=al==bl,sqlite_unchanged=ar==br,matched=matched))
 assert source==digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 failures=sum(not c['matched'] for c in cases)
 report=dict(seed=a.seed,random_cases=a.random_cases,generated_values=generated,fixtures=fixtures,cases=cases,failures=failures,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
