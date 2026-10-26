#!/usr/bin/env python3
"""Persist jsonb() results and failures in both public Core file engines.

Pinned C supplies page geometry and input JSONB. Newly seeded data and SQL
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
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354973);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=16);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
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
 inputs=[literal(s) for s in ['null','1','[]','{"a":[1,true]}','{a:1}','[1,]','"\\x41"','invalid','[','01','1\0junk']]
 inputs += ['NULL','1','1.25',"X'00'","X'0b'","X'3c176100'","X'1bff'","X'c000'","X'00ff'"]
 generated=[]
 for _ in range(a.random_cases):
  value={'v':[rng.randrange(-100000,100000),rng.choice([None,True,False]),''.join(rng.choice('abé中😀') for _ in range(5))]}
  s=json.dumps(value,ensure_ascii=False);r=csql(':memory:','SELECT hex(jsonb('+literal(s)+'));');assert r['code']==0,r
  generated.append(dict(text=s,jsonb_hex=r['stdout'].strip()))
  inputs.extend([literal(s),"X'"+r['stdout'].strip()+"'"])
 scripts=[]
 def add(group,sql):scripts.append(dict(group=group,sql=sql))
 for expr in ['jsonb(v)','jsonb(CAST(v AS TEXT))','jsonb(CASE WHEN flags IS NULL THEN NULL ELSE v END)']:
  add('update',f'UPDATE t SET valid={expr};')
  add('insert-select',f'INSERT INTO out SELECT id,{expr} FROM t;')
  add('ctas',f'CREATE TABLE made AS SELECT id,{expr} AS valid FROM t;')
  add('delete',f'DELETE FROM t WHERE {expr}>0;')
  add('update-returning',f'UPDATE t SET valid={expr} WHERE id<=20 RETURNING id,valid;')
 for suffix in ['ROLLBACK;','COMMIT;']:
  add('transaction','BEGIN;\nUPDATE t SET valid=jsonb(v);\n'+suffix+'\nSELECT id,valid FROM t ORDER BY id;')
 add('savepoint','SAVEPOINT j;\nUPDATE t SET valid=jsonb(v);\nROLLBACK TO j;\nRELEASE j;\nSELECT id,valid FROM t ORDER BY id;')
 error_expr='jsonb(CASE WHEN id=3 THEN abs(-9223372036854775808) ELSE v END)'
 add('atomic-error','UPDATE t SET valid='+error_expr+';')
 add('transaction-error','BEGIN;\nUPDATE t SET valid=jsonb(v);\nUPDATE t SET valid='+error_expr+';\nCOMMIT;')
 add('returning-error','UPDATE t SET valid=1 WHERE id<5 RETURNING id,'+error_expr+';')
 add('insert-returning',"INSERT INTO t VALUES(999,'[1,]',2,jsonb('[1,]')) RETURNING id,valid;")
 add('insert-error','INSERT INTO out SELECT id,'+error_expr+' FROM t;')
 add('ctas-error','CREATE TABLE made AS SELECT id,'+error_expr+' AS valid FROM t;')
 add('admission-error','UPDATE t SET valid=jsonb() WHERE 0;')
 add('admission-error','INSERT INTO out SELECT id,jsonb(1,2) FROM t WHERE 0;')
 for expr in ['jsonb(v)','jsonb(CAST(v AS TEXT))']:
  for where in [' WHERE id<=7',' WHERE id>21']:
   add('successful-update',f'UPDATE t SET valid={expr}'+where+' RETURNING id,valid;')
   add('successful-insert',f'INSERT INTO out SELECT id,{expr} FROM t'+where+';')
   add('successful-ctas',f'CREATE TABLE made AS SELECT id,{expr} AS valid FROM t'+where+';')
 add('successful-savepoint','SAVEPOINT j; UPDATE t SET valid=jsonb(v) WHERE id<=7; ROLLBACK TO j; RELEASE j; SELECT id,valid FROM t ORDER BY id;')
 add('successful-transaction','BEGIN; UPDATE t SET valid=jsonb(v) WHERE id<=7; COMMIT; SELECT id,hex(valid) FROM t ORDER BY id;')
 for _ in range(a.random_cases):
  expr=rng.choice(['v','CAST(v AS TEXT)','NULL',error_expr,'flags']);lo=rng.randrange(len(inputs)+1);hi=lo+rng.randrange(1,10)
  add('seeded-update',f'UPDATE t SET valid=jsonb({expr}) WHERE id BETWEEN {lo} AND {hi};')
 observation='PRAGMA integrity_check;PRAGMA user_version;PRAGMA application_id;PRAGMA table_info(t);PRAGMA table_info(out);PRAGMA table_info(made);SELECT id,typeof(v),hex(v),typeof(flags),quote(flags),typeof(valid),quote(valid) FROM t ORDER BY id;SELECT id,typeof(valid),quote(valid) FROM out ORDER BY id;'
 read='SELECT id,typeof(v),hex(v),typeof(flags),quote(flags),typeof(valid),quote(valid) FROM t ORDER BY id;SELECT id,typeof(valid),quote(valid) FROM out ORDER BY id;'
 cases=[];fixtures=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-write-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=512<<(fixture%8)
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v,flags,valid);CREATE TABLE out(id INTEGER PRIMARY KEY,valid);'
   for i,value in enumerate(inputs):
    flags=rng.choice(["'$'","'$.v'","'$[0]'","'$[#-1]'","'bad'",'NULL'])
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
 report=dict(seed=a.seed,random_cases=a.random_cases,generated_jsonb=generated,fixtures=fixtures,cases=cases,failures=failures,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
