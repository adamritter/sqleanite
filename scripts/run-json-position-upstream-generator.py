#!/usr/bin/env python3
"""JSON diagnostic-position controls from pinned SQLite's randomjson test-data generator.

Only the C oracle process loads the upstream extension. Production never calls
the generator, C, Python, or an external parser. Four input representations per
seed (JSON text, JSON5 text, JSONB of each) pass through both public file modes.
Seeded byte mutations and trailing garbage supplement the original values, with immutable
main/WAL bytes and independent C typed-row/integrity observations.
"""
import argparse,hashlib,json,os,shutil,subprocess,tempfile,time,random,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def mutate(rng,data):
 data=bytearray(data)
 for _ in range(rng.randrange(1,5)):
  pos=rng.randrange(len(data)+1);op=rng.randrange(3)
  if op==0:data[pos:pos]=bytes([rng.randrange(256)])
  elif pos<len(data) and op==1:del data[pos]
  elif pos<len(data):data[pos]=rng.randrange(256)
 return bytes(data)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--start-seed',type=int,default=1);p.add_argument('--count',type=int,default=5000);p.add_argument('--page-size',type=int,default=4096);p.add_argument('--extension',type=Path,required=True);p.add_argument('--generator-source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=digest();exe=sha(binary)
 def run(cmd,sql):
  start=time.time();r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=600)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'),seconds=time.time()-start)
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:sha(Path(str(path)+s)) for s in ['','-wal'] if Path(str(path)+s).exists()}
 cases=[];runs=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-upstream-') as tmp:
  folder=Path(tmp);base=folder/'base.db'
  setup=f'.load {a.extension} sqlite3_randomjson_init\nPRAGMA page_size={a.page_size};CREATE TABLE t(id INTEGER PRIMARY KEY,v);\n'
  for offset,expr in enumerate(['random_json(seed)','random_json5(seed)','jsonb(random_json(seed))','jsonb(random_json5(seed))']):
   setup+=f'WITH RECURSIVE seeds(seed) AS (VALUES({a.start_seed}) UNION ALL SELECT seed+1 FROM seeds WHERE seed<{a.start_seed+a.count-1}) INSERT INTO t SELECT seed*4+{offset},{expr} FROM seeds;\n'
  generated=csql(base,setup);assert generated['code']==0,generated
  values=csql(base,'SELECT id,typeof(v),hex(v) FROM t ORDER BY id;');assert values['code']==0,values
  inputs=values['stdout'].splitlines();assert len(inputs)==4*a.count
  # Preserve each generated value, then add a mutation in the same storage class.
  rng=random.Random(a.start_seed);mutation_sql='BEGIN;';original_count=len(inputs)
  for original in inputs:
   identifier,kind,data=original.split('|');encoded=mutate(rng,bytes.fromhex(data));expr="X'"+encoded.hex()+"'"
   if kind=='text':expr='CAST('+expr+' AS TEXT)'
   mutation_sql+='INSERT INTO t VALUES('+str(int(identifier)+(a.start_seed+a.count+1)*4)+','+expr+');'
  mutation_sql+='COMMIT;';mutated=csql(base,mutation_sql);assert mutated['code']==0,mutated
  values=csql(base,'SELECT id,typeof(v),hex(v) FROM t ORDER BY id;');assert values['code']==0,values
  inputs=values['stdout'].splitlines();assert len(inputs)==2*original_count
  fields=['quote(json_error_position(v))','quote(json_error_position(CAST(v AS TEXT)))','json_valid(v,2)','json_valid(v,8)']
  sql='SELECT id,'+','.join(fields)+' FROM t ORDER BY id;'
  for mode in ['--verified-file','--verified-wal-file']:
   left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
   l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);ll,cl=l['stdout'].splitlines(),c['stdout'].splitlines()
   assert len(cl)==len(inputs),c
   for i,wanted in enumerate(cl):
    actual=ll[i] if i<len(ll) else None;identifier,kind,hexvalue=inputs[i].split('|')
    cases.append(dict(mode=mode,seed=(int(identifier)//4 if i<original_count else int(identifier)//4-(a.start_seed+a.count+1)),representation=int(identifier)%4,mutated=i>=original_count,input_type=kind,input_hex=hexvalue,lean=actual,sqlite=wanted,matched=actual==wanted))
   lo=csql(left,'PRAGMA integrity_check;SELECT id,typeof(v),hex(v) FROM t ORDER BY id;');co=csql(right,'PRAGMA integrity_check;SELECT id,typeof(v),hex(v) FROM t ORDER BY id;')
   runs.append(dict(mode=mode,sql=sql,lean=l,sqlite=c,lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),observation_lean=lo,observation_sqlite=co,
     matched=l['code']==c['code']==0 and l['stdout']==c['stdout'] and len(ll)==len(cl) and bl==snapshot(left) and br==snapshot(right) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n')))
 assert source==digest() and exe==sha(binary),'Implementation changed during evaluation'
 failures=sum(not c['matched'] for c in cases)+sum(not r['matched'] for r in runs)
 report=dict(start_seed=a.start_seed,count=a.count,page_size=a.page_size,generator_source=str(a.generator_source),generator_source_sha256=sha(a.generator_source),extension_sha256=sha(a.extension),generation_sql=setup,mutation_sql=mutation_sql,comparison=__doc__.strip(),
  cases=cases,runs=runs,failures=failures,implementation_sha256=source,executable_sha256=exe,harness_sha256=sha(Path(__file__)),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
