#!/usr/bin/env python3
"""Compare public jsonb_extract() with pinned upstream random_json/random_json5 data.

Each generated JSON/JSON5 text and its C JSONB is retained, alongside an
unfiltered byte mutation. Each input is executed separately through both public
file modes and C, so a malformed value cannot mask another value. Full exact
SQL storage type and quoted-value hex output, status and first diagnostic are compared. C alone loads the upstream
generator. File snapshots and independent C integrity are checked after reads.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('json_position',ROOT/'scripts/run-json-position-differential.py')
helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--start-seed',type=int,required=True);p.add_argument('--count',type=int,default=1024);p.add_argument('--extension',type=Path,required=True);p.add_argument('--generator-source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();executable=sha(binary);rng=random.Random(a.start_seed)
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:sha(Path(str(path)+s)) for s in ['','-wal'] if Path(str(path)+s).exists()}
 setup=f'.load {a.extension} sqlite3_randomjson_init\nCREATE TABLE t(id INTEGER PRIMARY KEY,v);\n'
 for i,expr in enumerate(['random_json(seed)','random_json5(seed)','jsonb(random_json(seed))','jsonb(random_json5(seed))']):
  setup+=f'WITH RECURSIVE seeds(seed) AS (VALUES({a.start_seed}) UNION ALL SELECT seed+1 FROM seeds WHERE seed<{a.start_seed+a.count-1}) INSERT INTO t SELECT seed*4+{i},{expr} FROM seeds;\n'
 setup+='SELECT id,typeof(v),hex(v) FROM t ORDER BY id;'
 generated=csql(':memory:',setup);assert generated['code']==0,generated;inputs=[]
 for line in generated['stdout'].splitlines():
  index,kind,data=line.split('|');data=bytes.fromhex(data)
  for changed,value in [(False,data),(True,helpers.mutate(rng,data))]:
   inputs.append(dict(seed=int(index)//4,representation=int(index)%4,mutated=changed,storage=kind,input_hex=value.hex()))
 assert len(inputs)==8*a.count
 cases=[];runs=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-jsonb-upstream-') as tmp:
  folder=Path(tmp);base=folder/'base.db';assert csql(base,'CREATE TABLE guard(id INTEGER PRIMARY KEY);')['code']==0
  for mode in ['--verified-file','--verified-wal-file']:
   left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
   for value in inputs:
    expr="X'"+value['input_hex']+"'"
    if value['storage']=='text':expr='CAST('+expr+' AS TEXT)'
    selected=[rng.choice(["'$'","'$.a'","'$[0]'","'$[#-1]'","'bad'",'NULL',"X'242e61'"]) for _ in range(rng.randrange(1,4))]
    for paths in [["'$'"],selected]:
     call='jsonb_extract('+expr+','+','.join(paths)+')';sql=f'SELECT typeof({call}),hex(quote({call}));'
     l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);cases.append(dict(value,paths=paths,mode=mode,lean=l,sqlite=c,matched=helpers.same(l,c)))
   lo,co=csql(left,'PRAGMA integrity_check;SELECT * FROM guard;'),csql(right,'PRAGMA integrity_check;SELECT * FROM guard;')
   runs.append(dict(mode=mode,lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),observation_lean=lo,observation_sqlite=co,matched=lo['code']==co['code']==0 and lo['stdout']==co['stdout']=='ok\n' and bl==snapshot(left) and br==snapshot(right)))
 assert source==helpers.digest() and executable==sha(binary)
 failures=sum(not c['matched'] for c in cases+runs)
 report=dict(start_seed=a.start_seed,count=a.count,generation_sql=setup,generator_source_sha256=sha(a.generator_source),extension_sha256=sha(a.extension),cases=cases,runs=runs,failures=failures,implementation_sha256=source,executable_sha256=executable,harness_sha256=sha(Path(__file__)),helper_sha256=sha(ROOT/'scripts/run-json-position-differential.py'),comparison=__doc__.strip(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
