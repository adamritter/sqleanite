#!/usr/bin/env python3
"""Compare two-table INNER/LEFT/CROSS/comma join syntax and optional ON.

Exercises all zero-to-three-word combinations of INNER/CROSS/LEFT/OUTER,
including invalid combinations. NATURAL, RIGHT/FULL, USING, scalar join
projections and joins of more than two tables are separate unsupported work.
Compare complete successful output and error status against pinned C SQLite;
read queries must preserve both engines' main/WAL bytes. Retain all failures.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354350);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 words=['INNER','CROSS','LEFT','OUTER'];joins=['JOIN',',']+[' '.join(parts)+' JOIN' for n in range(1,4) for parts in itertools.product(words,repeat=n)]
 queries=[]
 for join in joins:
  for condition in ['', ' ON a.id=b.id']:
   queries.append(f'SELECT a.id,b.id,a.v,b.v FROM l AS a {join} r AS b{condition} ORDER BY a.id,b.id;')
 for _ in range(a.random_cases):
  join=rng.choice(joins);condition=rng.choice(['',' ON a.id=b.id',' ON a.id<b.id',' ON a.v=b.v'])
  where=rng.choice(['',' WHERE a.id<3',' WHERE b.id IS NULL',' WHERE a.id<2 OR b.id>2'])
  projection=rng.choice(['a.id,b.id','a.*,b.*','b.id,a.v','a.v,b.v'])
  tail=rng.choice(['',f' LIMIT {rng.randrange(0,9)}',f" LIMIT '{rng.randrange(0,6)}.0'"])
  queries.append(f'SELECT {projection} FROM l AS a {join} r AS b{condition}{where} ORDER BY a.id,b.id{tail};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-syntax-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3];counts=[(3,4),(0,4),(3,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(0,12),rng.randrange(0,12))
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,v);CREATE TABLE r(id INTEGER PRIMARY KEY,v);'
   for table,count in zip(['l','r'],counts):
    for i in range(1,count+1):setup+=f"INSERT INTO {table} VALUES({i},{rng.choice(['NULL','1','2',chr(39)+'A'+chr(39),chr(39)+'a'+chr(39)])});"
   assert csql(base,setup)['code']==0
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);before_l=snapshot(left);before_r=snapshot(right)
    for sql in queries:
     l=run([str(binary),mode,str(left)],sql);r=csql(right,sql)
     matched=(l['code']==r['code']==0 and l['stdout']==r['stdout']) or(l['code']>0 and r['code']>0)
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=matched))
    observation='PRAGMA integrity_check;SELECT id,typeof(v),hex(v) FROM l ORDER BY id;SELECT id,typeof(v),hex(v) FROM r ORDER BY id;'
    lo=csql(left,observation);ro=csql(right,observation)
    fixtures.append(dict(fixture=fixture,page_size=page,mode=mode,setup=setup,lean_unchanged=before_l==snapshot(left),sqlite_unchanged=before_r==snapshot(right),observation_lean=lo,observation_sqlite=ro,matched=before_l==snapshot(left) and before_r==snapshot(right) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')))
 failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures)
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,fixtures=fixtures,failures=failures,implementation_sha256=digest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),fixtures=len(fixtures),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
