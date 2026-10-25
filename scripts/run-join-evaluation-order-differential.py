#!/usr/bin/env python3
"""Compare public joined evaluation order, LIMIT and error propagation.

The fixed corpus includes integer overflow, early windows, WHERE filtering,
aggregates, all four join kinds and static/dynamic ON expressions. Seeded
fixtures vary safe data and the position of the overflowing row. Complete
stdout is compared even on errors, retaining partial-output differences.
Every mismatch and immutable C-created file/WAL observation is retained.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354590);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 queries=[]
 for kind in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']:
  for on in ['a.id=b.id','a.id+0=b.id','abs(a.k)=b.k','a.id=b.k+1']:
   for projection in ['abs(a.k),a.id,b.id','a.id,b.id','count(*)']:
    for condition in ['', ' WHERE a.id>1', ' WHERE 0']:
     for tail in ['', ' ORDER BY a.id DESC,b.id LIMIT 1', ' ORDER BY a.id DESC,b.id LIMIT 1 OFFSET 1',' LIMIT 0']:
      queries.append(f'SELECT {projection} FROM l a {kind} r b ON {on}{condition}{tail};')
 for _ in range(a.random_cases):
  kind=rng.choice(['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN'])
  on=rng.choice(['a.id=b.id','a.id+0=b.id','abs(a.k)=b.k','a.id=b.k+1'])
  projection=rng.choice(['abs(a.k),a.id,b.id','a.id,b.id','count(*)'])
  condition=rng.choice(['', ' WHERE a.id>1',' WHERE a.id<4',' WHERE a.id!=2',' WHERE 0',' WHERE 1'])
  direction=rng.choice(['ASC','DESC'])
  queries.append(f'SELECT {projection} FROM l a {kind} r b ON {on}{condition} ORDER BY a.id {direction},b.id LIMIT {rng.randrange(0,5)} OFFSET {rng.randrange(0,4)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-evaluation-order-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3]
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER);CREATE TABLE r(id INTEGER PRIMARY KEY,k INTEGER);'
   bad=1 if fixture==0 else rng.randrange(1,5)
   for i in range(1,5):
    left=-9223372036854775808 if i==bad else (i if fixture==0 else rng.randrange(-5,6))
    right=i if fixture==0 else rng.randrange(-5,6)
    setup+=f'INSERT INTO l VALUES({i},{left});INSERT INTO r VALUES({i},{right});'
   assert csql(base,setup)['code']==0
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);before_l=snapshot(left);before_r=snapshot(right)
    for sql in queries:
     l=run([str(binary),mode,str(left)],sql);r=csql(right,sql)
     matched=(bool(l['code'])==bool(r['code'])) and l['stdout']==r['stdout']
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=matched))
    observation='PRAGMA integrity_check;SELECT id,typeof(k),hex(k) FROM l ORDER BY id;SELECT id,typeof(k),hex(k) FROM r ORDER BY id;'
    lo=csql(left,observation);ro=csql(right,observation)
    fixtures.append(dict(fixture=fixture,page_size=page,mode=mode,setup=setup,lean_unchanged=before_l==snapshot(left),sqlite_unchanged=before_r==snapshot(right),observation_lean=lo,observation_sqlite=ro,matched=before_l==snapshot(left) and before_r==snapshot(right) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')))
 failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures)
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,fixtures=fixtures,failures=failures,implementation_sha256=digest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),fixtures=len(fixtures),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
