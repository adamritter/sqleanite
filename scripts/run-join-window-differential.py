#!/usr/bin/env python3
"""Compare two-table DISTINCT and LIMIT/OFFSET after ordinary/outer joins.

Exact successful output and error status on C-created images in both file modes.
Mixed INTEGER/REAL/TEXT/BLOB/NULL outputs exercise SQL numeric duplicate equality
and first stored representatives. Ordered output uses explicit source columns.
Every mismatch is retained; aliases/ordinals, collations and larger joins are
separate work. Main/WAL images and typed C observations must remain unchanged.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354380);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 sources=['l AS a CROSS JOIN r AS b','l AS a JOIN r AS b','l AS a JOIN r AS b ON a.id=b.id',
  'l AS a LEFT JOIN r AS b ON a.id=b.id','l AS a JOIN r AS b USING(id)',
  'l AS a NATURAL LEFT JOIN r AS b']
 projections=['a.k','b.k','a.k,b.k','*','a.id,b.id']
 windows=['',' LIMIT 0 OFFSET 1',' LIMIT 1 OFFSET 1',' LIMIT 2 OFFSET 2',
  ' LIMIT -1 OFFSET 2',' LIMIT 2,3',' LIMIT 3 OFFSET -2',
  " LIMIT '2' OFFSET '1.0'",' LIMIT (1+1) OFFSET abs(-1)',
  ' LIMIT 2 OFFSET 999999999999',' LIMIT 0 OFFSET 1.5']
 queries=[]
 for source in sources:
  for projection in projections:
   for distinct in ['', 'DISTINCT ']:
    for window in windows:
     queries.append(f'SELECT {distinct}{projection} FROM {source} ORDER BY a.id,b.id{window};')
 for source in sources:
  for projection in projections:
   for order in ['a.id DESC,b.id DESC','a.id,b.id DESC','a.id DESC,b.id',
     'a.id DESC,b.k DESC,b.id','b.id DESC,a.id DESC','b.id DESC,a.k DESC,a.id']:
    queries.append(f'SELECT DISTINCT {projection} FROM {source} ORDER BY {order} LIMIT 2 OFFSET 1;')
 for _ in range(a.random_cases):
  source=rng.choice(sources);projection=rng.choice(projections);distinct=rng.choice(['','DISTINCT '])
  order=rng.choice(['a.id,b.id','a.k,b.k,a.id,b.id','a.id DESC,b.id DESC','b.id DESC,a.id','a.id DESC,b.k DESC,b.id'])
  condition=rng.choice(['',' WHERE a.id<5',' WHERE b.id IS NULL',' WHERE a.id<2 OR b.id>2'])
  queries.append(f'SELECT {distinct}{projection} FROM {source}{condition} ORDER BY {order} LIMIT {rng.randrange(-2,9)} OFFSET {rng.randrange(-2,12)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-window-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3];counts=[(3,4),(0,4),(3,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(0,12),rng.randrange(0,12))
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,k);CREATE TABLE r(id INTEGER PRIMARY KEY,k);'
   values=['NULL','0','0.0','1','1.0',"'1'","'01'","X'31'",'2','2.5',"'a'","'A'",'-9223372036854775808','9223372036854775807']
   if fixture==0:counts=(8,8)
   for table,count in zip(['l','r'],counts):
    for i in range(1,count+1):
     value=values[(i-1)%len(values)] if fixture==0 else rng.choice(values)
     setup+=f'INSERT INTO {table} VALUES({i},{value});'
   assert csql(base,setup)['code']==0
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);before_l=snapshot(left);before_r=snapshot(right)
    for sql in queries:
     l=run([str(binary),mode,str(left)],sql);r=csql(right,sql)
     matched=(l['code']==r['code']==0 and l['stdout']==r['stdout']) or(l['code']>0 and r['code']>0)
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=matched))
    observation='PRAGMA integrity_check;SELECT id,typeof(k),hex(k) FROM l ORDER BY id;SELECT id,typeof(k),hex(k) FROM r ORDER BY id;'
    lo=csql(left,observation);ro=csql(right,observation)
    fixtures.append(dict(fixture=fixture,page_size=page,mode=mode,setup=setup,lean_unchanged=before_l==snapshot(left),sqlite_unchanged=before_r==snapshot(right),observation_lean=lo,observation_sqlite=ro,matched=before_l==snapshot(left) and before_r==snapshot(right) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')))
 failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures)
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,fixtures=fixtures,failures=failures,implementation_sha256=digest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),fixtures=len(fixtures),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
