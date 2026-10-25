#!/usr/bin/env python3
"""Compare value-preserving wrappers on joined projection atoms.

Unary plus, COLLATE and valid probability hints, including DISTINCT, output
aliases/positions, compound metadata and windows. Fixed controls and newly
seeded fixtures/combinations. Full stdout/error status, immutable main/WAL
images and independent C typed observations; retain every mismatch.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354520);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 sources=['l AS a CROSS JOIN r AS b','l AS a JOIN r AS b ON a.id=b.id',
  'l AS a LEFT JOIN r AS b ON a.id=b.id','l AS a JOIN r AS b USING(id)',
  'l AS a NATURAL LEFT JOIN r AS b']
 projections=['+a.k','++a.k','likely(a.k)','unlikely(b.k)','likelihood(a.k,0.25)',
  'a.k COLLATE nocase','b.k COLLATE rtrim','+a.k COLLATE nocase',
  'likely(a.k COLLATE nocase)','(a.k COLLATE nocase) COLLATE rtrim',
  'a.k COLLATE missing','likely(a.k COLLATE missing)',
  'likelihood(a.k,2.0)','likely(a.k,a.id)','likely(missing)',
  'true COLLATE nocase','likely("true")','+"k"',
  "'a' COLLATE nocase", "likely(-9223372036854775808)",
  'a.k COLLATE nocase AS x,b.k COLLATE rtrim AS y',
  'likely(a.k) AS x,a.id,b.id',
  'a.id,a.*,b.k COLLATE nocase', 'a.k COLLATE nocase,1,1.0']
 tails=[' ORDER BY a.id,b.id',' ORDER BY 1,a.id,b.id',
  ' ORDER BY 1 DESC,a.id,b.id LIMIT 2 OFFSET 1',' ORDER BY 1,a.id,b.id LIMIT 0']
 queries=[f'SELECT {distinct}{projection} FROM {source}{tail};'
  for source in sources for projection in projections for distinct in ['', 'DISTINCT '] for tail in tails]
 for source in sources:
  for expression in ['+a.k','likely(a.k)','a.k COLLATE nocase','likely(a.k COLLATE rtrim)',"'a' COLLATE nocase",'a.k COLLATE missing']:
   for ordering in ['x','1','x COLLATE binary',expression]:
    queries.append(f'SELECT {expression} AS x,a.id,b.id FROM {source} ORDER BY {ordering},a.id,b.id;')
   for operation in ['UNION ALL','UNION','INTERSECT','EXCEPT']:
    queries.append(f"SELECT {expression} AS x FROM {source} {operation} SELECT 'A' ORDER BY 1;")
 for source in sources:
  for expression in ['a.k','+a.k','likely(a.k)',"'a'"]:
   for operation in ['UNION','INTERSECT','EXCEPT']:
    for collation in ['nocase','rtrim','missing']:
     queries.append(f"SELECT {expression} FROM {source} {operation} SELECT 'A' COLLATE {collation} ORDER BY 1;")
 for _ in range(a.random_cases):
  source=rng.choice(sources);projection=rng.choice(projections);distinct=rng.choice(['','DISTINCT '])
  queries.append(f'SELECT {distinct}{projection} FROM {source} ORDER BY 1,a.id DESC,b.id LIMIT {rng.randrange(-1,8)} OFFSET {rng.randrange(-1,8)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-wrappers-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3];counts=[(3,4),(0,4),(3,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(0,12),rng.randrange(0,12))
   left_bool=',"true"' if fixture%3 else ''
   right_bool=(',"false"' if fixture%3==1 else ',"true"') if fixture%3 else ''
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,k{left_bool});CREATE TABLE r(id INTEGER PRIMARY KEY,k{right_bool});' 
   values=['NULL','0','0.0','1','1.0',"'1'","'01'","X'31'",'2','2.5',"'a'","'A'","'a '","'A  '","'Z'","CAST(X'610062' AS TEXT)","CAST(X'410063' AS TEXT)","CAST(X'61006263' AS TEXT)","CAST(X'FF61' AS TEXT)",'-9223372036854775808' ,'9223372036854775807']
   if fixture==0:counts=(21,7)
   for table,count in zip(['l','r'],counts):
    for i in range(1,count+1):
     value=values[(i-1)%len(values)] if fixture==0 else rng.choice(values)
     extra=','+str((count-i) if table=='l' else i) if fixture%3 else ''
     setup+=f'INSERT INTO {table} VALUES({i},{value}{extra});'
   assert csql(base,setup)['code']==0
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);before_l=snapshot(left);before_r=snapshot(right)
    for sql in queries:
     l=run([str(binary),mode,str(left)],sql);r=csql(right,sql)
     matched=bool(l['code'])==bool(r['code']) and l['stdout']==r['stdout']
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=matched))
    observation='PRAGMA integrity_check;SELECT id,typeof(k),hex(k) FROM l ORDER BY id;SELECT id,typeof(k),hex(k) FROM r ORDER BY id;'
    lo=csql(left,observation);ro=csql(right,observation)
    fixtures.append(dict(fixture=fixture,page_size=page,mode=mode,setup=setup,lean_unchanged=before_l==snapshot(left),sqlite_unchanged=before_r==snapshot(right),observation_lean=lo,observation_sqlite=ro,matched=before_l==snapshot(left) and before_r==snapshot(right) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')))
 failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures)
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,fixtures=fixtures,failures=failures,implementation_sha256=digest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),fixtures=len(fixtures),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
