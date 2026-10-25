#!/usr/bin/env python3
"""Compare literal and quoted/Boolean column atoms in joined outputs.

Exact successful output/error status and immutable C-created files in both
modes. Include Boolean column shadowing in comparisons, outer padding, merged
names, DISTINCT, aliases, ordinal ordering and windows. Typed C observations
remain independent; all mismatches are retained. General row expressions are
separate work.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354410);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 sources=['l AS a CROSS JOIN r AS b','l AS a JOIN r AS b ON a.id=b.id',
  'l AS a LEFT JOIN r AS b ON a.id=b.id','l AS a JOIN r AS b USING(id)',
  'l AS a NATURAL LEFT JOIN r AS b']
 projections=['1','NULL',"'x'","X'80FF'",'1.5','-1','+1','~1','NOT NULL',
  '-9223372036854775808','9223372036854775807',"+'a'","~'x'",
  'true','false','"k"','"id"','"true"','"false"','a."k"',
  "1,a.id,b.id,'x'","'1',1,1.0,X'31'",'true AS truth,false AS f,a.id,b.id','"k" AS x,a.id,b.id']
 tails=[' ORDER BY a.id,b.id',' ORDER BY 1,a.id,b.id',
  ' ORDER BY 1 DESC,a.id,b.id LIMIT 2 OFFSET 1',' ORDER BY 1,a.id,b.id LIMIT 0']
 queries=[f'SELECT {distinct}{projection} FROM {source}{tail};'
  for source in sources for projection in projections for distinct in ['', 'DISTINCT '] for tail in tails]
 for source in sources:
  for predicate in ['true=1','false=0','"true"=1','"k"=1','"k" IS NULL']:
   queries.append(f'SELECT a.id,b.id FROM {source} WHERE {predicate} ORDER BY a.id,b.id;')
  queries.append(f'SELECT 1 AS z,a.id,b.id FROM {source} ORDER BY z DESC,a.id,b.id;')
 for source in sources:
  queries += [f'SELECT 1,a.id FROM {source} UNION ALL SELECT 2,99 ORDER BY 1,2;',
   f'SELECT true FROM {source} UNION SELECT false FROM {source} ORDER BY 1;',
   f'SELECT "k" FROM {source} UNION ALL SELECT \'other\' ORDER BY 1;',
   f'SELECT 1 AS x FROM {source} UNION SELECT 2 ORDER BY x;']
 for _ in range(a.random_cases):
  source=rng.choice(sources);projection=rng.choice(projections);distinct=rng.choice(['','DISTINCT '])
  queries.append(f'SELECT {distinct}{projection} FROM {source} ORDER BY 1,a.id DESC,b.id LIMIT {rng.randrange(-1,8)} OFFSET {rng.randrange(-1,8)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-atoms-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3];counts=[(3,4),(0,4),(3,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(0,12),rng.randrange(0,12))
   left_bool=',"true"' if fixture%3 else ''
   right_bool=(',"false"' if fixture%3==1 else ',"true"') if fixture%3 else ''
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,k{left_bool});CREATE TABLE r(id INTEGER PRIMARY KEY,k{right_bool});' 
   values=['NULL','0','0.0','1','1.0',"'1'","'01'","X'31'",'2','2.5',"'a'","'A'",'-9223372036854775808','9223372036854775807']
   if fixture==0:counts=(8,8)
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
     matched=(l['code']==r['code']==0 and l['stdout']==r['stdout']) or(l['code']>0 and r['code']>0)
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=matched))
    observation='PRAGMA integrity_check;SELECT id,typeof(k),hex(k) FROM l ORDER BY id;SELECT id,typeof(k),hex(k) FROM r ORDER BY id;'
    lo=csql(left,observation);ro=csql(right,observation)
    fixtures.append(dict(fixture=fixture,page_size=page,mode=mode,setup=setup,lean_unchanged=before_l==snapshot(left),sqlite_unchanged=before_r==snapshot(right),observation_lean=lo,observation_sqlite=ro,matched=before_l==snapshot(left) and before_r==snapshot(right) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')))
 failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures)
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,fixtures=fixtures,failures=failures,implementation_sha256=digest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),fixtures=len(fixtures),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
