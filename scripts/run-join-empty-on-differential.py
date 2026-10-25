#!/usr/bin/env python3
"""Compare LEFT JOIN ON evaluation with empty and nonempty inputs.

Validate names, function signatures and generated errors before execution.
Empty-side fixtures plus nonempty controls retain every mismatch, including
currently unsupported dynamic predicates and partial-error output. Fixed controls plus newly
seeded fixtures/combinations, full output/error status, immutable main/WAL
images and independent C typed/integrity checks. Preserve every mismatch.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354510);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 predicates=['abs(-9223372036854775808)','abs(a.k)','abs(b.k)','coalesce(a.k,b.k)',
  'not_a_function(a.k)','coalesce(missing,1)','abs(true)',"min(a.k COLLATE missing,'x')",
  '-0x8000000000000000','0x10000000000000000','sum(a.k)',"json_extract(a.k,'$')",
  'coalesce(a.k)','abs(a.k,a.k)','random()','likelihood(a.k,2.0)',
  'a.k IN (0,abs(-9223372036854775808))','(a.k=1) OR abs(-9223372036854775808)',
  'a.k+b.k>0',"a.k LIKE '%a%'",'a.k IS b.k','a.k COLLATE nocase=b.k']
 predicates += [f'({expression}) OR 1' for expression in predicates[:16]]
 queries=[]
 for predicate in predicates:
  for where in ['', ' WHERE b.id IS NULL', ' WHERE a.id>1', ' WHERE a.k IS NOT NULL']:
   for tail in [' ORDER BY a.id,b.id', ' ORDER BY 2 DESC,1 NULLS FIRST LIMIT 2 OFFSET 1', ' ORDER BY a.id DESC LIMIT 0']:
    queries.append(f'SELECT a.id,b.id FROM l a LEFT JOIN r b ON {predicate}{where}{tail};')
 for predicate in predicates[:8]:
  for operation in ['UNION ALL','UNION','INTERSECT','EXCEPT']:
   queries.append(f'SELECT a.id,b.id FROM l a LEFT JOIN r b ON {predicate} {operation} SELECT 99,98 ORDER BY 1,2;')
 for _ in range(a.random_cases):
  first=rng.choice(predicates);second=rng.choice(predicates);operator=rng.choice(['AND','OR'])
  queries.append(f'SELECT a.id,b.id FROM l a LEFT JOIN r b ON ({first}) {operator} ({second}) ORDER BY a.id,b.id LIMIT {rng.randrange(-1,8)} OFFSET {rng.randrange(-1,8)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-empty-on-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3];counts=[(0,4),(3,0),(0,0),(3,4)][fixture%4]
   if fixture>=4:counts=tuple(0 if n==0 else rng.randrange(1,12) for n in counts)
   left_bool=',"true"' if fixture%3 else ''
   right_bool=(',"false"' if fixture%3==1 else ',"true"') if fixture%3 else ''
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,k{left_bool});CREATE TABLE r(id INTEGER PRIMARY KEY,k{right_bool});' 
   values=['NULL','0','0.0','1','1.0',"'1'","'01'","X'31'",'2','2.5',"'a'","'A'","'a '","'A  '",'-9223372036854775808','9223372036854775807',"'1x'","'0.5suffix'","'  -2tail'","X'31FF'","X'00'","X'302E35FF'","CAST(X'3100FF' AS TEXT)","CAST(X'FF31' AS TEXT)",'1e-310','1e999','-1e999']
   if fixture==0:counts=(0,14)
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
     matched=(bool(l['code'])==bool(r['code'])) and l['stdout']==r['stdout']
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=matched))
    observation='PRAGMA integrity_check;SELECT id,typeof(k),hex(k) FROM l ORDER BY id;SELECT id,typeof(k),hex(k) FROM r ORDER BY id;'
    lo=csql(left,observation);ro=csql(right,observation)
    fixtures.append(dict(fixture=fixture,page_size=page,mode=mode,setup=setup,lean_unchanged=before_l==snapshot(left),sqlite_unchanged=before_r==snapshot(right),observation_lean=lo,observation_sqlite=ro,matched=before_l==snapshot(left) and before_r==snapshot(right) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')))
 failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures)
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,fixtures=fixtures,failures=failures,implementation_sha256=digest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),fixtures=len(fixtures),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
