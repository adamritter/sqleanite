#!/usr/bin/env python3
"""Compare SQLite truth conversion of atoms in joined ON/WHERE conditions.

Complete successful output/error status, immutable C-created main/WAL images
and independent C typed observations. Cover NULL, numbers, numeric-prefix
TEXT/BLOB, bare/quoted columns, Boolean names, AND/OR/NOT, outer padding and
row windows. General row arithmetic/functions are separate work.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354440);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 atoms=['NULL','0','1','-1','0.0','-0.0','0.5',"'0'","'1'","'1x'","'x'",
  "'  -2.5tail'","X'31'","X'00'","X'302E35FF'",'true','false','a.k','b.k','a.id','"true"','"k"']
 predicates=[variant for atom in atoms for variant in [atom,f'NOT ({atom})',f'({atom}) AND a.id=b.id',f'({atom}) OR a.id=b.id']]
 queries=[]
 for predicate in predicates:
  for source,where in [('l a JOIN r b ON '+predicate,''),('l a LEFT JOIN r b ON '+predicate,''),
    ('l a CROSS JOIN r b',' WHERE '+predicate),('l a LEFT JOIN r b ON a.id=b.id',' WHERE '+predicate)]:
   for tail in ['', ' LIMIT 2 OFFSET 1']:
    queries.append(f'SELECT a.id,b.id FROM {source}{where} ORDER BY a.id,b.id{tail};')
 for predicate in ['0 AND missing','missing AND 0','1 OR missing','0 AND not_a_function()',
   'false AND missing','true OR missing','0 AND "missing"']:
  queries.append(f'SELECT a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE {predicate} ORDER BY a.id,b.id;')
 for _ in range(a.random_cases):
  first=rng.choice(atoms);second=rng.choice(atoms);operator=rng.choice(['AND','OR'])
  queries.append(f'SELECT a.id,b.id FROM l a LEFT JOIN r b ON ({first}) {operator} ({second}) ORDER BY a.id,b.id LIMIT {rng.randrange(-1,8)} OFFSET {rng.randrange(-1,8)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-truth-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3];counts=[(3,4),(0,4),(3,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(0,12),rng.randrange(0,12))
   left_bool=',"true"' if fixture%3 else ''
   right_bool=(',"false"' if fixture%3==1 else ',"true"') if fixture%3 else ''
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,k{left_bool});CREATE TABLE r(id INTEGER PRIMARY KEY,k{right_bool});' 
   values=['NULL','0','0.0','1','1.0',"'1'","'01'","X'31'",'2','2.5',"'a'","'A'",'-9223372036854775808','9223372036854775807',"'1x'","'0.5suffix'","'  -2tail'","X'31FF'","X'00'","X'302E35FF'","CAST(X'3100FF' AS TEXT)","CAST(X'FF31' AS TEXT)",'1e-310','1e999','-1e999']
   if fixture==0:counts=(14,7)
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
