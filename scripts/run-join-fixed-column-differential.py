#!/usr/bin/env python3
"""Compare fixed-column affinity, singleton cursor plans and declared-null metadata.

Public executables run the same SELECTs on copies of pinned-C databases in
both file modes. Exact stdout, including partial rows before errors, and error
status are compared. All mismatches and file immutability checks are retained.
Seeds vary safe values and the overflowing row; fixed controls remain fixed.
Inputs include empty and nonempty sources, NOT NULL declarations, mixed stored
values, original/commuted comparisons and exact error stdout.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354660);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 conditions=['abs(a.k)=b.id AND b.id=1','b.id=1 AND abs(a.k)=b.id',
  'abs(a.k)=b.k AND b.k=1','b.k=1 AND abs(a.k)=b.k',
  "b.id='1' AND abs(a.k)=b.id","b.id=CAST('1' AS TEXT) AND abs(a.k)=b.id",
  'b.id=1 AND abs(a.k)>b.id','abs(a.k)>b.id AND b.id=1',
  'b.id=1 AND abs(a.k)<b.id','abs(a.k)<b.id AND b.id=1',
  'b.id=abs(-9223372036854775808) AND a.id=2',
  'a.id=2 AND b.id=abs(-9223372036854775808)',
  'b.id=a.id AND abs(a.k)=b.id','a.id=b.id AND b.id=abs(a.k)',
  'abs(a.k)=b.id AND b.id=a.id','a.id=2 AND b.id=a.id AND abs(a.k)=b.id',
  'b.k=1 AND abs(a.k)=+b.k','b.k=1 AND CAST(abs(a.k) AS TEXT)=b.k',
  'b.k=1 AND abs(a.k)=coalesce(b.k,1)',"b.k=CAST('1' AS TEXT) AND abs(a.k)=b.k"]
 queries=[]
 for kind in ['JOIN','CROSS JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']:
  for condition in conditions:
   for where in ['', ' WHERE a.id>1',' WHERE a.id=2',' WHERE a.id IS 2',' WHERE b.k IS NULL',' WHERE b.k IS NOT NULL',' WHERE a.k IS NOT NULL AND a.id>1',' WHERE b.id IS NOT NULL AND a.id>1',' WHERE 0']:
    for tail in ['',' ORDER BY a.id,b.id',' ORDER BY a.id DESC,b.id LIMIT 1']:
     queries.append(f'SELECT a.id,b.id FROM l a {kind} r b ON {condition}{where}{tail};')
 for _ in range(a.random_cases):
  kind=rng.choice(['JOIN','CROSS JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']);condition=rng.choice(conditions)
  where=rng.choice(['',' WHERE a.id>1',' WHERE a.id=2',' WHERE a.id IS 2',' WHERE a.id IN (2)',' WHERE a.id IS NOT NULL',' WHERE b.k IS NULL',' WHERE b.k IS NOT NULL',' WHERE a.k IS NOT NULL AND a.id>1',' WHERE b.id IS NOT NULL AND a.id>1',' WHERE 0'])
  direction=rng.choice(['ASC','DESC'])
  queries.append(f'SELECT a.id,b.id FROM l a {kind} r b ON {condition}{where} ORDER BY a.id {direction},b.id LIMIT {rng.randrange(0,4)} OFFSET {rng.randrange(0,3)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-fixed-column-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3]
   typ=['TEXT','INTEGER','NUMERIC','BLOB','REAL',''][fixture%6]
   left_not_null=' NOT NULL' if fixture%3!=0 else ''
   right_not_null=' NOT NULL' if fixture%2==0 else ''
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,k INTEGER{left_not_null});CREATE TABLE r(id INTEGER PRIMARY KEY,k {typ}{right_not_null});'
   # Fixed presence patterns cover empty sources and nonempty TEXT/BLOB/REAL
   # storage without selecting cases according to the reference's result.
   if fixture%8 in [1,2,3,4,6]:
    for i in range(1,4):
     value=rng.choice(['1','1.0',"'01'","'1.0'","'A'",'2','3'])
     setup+=f'INSERT INTO r VALUES({i},{value});'
   if fixture%8 not in [2,7]:
    bad=1 if fixture<4 else rng.randrange(1,5)
    for i in range(1,5):
     value=-9223372036854775808 if i==bad else rng.randrange(-5,6)
     setup+=f'INSERT INTO l VALUES({i},{value});'
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
