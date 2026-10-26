#!/usr/bin/env python3
"""Compare BETWEEN expression evaluation, affinity and joined cursor constraints.

Public executables run the same SELECTs on copies of pinned-C databases in
both file modes. Exact stdout, including partial rows before errors, and error
status are compared. All mismatches and file immutability checks are retained.
Seeds vary safe values and the overflowing row; fixed controls remain fixed.
Inputs include actual NULLs in nullable columns, empty and nonempty sources, NOT NULL declarations, mixed stored
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
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354680);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 conditions=['b.k=1 AND abs(a.k) BETWEEN b.k AND 3',
  'b.k=1 AND b.k BETWEEN abs(a.k) AND 3',
  'b.k=1 AND abs(a.k) NOT BETWEEN b.k AND 3',
  'b.k=1 AND b.k NOT BETWEEN abs(a.k) AND 3',
  'abs(a.k) BETWEEN b.id AND b.id+2','b.id BETWEEN abs(a.k) AND 3',
  'a.id BETWEEN b.id AND b.id+1 AND abs(a.k)',
  'b.id BETWEEN a.id AND a.id+1 AND abs(a.k)',
  'b.id BETWEEN 1 AND 2 AND abs(a.k)',
  'b.id NOT BETWEEN 1 AND 2 AND abs(a.k)',
  'a.k BETWEEN b.k AND 3','b.k BETWEEN a.k AND 3']
 # Include branch-sensitive upper bounds and NULL-tested values on actual
 # candidate pairs, with scalar wrappers as separate syntax controls.
 for branch in ['a.k BETWEEN 1 AND abs(-9223372036854775808)',
  'a.k NOT BETWEEN 1 AND abs(-9223372036854775808)',
  'b.k BETWEEN 1 AND abs(-9223372036854775808)',
  'b.k NOT BETWEEN 1 AND abs(-9223372036854775808)',
  'NULL BETWEEN NULL AND abs(a.k)', 'NULL NOT BETWEEN NULL AND abs(a.k)']:
  conditions.extend([branch, f'({branch}) COLLATE binary', f'likely({branch})'])
 wheres=['', ' WHERE a.id=2',' WHERE b.k IS NULL',' WHERE b.k IS NOT NULL',
  ' WHERE a.k BETWEEN 1 AND 3',' WHERE b.id BETWEEN 1 AND 2',
  ' WHERE a.id NOT BETWEEN 1 AND 3',' WHERE 0']
 queries=[]
 for kind,condition,where,tail in itertools.product(['JOIN','CROSS JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN'],conditions,wheres,['',' ORDER BY a.id,b.id',' ORDER BY a.id DESC,b.id LIMIT 1']):
  queries.append(f'SELECT a.id,b.id FROM l a {kind} r b ON {condition}{where}{tail};')
 for argument,lower,upper,negated in itertools.product(['NULL','0','2',"'2'",'a.k'],['NULL','1',"'1'"],['NULL','3','abs(-9223372036854775808)'],['','NOT ']):
  expression=f'{argument} {negated}BETWEEN {lower} AND {upper}'
  source=' FROM l a' if 'a.k' in expression else ''
  for sql in [f'SELECT {expression}{source};',f'SELECT 1{source} WHERE {expression};',f'SELECT CASE WHEN {expression} THEN 7 ELSE 9 END{source};']:
   queries.append(sql)
 for expression in ['2 NOT BETWEEN 1 AND 3=-3',"'2' BETWEEN 2 AND 1 IS NOT -3",'0 AND missing BETWEEN 1 AND 2','2 BETWEEN 1 COLLATE missing AND 3','__sqlean_between(2,1,3)','__SQLEAN_BETWEEN(2,1,3)']:
  queries.append(f'SELECT {expression};')
 for _ in range(a.random_cases):
  kind=rng.choice(['JOIN','CROSS JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']);condition=rng.choice(conditions);where=rng.choice(wheres)
  queries.append(f'SELECT a.id,b.id FROM l a {kind} r b ON {condition}{where} ORDER BY a.id {rng.choice(["ASC","DESC"])},b.id LIMIT {rng.randrange(0,4)} OFFSET {rng.randrange(0,3)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-between-') as tmp:
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
     value=rng.choice(['1','1.0',"'01'","'1.0'","'A'",'2','3']+(['NULL'] if not right_not_null else []))
     setup+=f'INSERT INTO r VALUES({i},{value});'
   if fixture%8 not in [2,7]:
    bad=1 if fixture<4 else rng.randrange(1,5)
    for i in range(1,5):
     value=-9223372036854775808 if i==bad else ('NULL' if not left_not_null and rng.randrange(4)==0 else rng.randrange(-5,6))
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
