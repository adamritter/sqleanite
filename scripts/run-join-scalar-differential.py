#!/usr/bin/env python3
"""Compare scalar expressions over two-source joins and source binding.

Fixed and newly seeded scalar projections, WHERE, aliases, DISTINCT, ordering
and windows. Dynamic ON and aggregates are explicit broader controls; retain
all mismatches, including partial output before an evaluation error. Full stdout/error status and immutable C images
with typed/integrity observations in both file modes.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354580);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 sources=[f'l a {kind} r b ON a.id=b.id' for kind in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']]
 sources += [f'l a {kind} r b USING(k)' for kind in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']]
 expressions=['a.k+1','a.k+b.k','a.k||b.k','coalesce(a.k,b.k)','ifnull(a.k,b.k)',
  'CASE WHEN a.k=b.k THEN a.k ELSE b.k END','typeof(a.k)','length(a.k)',
  'substr(a.k,1,2)','lower(a.k)','a.k IS b.k','a.k BETWEEN 0 AND 2',
  'a.k IN (b.k,1,NULL)','likely(a.k+1)','CAST(a.k AS TEXT)','CAST(a.k AS REAL)',
  'min(a.k,b.k)','max(a.k,b.k)','nullif(a.k,b.k)','iif(a.k,b.k,1)','abs(a.k)',
  'round(a.k,1)','k+1',"k='1'",'typeof(k)']
 conditions=['1','a.k+1>0',"typeof(b.k)='integer'",'coalesce(a.k,b.k) IS NOT NULL']
 queries=[]
 for source in sources:
  for expression in expressions:
   for condition in conditions:
    queries.append(f'SELECT {expression} AS chosen,a.id,b.id FROM {source} WHERE {condition} ORDER BY a.id,b.id;')
   queries.append(f'SELECT {expression} AS chosen,a.id,b.id FROM {source} ORDER BY chosen,a.id,b.id LIMIT 3 OFFSET 1;')
   queries.append(f'SELECT DISTINCT {expression} AS chosen FROM {source} ORDER BY chosen;')
   queries.append(f'SELECT {expression} AS chosen FROM {source} WHERE chosen IS NOT NULL ORDER BY a.id,b.id LIMIT 0;')
  for expression in ['not_a_function(a.k)','a.missing+1','a.k COLLATE missing',"min(a.k,b.k COLLATE missing)"]:
   queries.append(f'SELECT {expression} FROM {source} LIMIT 0;')
  for projection in ['count(*)','sum(a.k)','max(b.k)','a.k,count(*)']:
   group=' GROUP BY a.k' if ',' in projection else ''
   queries.append(f'SELECT {projection} FROM {source}{group} ORDER BY 1;')
 for kind in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']:
  for condition in ['a.k+1=b.k','coalesce(a.k,0)=b.k','abs(a.k)=b.k']:
   queries.append(f'SELECT a.id,b.id FROM l a {kind} r b ON {condition} ORDER BY a.id,b.id;')
 for _ in range(a.random_cases):
  source=rng.choice(sources);expression=rng.choice(expressions);condition=rng.choice(conditions)
  queries.append(f'SELECT {expression} AS chosen,a.id,b.id FROM {source} WHERE {condition} ORDER BY chosen,a.id,b.id LIMIT {rng.randrange(0,8)} OFFSET {rng.randrange(0,3)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-scalar-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3];counts=[(3,4),(0,4),(3,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(0,12),rng.randrange(0,12))
   left_bool=',"true"' if fixture%3 else ''
   right_bool=(',"false"' if fixture%3==1 else ',"true"') if fixture%3 else ''
   left_type=['TEXT','INTEGER','NUMERIC','BLOB','REAL',''][fixture%6];right_type=['NUMERIC','TEXT','BLOB','INTEGER','','REAL'][fixture%6]
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,k {left_type}{left_bool});CREATE TABLE r(id INTEGER PRIMARY KEY,k {right_type}{right_bool});' 
   values=['NULL','0','0.0','1','1.0',"'1'","'01'","X'31'",'2','2.5',"'a'","'A'","'a '","'A  '",'-9223372036854775808','9223372036854775807',"'1x'","'0.5suffix'","'  -2tail'","X'31FF'","X'00'","X'302E35FF'","CAST(X'3100FF' AS TEXT)","CAST(X'FF31' AS TEXT)",'1e-310','1e999','-1e999']
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
     matched=(bool(l['code'])==bool(r['code'])) and l['stdout']==r['stdout']
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=matched))
    observation='PRAGMA integrity_check;SELECT id,typeof(k),hex(k) FROM l ORDER BY id;SELECT id,typeof(k),hex(k) FROM r ORDER BY id;'
    lo=csql(left,observation);ro=csql(right,observation)
    fixtures.append(dict(fixture=fixture,page_size=page,mode=mode,setup=setup,lean_unchanged=before_l==snapshot(left),sqlite_unchanged=before_r==snapshot(right),observation_lean=lo,observation_sqlite=ro,matched=before_l==snapshot(left) and before_r==snapshot(right) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')))
 failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures)
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,fixtures=fixtures,failures=failures,implementation_sha256=digest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),fixtures=len(fixtures),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
