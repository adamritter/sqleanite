#!/usr/bin/env python3
"""Compare stored-column affinity in two-table join comparisons.

All ordered pairs of six declared type forms, both operand orders, six comparison
operators, INNER/LEFT and post-join WHERE. Exact successful CLI bytes and error
status; C-created images, typed independent observations and immutable main/WAL
bytes. Every mismatch is retained. Arbitrary scalar join expressions, explicit
collations, USING and RIGHT/FULL are separate work.
"""
import argparse,hashlib,itertools,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354360);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';cases=[];fixtures=[]
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 values=['NULL','0','1','1.0',"'1'","'01'","' 2 '","'2x'",'1.5',"'1.5'","''","X'31'",'-9223372036854775808','9223372036854775807','9223372036854775808.0',"'9223372036854775807'", "CAST(X'310078' AS TEXT)"]
 queries=[]
 for op in ['=','<>','<','<=','>','>=']:
  for left,right in [('a.k','b.k'),('b.k','a.k')]:
   condition=f'{left}{op}{right}'
   for join in ['JOIN','LEFT JOIN']:
    queries.append(f'SELECT a.id,b.id,a.k,b.k FROM l AS a {join} r AS b ON {condition} ORDER BY a.id,b.id;')
   queries.append(f'SELECT a.id,b.id,a.k,b.k FROM l AS a JOIN r AS b ON a.id=b.id WHERE {condition} ORDER BY a.id,b.id;')
 for op in ['=','<>','<','<=','>','>=']:
  queries.append(f'SELECT a.id,b.id FROM l AS a LEFT JOIN e AS b ON a.k{op}b.k ORDER BY a.id,b.id;')
  queries.append(f'SELECT a.id,b.id FROM l AS a LEFT JOIN e AS b ON a.id=b.id WHERE a.k{op}b.k ORDER BY a.id,b.id;')
 for _ in range(a.random_cases):
  op=rng.choice(['=','<>','<','<=','>','>=']);bound=rng.choice(values)
  queries.append(f'SELECT a.id,b.id FROM l AS a LEFT JOIN r AS b ON a.k{op}b.k WHERE a.k{rng.choice(["=","<",">"])}{bound} ORDER BY a.id,b.id LIMIT {rng.randrange(0,30)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-affinity-') as tmp:
  for fixture,(lt,rt) in enumerate(itertools.product(['INTEGER','NUMERIC','REAL','TEXT','BLOB',''],repeat=2)):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=[512,4096,65536][fixture%3]
   setup=f'PRAGMA page_size={page};CREATE TABLE l(id INTEGER PRIMARY KEY,k {lt});CREATE TABLE r(id INTEGER PRIMARY KEY,k {rt});CREATE TABLE e(id INTEGER PRIMARY KEY,k {rt});'
   for table in ['l','r']:
    inputs=values+[rng.choice(values) for _ in range(4)]
    n=rng.randrange(-100000,100001);m=rng.randrange(-100000,100001);exponent=rng.randrange(-4,5)
    inputs += [str(n), f"'{m}.0'", f"'{n}e{exponent}'"]
    rng.shuffle(inputs)
    setup+=f'INSERT INTO {table} VALUES'+','.join(f'({i},{v})' for i,v in enumerate(inputs,1))+';'
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);before_l=snapshot(left);before_r=snapshot(right)
    for sql in queries:
     l=run([str(binary),mode,str(left)],sql);r=csql(right,sql)
     matched=(l['code']==r['code']==0 and l['stdout']==r['stdout']) or(l['code']>0 and r['code']>0)
     if matched:
      for capture in [l,r]:
       if len(capture['stdout'])>4096:
        raw=capture.pop('stdout').encode('latin1');capture.update(stdout_bytes=len(raw),stdout_sha256=hashlib.sha256(raw).hexdigest())
     cases.append(dict(fixture=fixture,page_size=page,left_type=lt,right_type=rt,mode=mode,sql=sql,lean=l,sqlite=r,matched=matched))
    observation='PRAGMA integrity_check;SELECT id,typeof(k),hex(k) FROM l ORDER BY id;SELECT id,typeof(k),hex(k) FROM r ORDER BY id;'
    lo=csql(left,observation);ro=csql(right,observation)
    fixtures.append(dict(fixture=fixture,page_size=page,left_type=lt,right_type=rt,mode=mode,setup=setup,lean_unchanged=before_l==snapshot(left),sqlite_unchanged=before_r==snapshot(right),observation_lean=lo,observation_sqlite=ro,matched=before_l==snapshot(left) and before_r==snapshot(right) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')))
 failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures)
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,fixtures=fixtures,failures=failures,implementation_sha256=digest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),fixtures=len(fixtures),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
