#!/usr/bin/env python3
"""Compare rowid-range traversal and USING/NATURAL sort/error boundaries.

Fixed templates mix with newly seeded rows, rowid aliases, affinities and
LIMIT/OFFSET. Compare all stdout, including prefixes before errors, status,
immutable main/WAL bytes and independent C typed-row/integrity observations.
Keep all failures. Both public file modes run on C-created databases.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest(root):
 h=hashlib.sha256()
 for p in sorted((root/'SQLeanite').rglob('*.lean'))+[root/'Main.lean']:h.update(str(p.relative_to(root)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354740);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=24);p.add_argument('--implementation-root',type=Path,default=ROOT);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 root=a.implementation_root.resolve();sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=root/'.lake/build/bin/sqleanite';source=digest(root);exe=hashlib.sha256(binary.read_bytes()).hexdigest();cases=[];fixtures=[]
 def run(argv,sql):
  r=subprocess.run(argv,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 kinds=['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN','CROSS JOIN']
 sources=[f'l a {kind} r b {using}' for kind in kinds for using in ['USING(k)','USING($pk,k)']]
 sources += [f'l a NATURAL {kind} r b' for kind in kinds]
 tails=['',' ORDER BY a.$pk,b.$pk',' ORDER BY a.$pk',' ORDER BY b.$pk,a.$pk',' ORDER BY a.$pk DESC,b.$pk LIMIT 1',' ORDER BY a.$pk,b.$pk DESC LIMIT 3 OFFSET 1']
 projections=['abs(a.k),a.$pk,b.$pk','a.$pk,b.$pk','CASE WHEN a.k THEN abs(a.k) ELSE b.k END,a.$pk,b.$pk']
 queries=[f'SELECT {projection} FROM {source}{tail};' for source in sources for tail in tails for projection in projections]
 ons=['a.$pk BETWEEN b.$pk AND b.$pk+1 AND abs(a.k)','b.$pk BETWEEN abs(a.k) AND 3']
 wheres=['',' WHERE b.$pk BETWEEN 1 AND 2',' WHERE b.k IS NULL',' WHERE a.$pk NOT BETWEEN 1 AND 3']
 queries += [f'SELECT a.$pk,b.$pk FROM l a {kind} r b ON {on}{where}{tail};' for kind in kinds for on in ons for where in wheres for tail in tails]
 for _ in range(a.random_cases):
  joined=rng.choice(sources);projection=rng.choice(projections)
  queries.append(f'SELECT {projection} FROM {joined} ORDER BY a.$pk {rng.choice(["ASC","DESC"])},b.$pk {rng.choice(["ASC","DESC"])} LIMIT {rng.randrange(0,6)} OFFSET {rng.randrange(0,4)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-range-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=512<<(fixture%8);pk=['id','rowid','oid','_rowid_'][fixture%4]
   lt=['INTEGER','TEXT','REAL','BLOB','NUMERIC',''][fixture%6];rt=['INTEGER','NUMERIC','TEXT','REAL','','BLOB'][fixture%6]
   counts=[(4,4),(0,4),(4,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(2,9),rng.randrange(2,9))
   setup=f'PRAGMA page_size={page};CREATE TABLE l({pk} INTEGER PRIMARY KEY,k {lt});CREATE TABLE r({pk} INTEGER PRIMARY KEY,k {rt});'
   values=['NULL','0','1','2','-9223372036854775808',"'1'","'01'","'x'","X'31'"]
   for table,count in zip(['l','r'],counts):
    bad=rng.randrange(count) if count else -1
    for i in range(count):
     value='-9223372036854775808' if table=='l' and i==bad else rng.choice(values)
     key=i-1 if fixture>=4 else i+1
     setup+=f'INSERT INTO {table} VALUES({key},{value});'
   created=csql(base,setup);assert created['code']==0,created
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
    for template in queries:
     sql=template.replace('$pk',pk);l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);matched=bool(l['code'])==bool(c['code']) and l['stdout']==c['stdout']
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=c,matched=matched))
    observe=f'PRAGMA integrity_check;SELECT {pk},typeof(k),hex(k) FROM l ORDER BY {pk};SELECT {pk},typeof(k),hex(k) FROM r ORDER BY {pk};';lo,co=csql(left,observe),csql(right,observe)
    fixtures.append(dict(fixture=fixture,mode=mode,page_size=page,setup=setup,lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),observation_lean=lo,observation_sqlite=co,matched=bl==snapshot(left) and br==snapshot(right) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n')))
 assert source==digest(root) and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,fixtures=fixtures,failures=sum(not c['matched'] for c in cases)+sum(not f['matched'] for f in fixtures),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
