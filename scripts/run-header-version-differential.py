#!/usr/bin/env python3
"""Compare SQLite read/write version and schema-format admission.

Each write receives its own copied database. Error equivalence is positive
exit status only; successful results and persisted rows are compared exactly.
The pinned CLI is both fixture producer and independent post-write observer.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=353950);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];fixtures=[]
 binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def observe(path):return run([a.sqlite,'-batch','-bail',str(path)],'PRAGMA integrity_check;SELECT id,typeof(v),hex(v) FROM t ORDER BY id;')
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 configs=[(4096,1,1,4,'sqlite'),(512,0,0,4,'sqlite'),(65536,2,2,4,'sqlite')]
 configs += [(4096,w,r,f,origin) for origin in ['sqlite','lean'] for w,r,f in [(3,1,4),(255,1,4),(1,3,4),(1,255,4),(255,255,4),(1,1,0),(1,1,1),(1,1,2),(1,1,3),(1,1,5),(1,1,255),(1,1,256),(1,1,260),(1,1,261)]]
 for _ in range(a.random_cases):configs.append((rng.choice([512,1024,4096,65536]),rng.choice([0,1,2,3,127,255]),rng.choice([0,1,2,3,128,255]),rng.choice([0,1,2,3,4,5,255,256,257,260,261,2**32-1]),'sqlite'))
 with tempfile.TemporaryDirectory(prefix='sqleanite-header-version-') as tmp:
  for number,(page,write,read,schema,origin) in enumerate(configs):
   folder=Path(tmp)/str(number);folder.mkdir();base=folder/'base.db'
   values=[rng.randrange(-10000,10000) for _ in range(rng.randrange(3,12))]
   setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE INDEX tv ON t(v);'+''.join(f'INSERT INTO t VALUES({i+1},{v});' for i,v in enumerate(values))
   if origin=='sqlite':r=run([a.sqlite,'-batch','-bail',str(base)],f'PRAGMA page_size={page};'+setup)
   else:r=run([binary,'--verified-file',str(base)],setup)
   assert r['code']==0,r
   raw=bytearray(base.read_bytes());raw[18]=write;raw[19]=read;raw[44:48]=schema.to_bytes(4,'big');base.write_bytes(raw)
   fixtures.append(dict(page_size=page,write_version=write,read_version=read,schema_format=schema,origin=origin,rows=len(values)))
   for mode in ['--verified-file','--verified-wal-file']:
    for operation,sql in [('read','SELECT 1;'),('read','SELECT * FROM t ORDER BY id;'),('read','SELECT v FROM t WHERE id=1;'),('read','SELECT id FROM t ORDER BY v,id;'),('write','UPDATE t SET v=v+1 WHERE id=1;'),('write',"INSERT INTO t VALUES(1000,'new');"),('write','BEGIN;UPDATE t SET v=v+2 WHERE id=1;ROLLBACK;'),('write','UPDATE t SET v=0 WHERE 0;'),('write','CREATE TABLE IF NOT EXISTS t(id INTEGER PRIMARY KEY,v);')]:
     dest=folder/(mode+str(len(cases)));dest.mkdir();lean=dest/'lean.db';ref=dest/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail']+(['-readonly'] if operation=='read' else [])+[str(ref)],sql)
     matched=(l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']);after=hashes(lean)
     unchanged=before==after
     item=dict(fixture=number,mode=mode,operation=operation,sql=sql,lean=l,sqlite=r,matched=matched,bytes_unchanged=unchanged)
     if operation=='read' or l['code']!=0:item['matched'] &= unchanged
     if operation=='write' and l['code']==r['code']==0:
      lo=observe(lean);ro=observe(ref);item['observed_lean']=lo;item['observed_sqlite']=ro;item['matched'] &= lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     cases.append(item)
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,random_cases=a.random_cases,fixtures=fixtures,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
