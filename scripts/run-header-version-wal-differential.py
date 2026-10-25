#!/usr/bin/env python3
"""Frozen WAL header-version cases, including base/page-one disagreement.

The producer closes before testing; WAL checksums are recomputed after deliberate
header changes. These comparisons do not test simultaneous process locking.
"""
import argparse,hashlib,json,os,random,struct,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def checksum(data,state,order):
 words=struct.unpack(order+'I'*(len(data)//4),data);a,b=state
 for x,y in zip(words[::2],words[1::2]):a=(a+x+b)&0xffffffff;b=(b+y+a)&0xffffffff
 return a,b
def rechecksum(data):
 order='<' if data[3]==0x82 else '>';page=struct.unpack_from('>I',data,8)[0];state=checksum(data[:24],(0,0),order);struct.pack_into('>II',data,24,*state)
 for offset in range(32,len(data),page+24):
  state=checksum(data[offset:offset+8]+data[offset+24:offset+24+page],state,order);struct.pack_into('>II',data,offset+16,*state)
 return data
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=353951);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];fixtures=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 def observe(path):return run([a.sqlite,'-batch','-bail',str(path)],'PRAGMA integrity_check;SELECT id,typeof(v),hex(v) FROM t ORDER BY id;')
 configs=[('control',None,None),('base-read',('base',19,1,3),None),('base-write',('base',18,1,3),None),('overlay-read',('wal',19,1,3),None),('overlay-write',('wal',18,1,3),None),('base-schema',('base',44,4,5),None),('overlay-schema',('wal',44,4,5),None),('wrapped-overlay-schema',('wal',44,4,260),None),('base-write-overlay-zero',('base',18,1,255),('wal',18,1,0)),('base-read-overlay-zero',('base',19,1,255),('wal',19,1,0))]
 with tempfile.TemporaryDirectory(prefix='sqleanite-header-wal-') as tmp:
  for sample in range(a.fixtures):
   for page in [512,4096,65536]:
    folder=Path(tmp)/f'{sample}-{page}';folder.mkdir();base=folder/'base.db'
    setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE INDEX tv ON t(v);BEGIN;'+''.join(f'INSERT INTO t VALUES({i},{rng.randrange(-10000,10000)});' for i in range(1,12))+'COMMIT;'
    r=run([a.sqlite,'-batch','-bail',str(base)],setup);assert r['code']==0,r
    r=run([a.sqlite,'-batch','-bail',str(base)],'PRAGMA journal_mode=WAL;\n.dbconfig no_ckpt_on_close on\nPRAGMA wal_autocheckpoint=0;BEGIN;UPDATE t SET v=v+1 WHERE id=1;PRAGMA user_version=77;COMMIT;');assert r['code']==0,r
    main=base.read_bytes();wal=Path(str(base)+'-wal').read_bytes();pageones=[off+24 for off in range(32,len(wal),page+24) if struct.unpack_from('>I',wal,off)[0]==1];assert pageones
    for label,first,second in configs:
     m=bytearray(main);w=bytearray(wal)
     for change in [first,second]:
      if change is None:continue
      target,off,size,value=change;data=m if target=='base' else w;start=off if target=='base' else pageones[-1]+off;data[start:start+size]=value.to_bytes(size,'big')
     rechecksum(w);fi=len(fixtures);fixtures.append(dict(sample=sample,page_size=page,variant=label,wal_frames=(len(w)-32)//(page+24)))
     for operation,sql in [('read','SELECT * FROM t ORDER BY id;'),('read','SELECT v FROM t WHERE id=1;'),('write','UPDATE t SET v=v+3 WHERE id=1;'),('write','BEGIN;INSERT INTO t VALUES(1000,7);ROLLBACK;'),('write','CREATE TABLE IF NOT EXISTS t(id INTEGER PRIMARY KEY,v);')]:
      dest=folder/(label+str(len(cases)));dest.mkdir();lean=dest/'lean.db';ref=dest/'sqlite.db'
      for path in [lean,ref]:path.write_bytes(m);Path(str(path)+'-wal').write_bytes(w)
      before=hashes(lean);l=run([binary,'--verified-wal-file',str(lean)],sql);r=run([a.sqlite,'-batch','-bail']+(['-readonly'] if operation=='read' else [])+[str(ref)],sql);same=(l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']);unchanged=before==hashes(lean)
      item=dict(fixture=fi,operation=operation,sql=sql,lean=l,sqlite=r,matched=same,bytes_unchanged=unchanged)
      if operation=='read' or l['code']!=0:item['matched'] &= unchanged
      if operation=='write' and l['code']==r['code']==0:
       lo=observe(lean);ro=observe(ref);item.update(observed_lean=lo,observed_sqlite=ro);item['matched'] &= lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
      cases.append(item)
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=fixtures,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
