#!/usr/bin/env python3
"""Fresh identical-UPDATE publication controls, including changed indexed keys.

Compare complete stdout/status/error, independent C typed rows/integrity, and
whether both main/WAL byte sets stay unchanged. An unchanged row image does not
justify skipping indexed-column or rowid writes. Both public modes/eight page
sizes are exercised by the full fixture matrix; all cases are retained.
"""
import argparse,hashlib,json,os,random,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354805);p.add_argument('--fixtures',type=int,default=8);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest();cases=[];fixtures=[]
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=60);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snap(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 def err(r):return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',r['stderr'].splitlines()[0]) if r['code'] and r['stderr'] else ''
 affinities=['','TEXT','INTEGER','NUMERIC','REAL'];rng.shuffle(affinities)
 with tempfile.TemporaryDirectory(prefix='sqleanite-update-noop-') as tmp:
  for fixture in range(a.fixtures):
   page=512<<(fixture%8);decl=affinities[fixture%len(affinities)]
   vals=['NULL',str(rng.randrange(-10000,10000)),str(rng.random()*1000),"'"+str(rng.randrange(10**9))+"'","X'"+bytes(rng.randrange(256) for _ in range(5)).hex()+"'"]
   for ix,index in enumerate(['','CREATE INDEX ix ON t(v);','CREATE UNIQUE INDEX ix ON t(v);','CREATE INDEX ix ON t(w);']):
    folder=Path(tmp)/f'{fixture}-{ix}';folder.mkdir();base=folder/'base.db'
    setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v {decl},w);'+''.join(f'INSERT INTO t VALUES({i+1},{v},{rng.randrange(10000)});' for i,v in enumerate(vals))+index
    made=csql(base,setup);assert made['code']==0,made;fixtures.append(dict(fixture=fixture,index=ix,page_size=page,setup=setup))
    sqls=['UPDATE t SET v=v;','UPDATE t SET v=NULL WHERE id=1;','UPDATE t SET w=w;','UPDATE t SET id=id;','UPDATE t SET rowid=rowid;','UPDATE t SET v=v RETURNING id;','UPDATE t SET v=v WHERE 0;','UPDATE t SET v=v,w=w;',"UPDATE t SET v=CASE WHEN id=1 THEN json_type(NULL) ELSE v END;",'UPDATE t SET v=v WHERE id BETWEEN 2 AND 4;', 'UPDATE t SET v=v WHERE id=99999;', 'UPDATE t SET w=w+1 WHERE id=2;']
    for mode in ['--verified-file','--verified-wal-file']:
     for i,sql in enumerate(sqls):
      case=folder/(mode+str(i));case.mkdir();left=case/'lean.db';right=case/'c.db';shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snap(left),snap(right)
      l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);al,ar=snap(left),snap(right)
      obs='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(w),hex(w) FROM t ORDER BY id;';lo,co=csql(left,obs),csql(right,obs)
      same=bool(l['code'])==bool(c['code']) and l['stdout']==c['stdout'] and err(l)==err(c) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and (bl==al)==(br==ar)
      cases.append(dict(fixture=fixture,index=ix,page_size=page,mode=mode,sql=sql,lean=l,sqlite=c,lean_error=err(l),sqlite_error=err(c),observation_lean=lo,observation_sqlite=co,lean_unchanged=bl==al,sqlite_unchanged=br==ar,matched=same))
 assert source==digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 failures=sum(not c['matched'] for c in cases);a.output.write_text(json.dumps(dict(seed=a.seed,cases=cases,fixtures=fixtures,failures=failures,implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip()),indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
