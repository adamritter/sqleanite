#!/usr/bin/env python3
"""Exhaustive short-byte JSON diagnostic positions through public file APIs.

Every byte string of lengths zero through --width is stored by pinned C SQLite.
A single ordered read per mode evaluates error positions for the BLOB value
and its TEXT cast, plus the validity checks for each representation. Compare every result row, complete output/error status, file
immutability and C integrity. This exhaustive fixed domain is not fresh data.
"""
import argparse,hashlib,itertools,json,os,shutil,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--width',type=int,choices=[1,2],default=2);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 values=[bytes(v) for n in range(a.width+1) for v in itertools.product(range(256),repeat=n)]
 def run(cmd,sql):
  start=time.time();r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=600)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'),seconds=time.time()-start)
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):
  return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 fields=['id','json_error_position(v)','json_error_position(CAST(v AS TEXT))','json_valid(v,8)','json_valid(CAST(v AS TEXT),2)']
 sql='SELECT '+','.join(fields)+' FROM t ORDER BY id;';cases=[];runs=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-bytes-') as tmp:
  for page in [512,65536]:
   folder=Path(tmp)/str(page);folder.mkdir();base=folder/'base.db'
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v);BEGIN;'+''.join(f"INSERT INTO t VALUES({i},X'{v.hex()}');" for i,v in enumerate(values))+'COMMIT;'
   built=csql(base,setup);assert built['code']==0,built
   for mode in ['--verified-file','--verified-wal-file']:
    lean=folder/(mode+'-lean.db');reference=folder/(mode+'-c.db');shutil.copyfile(base,lean);shutil.copyfile(base,reference);bl,br=snapshot(lean),snapshot(reference)
    l=run([str(binary),mode,str(lean)],sql);c=csql(reference,sql)
    ll,cl=l['stdout'].splitlines(),c['stdout'].splitlines()
    assert len(cl)==len(values),c
    for i,wanted in enumerate(cl):
     actual=ll[i] if i<len(ll) else None
     cases.append(dict(page_size=page,mode=mode,input_hex=values[i].hex(),lean=actual,sqlite=wanted,matched=actual==wanted))
    li,ci=csql(lean,'PRAGMA integrity_check;'),csql(reference,'PRAGMA integrity_check;')
    runs.append(dict(page_size=page,mode=mode,sql=sql,lean=l,sqlite=c,lean_unchanged=bl==snapshot(lean),sqlite_unchanged=br==snapshot(reference),integrity_lean=li,integrity_sqlite=ci,
      matched=l['code']==c['code']==0 and l['stdout']==c['stdout'] and len(ll)==len(cl) and bl==snapshot(lean) and br==snapshot(reference) and li['stdout']==ci['stdout']=='ok\n'))
 assert source==digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 failures=sum(not c['matched'] for c in cases)+sum(not r['matched'] for r in runs)
 report=dict(width=a.width,comparison=__doc__.strip(),cases=cases,runs=runs,failures=failures,implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
