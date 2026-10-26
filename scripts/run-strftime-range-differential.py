#!/usr/bin/env python3
"""Batched public strftime range comparison based on SQLite test/date4.test.

This reconstructs its deterministic timestamp range and Linux format set;
the oracle is the pinned SQLite binary rather than libc or Tcl assertions.
Both file modes compare every emitted row and the unchanged stored catalog.
"""
import argparse,gzip,hashlib,importlib.util,json,os,shutil,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('helpers',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--start',type=int,default=0);p.add_argument('--count',type=int,default=24859);p.add_argument('--stride',type=int,default=86390);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert a.count>0
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(command,sql):
  begin=time.time()
  try:
   r=subprocess.run(command,input=sql.encode(),capture_output=True,timeout=180);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'),seconds=time.time()-begin)
  except subprocess.TimeoutExpired as r:return dict(code=124,stdout=(r.stdout or b'').decode('latin1'),stderr=(r.stderr or b'').decode('latin1'),seconds=time.time()-begin,timed_out=True)
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 assert csql(':memory:','SELECT sqlite_version();')['stdout']=='3.53.4\n'
 fmt='%d,%e,%F,%H,%k,%I,%l,%j,%m,%M,%u,%w,%W,%Y,%%,%P,%p,%U,%V,%G,%g'
 sql='\n'.join("SELECT "+str(i)+",strftime('"+fmt+"',"+str(a.start+i*a.stride)+",'unixepoch');" for i in range(a.count))
 cases=[];runs=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-strftime-range-') as tmp:
  folder=Path(tmp);base=folder/'base.db';assert csql(base,'CREATE TABLE t(id INTEGER PRIMARY KEY);')['code']==0
  reference=csql(base,sql);assert reference['code']==0,reference['stderr'];expected=reference['stdout'].splitlines();assert len(expected)==a.count
  observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;';observation=csql(base,observe)
  for mode in ['--verified-file','--verified-wal-file']:
   db=folder/(mode+'.db');shutil.copyfile(base,db);result=run([str(binary),mode,str(db)],sql);actual=result['stdout'].splitlines();stored=csql(db,observe)
   storage_ok={k:stored[k] for k in ('code','stdout','stderr')}=={k:observation[k] for k in ('code','stdout','stderr')}
   valid=result['code']==0 and len(actual)==a.count and storage_ok
   cases.extend(dict(mode=mode,input=i,timestamp=a.start+i*a.stride,lean=actual[i] if i<len(actual) else None,sqlite=expected[i],matched=valid and i<len(actual) and actual[i]==expected[i]) for i in range(a.count))
   runs.append(dict(mode=mode,code=result['code'],seconds=result['seconds'],stderr=result['stderr'],output_rows=len(actual),stdout_sha256=hashlib.sha256(result['stdout'].encode('latin1')).hexdigest(),storage_equal=storage_ok,observation=stored))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 report=dict(comparison=__doc__.strip(),start=a.start,stride=a.stride,inputs=a.count,format=fmt,sql_sha256=hashlib.sha256(sql.encode()).hexdigest(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),runs=runs,cases=cases,failures=sum(not c['matched'] for c in cases))
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'],runs=[{k:v for k,v in r.items() if k not in ('observation','stderr')} for r in runs])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
