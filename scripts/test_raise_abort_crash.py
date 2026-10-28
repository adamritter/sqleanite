#!/usr/bin/env python3
"""SIGKILL samples of an aborting statement: no pending body write may publish."""
import argparse,json,shutil,subprocess,tempfile,time
from pathlib import Path
from test_trigger_catalog_crash import SQLITE,BINARY,state,sha

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path);a=p.parse_args();records=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-raise-abort-crash-') as folder:
  folder=Path(folder);original=folder/'original.db';reference=folder/'reference.db'
  setup="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);WITH RECURSIVE c(i) AS(VALUES(1) UNION ALL SELECT i+1 FROM c WHERE i<64) INSERT INTO t SELECT i,printf('value %d',i),i FROM c;CREATE UNIQUE INDEX retained ON t(n);CREATE TABLE log(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES(new.id,old.v||'/'||new.v,new.n);SELECT CASE WHEN new.id=64 THEN RAISE(ABORT,'stop last') ELSE 0 END;END;"
  subprocess.run([SQLITE,str(original)],input=setup,text=True,capture_output=True,check=True)
  shutil.copyfile(original,reference);before=state(original)
  mutation="UPDATE t SET v=v||'changed',n=n+10000;"
  native=subprocess.run([SQLITE,str(reference)],input=mutation,text=True,capture_output=True)
  if native.returncode!=1 or 'stop last' not in native.stderr:raise AssertionError(native)
  if state(reference)!=before:raise AssertionError('reference ABORT published a pending write')
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   for i,delay in enumerate([.001,.003,.007,.015,.025,.04,.06,.09,.13,.2,.35,.7]):
    path=folder/f'{suffix}-{i}.db';shutil.copyfile(original,path);started=time.monotonic()
    writer=subprocess.Popen([str(BINARY),mode,str(path)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    killed=False
    try:stdout,stderr=writer.communicate(mutation,timeout=delay)
    except subprocess.TimeoutExpired:killed=True;writer.kill();stdout,stderr=writer.communicate()
    if not killed and (writer.returncode!=1 or stdout or stderr.strip()!='Error: stop last'):raise AssertionError((writer.returncode,stdout,stderr))
    elapsed=time.monotonic()-started
    recovery=subprocess.run([str(BINARY),mode,str(path)],input='SELECT count(*) FROM t;',text=True,capture_output=True,timeout=30)
    if recovery.returncode:raise AssertionError(recovery.stderr)
    actual=state(path)
    if actual!=before:raise AssertionError(f'ABORT published an intermediate write after {delay}s ({mode})')
    records.append(dict(mode=mode,delay_seconds=delay,elapsed_seconds=elapsed,killed=killed,writer_returncode=writer.returncode,recovered='old',snapshot_sha256=sha(actual)))
 report=dict(scope='SIGKILL timing samples during a multi-table BEFORE UPDATE that raises ABORT on the final source row after pending body writes. Native reference failure and complete old-state persistence are required. Public Lean recovery precedes independent SQLite catalog/row/integrity checks. This failure-closing protocol does not evaluate post-error connection counters or every syscall/power-loss outcome.',cases=len(records),failures=0,records=records)
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(records),failures=0,killed=sum(r['killed'] for r in records),old=len(records))))
if __name__=='__main__':main()
