#!/usr/bin/env python3
"""SIGKILL timing samples for retained composite-table keys in both file modes."""
import argparse,hashlib,json,shutil,subprocess,tempfile,time
from pathlib import Path
from test_last_insert_rowid import SQLITE,BINARY,snapshot

def state(path):
 result=snapshot(path)
 for sql in ["PRAGMA index_list(t);","SELECT v,n FROM t ORDER BY v,n;","PRAGMA schema_version;"]:
  result.append(subprocess.check_output([SQLITE,str(path),sql]))
 return result

def sha(parts):
 h=hashlib.sha256()
 for part in parts:h.update(len(part).to_bytes(8,'little'));h.update(part)
 return h.hexdigest()

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path);a=p.parse_args();records=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-composite-table-crash-') as directory:
  folder=Path(directory);original=folder/'original.db';expected=folder/'expected.db'
  setup="CREATE TABLE t(id INTEGER,v TEXT,n INTEGER,PRIMARY KEY(id,v));WITH RECURSIVE c(i) AS(VALUES(1) UNION ALL SELECT i+1 FROM c WHERE i<200) INSERT INTO t SELECT i,printf('value %d',i),i-100 FROM c;CREATE INDEX retained ON t(n);"
  subprocess.run([SQLITE,str(original)],input=setup,text=True,capture_output=True,check=True)
  shutil.copyfile(original,expected)
  sql="BEGIN;UPDATE t SET n=100-n,v=v||'changed';COMMIT;"
  subprocess.run([SQLITE,str(expected)],input=sql,text=True,capture_output=True,check=True)
  before=state(original);after=state(expected)
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   for i,delay in enumerate([.001,.003,.007,.015,.025,.04,.06,.09,.13,.2,.35,.7]):
    path=folder/f'{suffix}-{i}.db';shutil.copyfile(original,path);started=time.monotonic()
    writer=subprocess.Popen([str(BINARY),mode,str(path)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    killed=False
    try:stdout,stderr=writer.communicate(sql,timeout=delay)
    except subprocess.TimeoutExpired:killed=True;writer.kill();stdout,stderr=writer.communicate()
    elapsed=time.monotonic()-started
    if not killed and writer.returncode:raise AssertionError(stderr)
    recovery=subprocess.run([str(BINARY),mode,str(path)],input='SELECT count(*) FROM t;',text=True,capture_output=True,timeout=30)
    if recovery.returncode:raise AssertionError(recovery.stderr)
    actual=state(path)
    if actual!=before and actual!=after:raise AssertionError(f'torn partial index transaction after {delay}s ({mode}): {actual!r}')
    records.append(dict(mode=mode,delay_seconds=delay,elapsed_seconds=elapsed,killed=killed,writer_returncode=writer.returncode,recovered='old' if actual==before else 'new',snapshot_sha256=sha(actual)))
 report=dict(scope='SIGKILL timing samples for a retained composite-table predicate, entered/left keys and an ordinary retained index. Production recovery followed by independent SQLite catalog SQL, partial flag, rows, indexed-key query, schema cookie and integrity checks. Not an every-syscall, power-loss, arbitrary-schedule or root-page-identity equivalence claim.',cases=len(records),failures=0,records=records)
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(records),failures=0,killed=sum(r['killed'] for r in records),old=sum(r['recovered']=='old' for r in records),new=sum(r['recovered']=='new' for r in records))))
if __name__=='__main__':main()
