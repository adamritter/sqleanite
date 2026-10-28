#!/usr/bin/env python3
"""SIGKILL timing samples for recursive REPLACE programs and three-table body writes.
These samples check process recovery, not every syscall or power-loss outcome.
"""
import argparse,json,shutil,subprocess,tempfile,time
from pathlib import Path
from test_trigger_catalog_crash import SQLITE,BINARY,state,sha

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path);a=p.parse_args();records=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-recursive-replace-crash-') as folder:
  folder=Path(folder)
  original=folder/'original.db';expected=folder/'expected.db'
  setup="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);CREATE UNIQUE INDEX retained ON t(v);WITH RECURSIVE c(i) AS(VALUES(1) UNION ALL SELECT i+1 FROM c WHERE i<64) INSERT INTO t SELECT i,printf('value %d',i),0 FROM c;CREATE TABLE log(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);CREATE TABLE detail(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);CREATE TRIGGER d AFTER DELETE ON t BEGIN INSERT INTO detail VALUES(old.id*10+old.n,old.v,old.n);END;CREATE TRIGGER a AFTER INSERT ON t WHEN new.n<3 BEGIN INSERT INTO log VALUES(new.id*10+new.n,new.v,new.n);INSERT OR REPLACE INTO t VALUES(new.id,new.v,new.n+1);END;"
  subprocess.run([SQLITE,str(original)],input=setup,text=True,capture_output=True,check=True)
  shutil.copyfile(original,expected)
  mutation="PRAGMA recursive_triggers=ON;INSERT OR REPLACE INTO t VALUES"+','.join(f"({i},'value {i} changed',1)" for i in range(1,65))+';'
  subprocess.run([SQLITE,str(expected)],input=mutation,text=True,capture_output=True,check=True)
  before=state(original);after=state(expected)
  for scenario,sql in [('autocommit',mutation)]:
   for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
    for i,delay in enumerate([.001,.003,.007,.015,.025,.04,.06,.09,.13,.2,.35,.7]):
     path=folder/f'{scenario}-{suffix}-{i}.db';shutil.copyfile(original,path);started=time.monotonic()
     writer=subprocess.Popen([str(BINARY),mode,str(path)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
     killed=False
     try:stdout,stderr=writer.communicate(sql,timeout=delay)
     except subprocess.TimeoutExpired:killed=True;writer.kill();stdout,stderr=writer.communicate()
     elapsed=time.monotonic()-started
     if not killed and writer.returncode:raise AssertionError(stderr)
     recovery=subprocess.run([str(BINARY),mode,str(path)],input='SELECT count(*) FROM t;',text=True,capture_output=True,timeout=30)
     if recovery.returncode:raise AssertionError(recovery.stderr)
     actual=state(path)
     if actual!=before and actual!=after:raise AssertionError(f'torn triggered write after {delay}s ({scenario}, {mode}): {actual!r}')
     records.append(dict(scenario=scenario,mode=mode,delay_seconds=delay,elapsed_seconds=elapsed,killed=killed,writer_returncode=writer.returncode,recovered='old' if actual==before else 'new',snapshot_sha256=sha(actual)))
 report=dict(scope='SIGKILL timing samples for recursive REPLACE INSERT/DELETE programs writing three tables, real OLD/NEW inputs, a live recursion flag and a unique index. Public Lean recovery followed by independent SQLite catalog/root-zero/rowid/schema-cookie/row/integrity checks. Complete old or new states are required. No every-syscall, power-loss or arbitrary-schedule claim.',cases=len(records),failures=0,records=records)
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(records),failures=0,killed=sum(r['killed'] for r in records),old=sum(r['recovered']=='old' for r in records),new=sum(r['recovered']=='new' for r in records))))
if __name__=='__main__':main()
