#!/usr/bin/env python3
"""Process-kill recovery sample for retained catalogs (not syscall-stage coverage)."""
import argparse,hashlib,json,os,shutil,subprocess,tempfile,time
from pathlib import Path
from test_last_insert_rowid import snapshot
ROOT=Path(__file__).resolve().parents[1]
BINARY=ROOT/'.lake/build/bin/sqleanite'
SQLITE=os.environ.get('SQLITE3_BIN','sqlite3')
def digest(parts):
 h=hashlib.sha256()
 for part in parts:h.update(len(part).to_bytes(8,'little'));h.update(part)
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();records=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-catalog-crash-') as directory:
  directory=Path(directory);original=directory/'original.db';expected=directory/'expected.db'
  setup="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);WITH RECURSIVE c(i) AS(VALUES(1) UNION ALL SELECT i+1 FROM c WHERE i<200) INSERT INTO t SELECT i,printf('value %d',i),i FROM c;CREATE UNIQUE INDEX \"original index\" ON t (n);"
  subprocess.run([SQLITE,str(original)],input=setup,text=True,capture_output=True,check=True)
  shutil.copyfile(original,expected)
  sql="UPDATE t SET n=n+10000,v=v||'changed';"
  subprocess.run([SQLITE,str(expected)],input=sql,text=True,capture_output=True,check=True)
  before=snapshot(original);after=snapshot(expected)
  for i,delay in enumerate([.001,.003,.007,.015,.025,.04,.06,.09,.13,.2,.35,.7]):
   path=directory/f'run-{i}.db';shutil.copyfile(original,path);started=time.monotonic()
   writer=subprocess.Popen([str(BINARY),'--verified-file',str(path)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
   killed=False
   try:stdout,stderr=writer.communicate(sql,timeout=delay)
   except subprocess.TimeoutExpired:
    killed=True;writer.kill();stdout,stderr=writer.communicate()
   elapsed=time.monotonic()-started
   if not killed and writer.returncode:raise AssertionError(stderr)
   recovery=subprocess.run([str(BINARY),'--verified-file',str(path)],input='SELECT count(*) FROM t;',text=True,capture_output=True,timeout=30)
   if recovery.returncode:raise AssertionError(recovery.stderr)
   actual=snapshot(path)
   if actual!=before and actual!=after:raise AssertionError(f'torn state after {delay}s: {actual!r}')
   records.append({'delay_seconds':delay,'elapsed_seconds':elapsed,'killed':killed,'writer_returncode':writer.returncode,'recovered':'old' if actual==before else 'new','snapshot_sha256':digest(actual)})
 report={'scope':'SIGKILL timing sample followed by production Lean recovery and independent SQLite catalog/rows/integrity checks; does not establish coverage of every syscall boundary or power-loss behavior.','cases':len(records),'failures':0,'old_snapshot_sha256':digest(before),'new_snapshot_sha256':digest(after),'records':records}
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'cases':len(records),'failures':0,'old':sum(r['recovered']=='old' for r in records),'new':sum(r['recovered']=='new' for r in records),'killed':sum(r['killed'] for r in records)}))
if __name__=='__main__':main()
