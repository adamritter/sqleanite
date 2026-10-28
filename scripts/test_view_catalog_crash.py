#!/usr/bin/env python3
"""VIEW + table/catalog transaction SIGKILL timing samples, both public file paths.
This samples process crashes; it does not claim syscall or power-loss coverage.
"""
import argparse,hashlib,json,shutil,subprocess,tempfile,time
from pathlib import Path
from test_last_insert_rowid import SQLITE,BINARY,snapshot

def state(path):
 result=snapshot(path)
 for sql in ["SELECT rowid,type,name,tbl_name,CASE WHEN type='view' THEN rootpage ELSE NULL END,sql FROM sqlite_schema ORDER BY rowid;",'PRAGMA schema_version;']:
  result.append(subprocess.check_output([SQLITE,str(path),sql]))
 names=subprocess.check_output([SQLITE,str(path),"SELECT hex(name) FROM sqlite_schema WHERE type='view' ORDER BY name;"],text=True)
 for raw in names.splitlines():
  name=bytes.fromhex(raw).decode();quoted='"'+name.replace('"','""')+'"'
  result.append(subprocess.check_output([SQLITE,str(path),'SELECT * FROM '+quoted+' ORDER BY id;']))
 return result

def sha(parts):
 h=hashlib.sha256()
 for part in parts:h.update(len(part).to_bytes(8,'little'));h.update(part)
 return h.hexdigest()

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path);a=p.parse_args();records=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-view-crash-') as folder:
  folder=Path(folder)
  for scenario in ['create','drop']:
   original=folder/(scenario+'-original.db');expected=folder/(scenario+'-expected.db')
   setup="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);WITH RECURSIVE c(i) AS(VALUES(1) UNION ALL SELECT i+1 FROM c WHERE i<200) INSERT INTO t SELECT i,printf('value %d',i),i FROM c;CREATE UNIQUE INDEX retained ON t(n);"
   if scenario=='drop':setup+='CREATE VIEW q AS SELECT id,v,n FROM t;'
   subprocess.run([SQLITE,str(original)],input=setup,text=True,capture_output=True,check=True)
   shutil.copyfile(original,expected)
   ddl='CREATE VIEW q AS SELECT id,v,n FROM t;' if scenario=='create' else 'DROP VIEW q;'
   sql="BEGIN;"+ddl+"UPDATE t SET n=n+10000,v=v||'changed';COMMIT;"
   subprocess.run([SQLITE,str(expected)],input=sql,text=True,capture_output=True,check=True)
   before=state(original);after=state(expected)
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
     if actual!=before and actual!=after:raise AssertionError(f'torn VIEW transaction after {delay}s ({scenario}, {mode}): {actual!r}')
     records.append(dict(scenario=scenario,mode=mode,delay_seconds=delay,elapsed_seconds=elapsed,killed=killed,writer_returncode=writer.returncode,recovered='old' if actual==before else 'new',snapshot_sha256=sha(actual)))
 report=dict(scope='SIGKILL timing samples for atomic VIEW create/drop plus base-row updates and a retained index, both public Core file modes; production Lean recovery followed by independent SQLite view/table/catalog rowid/schema-cookie/integrity checks. Does not establish every syscall boundary, power loss or concurrent-schedule coverage.',cases=len(records),failures=0,records=records)
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(records),failures=0,killed=sum(r['killed'] for r in records),old=sum(r['recovered']=='old' for r in records),new=sum(r['recovered']=='new' for r in records))))
if __name__=='__main__':main()
