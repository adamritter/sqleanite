#!/usr/bin/env python3
"""First-commit SIGKILL samples from a zero-byte database (not power-loss proof)."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile
import time
from test_index_catalog_crash import BINARY,SQLITE,digest
from test_last_insert_rowid import snapshot

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',required=True,type=Path);a=p.parse_args();records=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-zero-crash-') as d:
  d=Path(d);original=d/'original.db';original.touch();expected=d/'expected.db';expected.touch()
  sql='BEGIN;CREATE TABLE t(id INTEGER PRIMARY KEY,v UNIQUE CHECK(v>0));INSERT INTO t VALUES'+','.join(f'({i},{i*3})' for i in range(1,201))+';COMMIT;'
  subprocess.run([SQLITE,str(expected)],input=sql,text=True,capture_output=True,check=True)
  before=snapshot(original);after=snapshot(expected)
  for initial in [b'',b'X']:
   for mode in ['--verified-file','--verified-wal-file']:
    for i,delay in enumerate([.001,.003,.007,.012,.02,.03,.05,.08,.12,.2,.35,.7]):
     path=d/f'{len(initial)}-{mode}-{i}.db';path.write_bytes(initial);start=time.monotonic()
     writer=subprocess.Popen([str(BINARY),mode,str(path)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
     killed=False
     try:stdout,stderr=writer.communicate(sql,timeout=delay)
     except subprocess.TimeoutExpired:
      killed=True;writer.kill();stdout,stderr=writer.communicate()
     if not killed and writer.returncode:raise AssertionError(stderr)
     elapsed=time.monotonic()-start
     recovery=subprocess.run([str(BINARY),mode,str(path)],input='SELECT count(*) FROM sqlite_schema;',text=True,capture_output=True,timeout=30)
     if recovery.returncode:raise AssertionError(recovery.stderr)
     actual=snapshot(path)
     if actual not in [before,after]:raise AssertionError(f'torn state: {mode} {delay}: {actual!r}')
     records.append({'mode':mode,'initial_bytes':len(initial),'delay_seconds':delay,'elapsed_seconds':elapsed,'killed':killed,'writer_returncode':writer.returncode,'recovered':'old' if actual==before else 'new','snapshot_sha256':digest(actual)})
 report={'scope':'First-commit SIGKILL timing sample on an existing zero-byte database. Production Lean recovery followed by independent SQLite catalog/row/integrity comparison. Not exhaustive syscall, power-loss or concurrent-open coverage.','cases':len(records),'failures':0,'old_snapshot_sha256':digest(before),'new_snapshot_sha256':digest(after),'records':records}
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'cases':len(records),'failures':0,'old':sum(r['recovered']=='old' for r in records),'new':sum(r['recovered']=='new' for r in records),'killed':sum(r['killed'] for r in records)}))
if __name__=='__main__':main()
