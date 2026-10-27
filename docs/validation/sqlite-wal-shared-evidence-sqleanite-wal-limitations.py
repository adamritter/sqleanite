"""Fresh negative controls: unsupported live WAL page-size conversion.

These are compatibility failures, even though rejecting without mutation is
safer than replacing files that an existing SQLite connection is using.
"""
import hashlib, importlib.util, json, os, pathlib, subprocess, tempfile

root=pathlib.Path('/dev/shm/sqleanite-catalog-20261026')
spec=importlib.util.spec_from_file_location('live',root/'scripts/run-wal-live-differential.py')
live=importlib.util.module_from_spec(spec);spec.loader.exec_module(live)
results=[]
with tempfile.TemporaryDirectory(prefix='sqleanite-wal-limitations-') as tmp:
 for size in [512,65536]:
  db=pathlib.Path(tmp)/f'page-{size}.db'
  owner=live.SQLite(os.environ['SQLITE3_BIN'],db)
  try:
   owner.query(f'PRAGMA page_size={size};PRAGMA journal_mode=WAL;PRAGMA wal_autocheckpoint=0;CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,29);')
   old={s:pathlib.Path(str(db)+s).read_bytes() for s in ['','-wal']}
   sql='UPDATE t SET v=67 WHERE id=1;'
   lean=subprocess.run([str(root/'.lake/build/bin/sqleanite'),'--verified-wal-file',str(db)],input=sql,text=True,capture_output=True,timeout=60)
   unchanged=all(pathlib.Path(str(db)+s).read_bytes()==data for s,data in old.items())
   sqlite_result=owner.query(sql+'SELECT v FROM t;')
   results.append(dict(page_size=size,sql=sql,observer='open idle SQLite connection',lean=dict(code=lean.returncode,stdout=lean.stdout,stderr=lean.stderr),sqlite=dict(code=0,stdout=sqlite_result),lean_preserved_files=unchanged,compatibility_match=lean.returncode==0 and sqlite_result=='67\n'))
  finally:owner.close()
report=dict(purpose=__doc__.strip(),cases=results,compatibility_failures=sum(not r['compatibility_match'] for r in results),executable_sha256=live.digest(root/'.lake/build/bin/sqleanite'),native_sha256=live.digest(root/'native/sqleanite_vfs.c'),harness_sha256=live.digest(pathlib.Path(__file__)),sqlite_identity=subprocess.check_output([os.environ['SQLITE3_BIN'],'--version'],text=True).strip())
dest=root/'docs/validation/sqlite-wal-shared-remaining-negative-20261027.json'
dest.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
