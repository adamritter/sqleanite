#!/usr/bin/env python3
"""Read-only transactions: exact SQL output, successful access to read-only files,
and unchanged main/WAL bytes, compared with pinned SQLite. No global claim.
"""
import argparse, hashlib, json, os, random, shutil, subprocess, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'))
 p.add_argument('--seed',type=int,default=354270)
 p.add_argument('--random-cases',type=int,default=0)
 p.add_argument('--output',type=Path,required=True)
 a=p.parse_args();rng=random.Random(a.seed);binary=ROOT/'.lake/build/bin/sqleanite';cases=[]
 def run(args,sql):
  r=subprocess.run([str(v) for v in args],input=sql.encode(),capture_output=True,timeout=120)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([a.sqlite,'-batch','-bail',path],sql)
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['', '-wal'] if Path(str(path)+s).exists()}
 queries=[
  'BEGIN;COMMIT;', 'BEGIN;SELECT id,v FROM t ORDER BY id;COMMIT;',
  'BEGIN;SELECT id,v FROM t ORDER BY id;ROLLBACK;',
  'SAVEPOINT s;RELEASE s;', 'SAVEPOINT s;SELECT id,v FROM t ORDER BY id;RELEASE s;',
  'BEGIN;SAVEPOINT s;SELECT id,v FROM t ORDER BY id;RELEASE s;COMMIT;',
  'SAVEPOINT outer;SAVEPOINT inner;SELECT id,v FROM t ORDER BY id;ROLLBACK TO inner;RELEASE outer;',
  'SAVEPOINT s;ROLLBACK TO s;RELEASE s;',
  'SAVEPOINT s;SELECT count(*) FROM t;COMMIT;',
  'SAVEPOINT s;SELECT count(*) FROM t;ROLLBACK;',
 ]
 writes=[
  "BEGIN;INSERT INTO t VALUES(4,'new');COMMIT;",
  "SAVEPOINT s;INSERT INTO t VALUES(4,'new');RELEASE s;",
  "SELECT 1;INSERT INTO t VALUES(4,'new');",
  "SAVEPOINT s;UPDATE t SET v=99 WHERE id=1;RELEASE s;",
 ]
 for _ in range(a.random_cases):
  count=rng.randrange(1,12);value=rng.randrange(1,4)
  sql='SAVEPOINT outer;'+''.join(f'SAVEPOINT s{i};SELECT v FROM t WHERE id={value};' for i in range(count))
  sql+=f'ROLLBACK TO s{rng.randrange(count)};RELEASE outer;'
  queries.append(sql)
 with tempfile.TemporaryDirectory(prefix='sqleanite-read-transaction-') as tmp:
  for page in [512,4096,65536]:
   base=Path(tmp)/f'base{page}.db'
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,7),(2,8),(3,9);CREATE INDEX tv ON t(v);'
   assert csql(base,setup)['code']==0
   for mode in ['--verified-file','--verified-wal-file']:
    for readonly in [False,True]:
     for multiline in [False,True]:
      for original in queries+(writes if readonly else []):
       sql=original.replace(';',';\n') if multiline else original
       folder=Path(tmp)/str(len(cases));folder.mkdir();left=folder/'lean.db';right=folder/'sqlite.db'
       shutil.copyfile(base,left);shutil.copyfile(base,right)
       if readonly:left.chmod(0o444);right.chmod(0o444)
       before_l=hashes(left);before_r=hashes(right)
       l=run([binary,mode,left],sql);r=csql(right,sql)
       after_l=hashes(left);after_r=hashes(right)
       observed_l=csql(left,'PRAGMA integrity_check;SELECT id,typeof(v),hex(v) FROM t ORDER BY id;')
       observed_r=csql(right,'PRAGMA integrity_check;SELECT id,typeof(v),hex(v) FROM t ORDER BY id;')
       matched=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and before_l==after_l and before_r==after_r and observed_l['code']==observed_r['code']==0 and observed_l['stdout']==observed_r['stdout'] and observed_l['stdout'].startswith('ok\n')
       cases.append(dict(page_size=page,mode=mode,readonly=readonly,multiline=multiline,write_attempt=original in writes,sql=sql,lean=l,sqlite=r,unchanged_lean=before_l==after_l,unchanged_sqlite=before_r==after_r,before_lean=before_l,after_lean=after_l,observed_lean=observed_l,observed_sqlite=observed_r,matched=matched))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
