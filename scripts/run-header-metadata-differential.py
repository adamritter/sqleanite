#!/usr/bin/env python3
"""Check persistent application_id and user_version through live writes.

Pinned SQLite creates each foreign input file and independently checks both
post-write databases. Compare public header PRAGMAs, typed/quoted data and
integrity_check. Raw counter/format fields are recorded, not required to equal
SQLite's allocation choices. This does not test concurrent connection caches.
"""
import argparse
import hashlib
import json
import os
import random
from pathlib import Path
import shutil
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--seed',type=int,default=353840)
    p.add_argument('--random-cases',type=int,default=0)
    p.add_argument('--wal-overlay',action='store_true')
    p.add_argument('--checkpoint',action='store_true')
    a=p.parse_args();cases=[];failures=[];rng=random.Random(a.seed)
    metadata=[(0,0),(1234567,42),(2147483647,2147483647),(-1,-7),(-2147483648,-2147483648)]
    metadata += [(rng.randrange(0,2**31),rng.randrange(0,2**31)) for _ in range(a.random_cases)]
    with tempfile.TemporaryDirectory(prefix='sqleanite-header-') as tmp:
        tmp=Path(tmp)
        for mode in (['--verified-wal-file'] if a.wal_overlay else ['--verified-file','--verified-wal-file']):
            for page in [512,4096,65536]:
                for app,user in metadata:
                    for operation in ['UPDATE t SET v=7 WHERE id=1;','INSERT INTO t VALUES(2,8);','CREATE INDEX t_v ON t(v);','UPDATE t SET v=9;INSERT INTO t VALUES(2,10);CREATE INDEX t_v ON t(v);DELETE FROM t WHERE id=1;']:
                        folder=tmp/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db'
                        setup=f'PRAGMA page_size={page};PRAGMA application_id={app};PRAGMA user_version={user};CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,3);'
                        subprocess.run([a.sqlite,'-batch','-bail',str(ref)],input=setup.encode(),check=True,capture_output=True)
                        if a.wal_overlay:
                            # Put the requested metadata only in the WAL, while
                            # keeping main-header metadata different. No reader
                            # connection remains open during the Lean write.
                            subprocess.run([a.sqlite,'-batch','-bail',str(ref)],input=b'PRAGMA application_id=0;PRAGMA user_version=0;',check=True,capture_output=True)
                            overlay=f'PRAGMA journal_mode=WAL;\n.dbconfig no_ckpt_on_close on\nPRAGMA application_id={app};PRAGMA user_version={user};UPDATE t SET v=4;\n'
                            subprocess.run([a.sqlite,'-batch','-bail',str(ref)],input=overlay.encode(),check=True,capture_output=True)
                            assert Path(str(ref)+'-wal').exists()
                        shutil.copyfile(ref,lean)
                        for suffix in ['-wal','-shm']:
                            if Path(str(ref)+suffix).exists():shutil.copyfile(str(ref)+suffix,str(lean)+suffix)
                        sql=folder/'write.sql';sql.write_text(operation)
                        l=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(lean),str(sql)],capture_output=True,timeout=120)
                        r=subprocess.run([a.sqlite,'-batch','-bail',str(ref)],input=operation.encode(),capture_output=True,timeout=120)
                        checkpoint_code=0
                        if a.checkpoint and mode=='--verified-wal-file' and l.returncode==0:
                            checkpoint=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),'--verified-wal-checkpoint',str(lean)],capture_output=True,timeout=120)
                            checkpoint_code=checkpoint.returncode
                        query='PRAGMA application_id;PRAGMA user_version;PRAGMA integrity_check;SELECT id,typeof(v),quote(v) FROM t ORDER BY id;'
                        def inspect(path):
                            result=subprocess.run([a.sqlite,'-batch','-bail',str(path)],input=query.encode(),capture_output=True)
                            h=path.read_bytes()[:100]
                            fields={name:int.from_bytes(h[offset:offset+4],'big') for name,offset in [('change_counter',24),('schema_cookie',40),('encoding',56),('user_version',60),('application_id',68),('version_valid_for',92),('sqlite_version',96)]}
                            return dict(code=result.returncode,stdout=result.stdout.decode('latin1'),stderr=result.stderr.decode('latin1'),raw_header=fields)
                        left,right=inspect(lean),inspect(ref)
                        item=dict(wal_overlay=a.wal_overlay,checkpoint=a.checkpoint,checkpoint_code=checkpoint_code,mode=mode,page_size=page,application_id=app,user_version=user,sql=operation,lean_write_code=l.returncode,sqlite_write_code=r.returncode,lean=left,sqlite=right)
                        same=l.returncode==r.returncode==left['code']==right['code']==checkpoint_code==0 and left['stdout']==right['stdout']
                        cases.append(item)
                        if not same:failures.append(len(cases)-1)
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(wal_overlay=a.wal_overlay,checkpoint=a.checkpoint,seed=a.seed,random_cases=a.random_cases,cases=cases,failed_case_indices=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=len(failures))))
    return bool(failures)
if __name__=='__main__':raise SystemExit(main())
