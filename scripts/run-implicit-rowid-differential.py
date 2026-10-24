#!/usr/bin/env python3
"""Compare implicit/aliased rowid allocation and persisted rowid tables.

Checks generated and explicit rowids, negative maxima, DEFAULT VALUES, duplicate
rejections, rowid-name shadowing, schema reopen, and cross-engine database/WAL
reads after writes. SQLite-created fixtures span all supported page sizes.
No maximum-rowid random-allocation parity claim is made by this suite.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import shutil
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353560)
    p.add_argument('--random-cases',type=int,default=50)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed)
    setup='CREATE TABLE t(v,w INTEGER);CREATE TABLE pk(id INTEGER PRIMARY KEY,v);CREATE TABLE shadows(rowid,oid,_rowid_,v);'
    steps=["INSERT INTO t(rowid,v,w) VALUES(-5,'a',1),(-2,'b',2);",
           "INSERT INTO t(v,w) VALUES('c',3);",'INSERT INTO t DEFAULT VALUES;',
           "INSERT INTO t(rowid,v) VALUES(NULL,'null id');", "INSERT INTO t(rowid,v) VALUES(12,'twelve');",
           "INSERT INTO t(v) VALUES('after twelve');", "INSERT INTO t(oid,v) VALUES(12,'duplicate');",
           "INSERT INTO t(unknown) VALUES(1);", 'INSERT INTO t(unknown) DEFAULT VALUES;',
           "INSERT INTO pk(v) VALUES('auto');", 'INSERT INTO pk DEFAULT VALUES;',
           "INSERT INTO pk VALUES(NULL,'null');", "INSERT INTO pk(id,v) VALUES(-20,'negative');",
           "INSERT INTO pk(rowid,v) VALUES(30,'explicit');", "INSERT INTO pk(v) VALUES('next');",
           "INSERT INTO shadows VALUES('shadow r','shadow o','shadow u',1);",
           "INSERT INTO shadows(rowid,v) VALUES('shadow two',2);",
           'INSERT INTO shadows DEFAULT VALUES;',
           "CREATE INDEX tw ON t(w);", "UPDATE t SET w=w+1 WHERE rowid=-5;",
           'DELETE FROM t WHERE rowid=-2;', "INSERT OR REPLACE INTO t(rowid,v,w) VALUES(12,'replace',0);",
           'INSERT INTO t VALUES();']
    for i in range(args.random_cases):
        op=rng.randrange(5)
        if op==0: steps.append(f"INSERT INTO t(_rowid_,v,w) VALUES({rng.randrange(-50,150)},'explicit {i}',{rng.randrange(-20,21)});")
        elif op==1: steps.append(f"INSERT INTO t(v,w) VALUES('auto {i}',{rng.randrange(-20,21)});")
        elif op==2: steps.append('INSERT INTO t DEFAULT VALUES;')
        elif op==3: steps.append(f'DELETE FROM t WHERE rowid={rng.randrange(-50,150)};')
        else: steps.append(f'UPDATE t SET w=w+1 WHERE rowid={rng.randrange(-50,150)};')
    observation='SELECT rowid,hex(v),w FROM t ORDER BY rowid;SELECT id,hex(v) FROM pk ORDER BY id;SELECT hex(rowid),hex(oid),hex(_rowid_),v FROM shadows;'
    failures=[];phases=[]
    def sqlrun(db,sql):
        return subprocess.run([args.sqlite,'-batch','-bail',str(db)],input=sql,text=True,capture_output=True,timeout=120)
    with tempfile.TemporaryDirectory(prefix='sqleanite-implicit-rowid-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            for origin,page_size in [('lean',4096)]+[('sqlite',n) for n in [512,1024,2048,4096,8192,16384,32768,65536]]:
                d=pathlib.Path(tmp)/(mode+'-'+origin+'-'+str(page_size));d.mkdir()
                a_db=d/'lean.db';b_db=d/'sqlite.db';q=d/'query.sql'
                def leanrun(sql):
                    q.write_text(sql)
                    return subprocess.run([str(args.lean),mode,str(a_db),str(q)],text=True,capture_output=True,timeout=120)
                assert sqlrun(b_db,f'PRAGMA page_size={page_size};'+setup).returncode==0
                if origin=='sqlite': shutil.copyfile(b_db,a_db)
                else:
                    result=leanrun(setup)
                    if result.returncode:
                        failures.append(dict(mode=mode,origin=origin,page_size=page_size,sql=setup,lean=result.stderr));continue
                expected_mode=rng.choice([0o600,0o640,0o660])
                a_db.chmod(expected_mode)
                initial_stat=a_db.stat()
                matching_errors=0;passed=0
                for sql in steps:
                    paths=[a_db,d/'lean.db-wal'];before={str(f):f.read_bytes() for f in paths if f.exists()}
                    a=leanrun(sql);b=sqlrun(b_db,sql)
                    if (a.returncode==0)!=(b.returncode==0):
                        failures.append(dict(mode=mode,origin=origin,page_size=page_size,sql=sql,lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=dict(code=b.returncode,stdout=b.stdout,stderr=b.stderr)))
                        break
                    current_stat=a_db.stat()
                    assert (current_stat.st_mode & 0o777)==expected_mode
                    assert (current_stat.st_uid,current_stat.st_gid)==(initial_stat.st_uid,initial_stat.st_gid)
                    if a.returncode:
                        matching_errors+=1
                        assert before=={str(f):f.read_bytes() for f in paths if f.exists()},sql
                    a=leanrun(observation);b=sqlrun(b_db,observation)
                    if a.returncode or b.returncode or a.stdout!=b.stdout:
                        failures.append(dict(mode=mode,origin=origin,page_size=page_size,after=sql,sql=observation,lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=dict(code=b.returncode,stdout=b.stdout,stderr=b.stderr)));break
                    # Observe copies: SQLite may checkpoint on close, so no active
                    # observer changes the engine-under-test's original image.
                    copy_db=d/'inspect.db';shutil.copyfile(a_db,copy_db)
                    wal=d/'lean.db-wal';copy_wal=d/'inspect.db-wal'
                    if wal.exists(): shutil.copyfile(wal,copy_wal)
                    elif copy_wal.exists(): copy_wal.unlink()
                    inspector=sqlrun(copy_db,observation+'PRAGMA integrity_check;')
                    if inspector.returncode or inspector.stdout!=b.stdout+'ok\n':
                        failures.append(dict(mode=mode,origin=origin,page_size=page_size,after=sql,kind='SQLite persisted-image read',sqlite=dict(code=inspector.returncode,stdout=inspector.stdout,stderr=inspector.stderr),expected=b.stdout+'ok\n'));break
                    passed+=1
                phases.append(dict(mode=mode,origin=origin,page_size=page_size,statements=len(steps),passed=passed,matching_errors=matching_errors))
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,
        implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    if args.output: args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__':raise SystemExit(main())
