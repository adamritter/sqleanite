#!/usr/bin/env python3
"""Compare rowid/INTEGER PRIMARY KEY UPDATE with independent SQLite images.

Every UPDATE starts from its own fixture copy. Checks exact rows, rejection
status, indexed-image integrity, full byte preservation on errors and rollback.
Declared non-rowid keys, conflict policies beyond ABORT and triggers are not
included; all generated mismatches are retained.
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
    p.add_argument('--seed',type=int,default=353570)
    p.add_argument('--random-cases',type=int,default=80)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed)
    observation='SELECT rowid,hex(v),n FROM t ORDER BY rowid;'
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-rowid-update-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            for explicit in [False,True]:
                for indexed in [False,True]:
                    d=pathlib.Path(tmp)/(mode+f'-{explicit}-{indexed}');d.mkdir()
                    key='id' if explicit else 'rowid'
                    schema='CREATE TABLE t('+('id INTEGER PRIMARY KEY,' if explicit else '')+'v TEXT,n INTEGER NOT NULL);'
                    setup=[schema,'CREATE TABLE empty(v);']
                    for i in [-5,-2,1,2,5,9]:setup.append(f"INSERT INTO t(rowid,v,n) VALUES({i},'row {i}',{rng.randrange(-50,51)});")
                    if indexed:setup+=['CREATE INDEX tv ON t(v);CREATE INDEX tn ON t(n);']
                    queries=[
                        f'UPDATE t SET {key}={key}+20;', f'UPDATE t SET {key}=-{key};',
                        f'UPDATE t SET {key}={key}+1;', f'UPDATE t SET {key}={key}-1;',
                        f'UPDATE t SET {key}=1;', f'UPDATE t SET {key}={key};',
                        f'UPDATE t SET {key}=NULL;', f'UPDATE t SET {key}=1.5;',
                        f"UPDATE t SET {key}='42';", f"UPDATE t SET {key}='42x';",
                        f'UPDATE t SET {key}=9223372036854775807 WHERE rowid=1;',
                        f'UPDATE t SET {key}=9223372036854775808 WHERE rowid=1;',
                        f"UPDATE t SET {key}={key}+100,v=v||{key},n={key};",
                        f'UPDATE t SET {key}=abs(-9223372036854775808),{key}={key}+50;',
                        f'UPDATE t SET {key}=missing,{key}={key}+50;',
                        f'UPDATE t AS x SET {key}=x.{key}+100,v=x.v||x.{key} WHERE x.n+1>0;',
                        'UPDATE t SET oid=oid+100 WHERE _rowid_ IN (-5,2,9);',
                        'UPDATE t SET rowid=100,_rowid_=rowid+20 WHERE rowid=1;',
                        'UPDATE t SET rowid=100,n=NULL WHERE rowid=1;',
                        'UPDATE t SET rowid=NULL WHERE 0;',
                        'UPDATE empty SET rowid=NULL;', 'UPDATE empty SET rowid=missing;',
                        'UPDATE t SET rowid=CASE WHEN rowid=9 THEN abs(-9223372036854775808) ELSE rowid+100 END;',
                        f'BEGIN;UPDATE t SET {key}={key}+100;ROLLBACK;']
                    choices=[f'{key}+{n}' for n in [-20,-3,-1,1,3,20,100]]+['0','NULL','-rowid','rowid%5','CAST(rowid AS TEXT)','rowid+0.0']
                    for _ in range(args.random_cases):
                        where=rng.choice(['',' WHERE rowid<0',' WHERE rowid>0',' WHERE rowid=1',' WHERE rowid IN (-5,2,9)',' WHERE n+1>0',' WHERE rowid< -100'])
                        target=rng.choice([key,'rowid','oid','_rowid_'])
                        queries.append(f'UPDATE t SET {target}={rng.choice(choices)},v=v||rowid{where};')
                    def sqlite(db,sql):return subprocess.run([args.sqlite,'-batch','-bail',str(db)],input=sql,text=True,capture_output=True,timeout=120)
                    def lean(db,sql):
                        q=d/'query.sql';q.write_text(sql)
                        return subprocess.run([str(args.lean),mode,str(db),str(q)],text=True,capture_output=True,timeout=120)
                    a_base=d/'lean-base.db';b_base=d/'sqlite-base.db'
                    a=lean(a_base,'\n'.join(setup));b=sqlite(b_base,'\n'.join(setup));assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
                    matching_errors=0;passed=0
                    for i,sql in enumerate(queries):
                        case=d/str(i);case.mkdir();a_db=case/'lean.db';b_db=case/'sqlite.db'
                        for source,target in [(a_base,a_db),(b_base,b_db)]:
                            shutil.copyfile(source,target)
                            wal=pathlib.Path(str(source)+'-wal')
                            if wal.exists():shutil.copyfile(wal,str(target)+'-wal')
                        files=[a_db,pathlib.Path(str(a_db)+'-wal')];before={str(f):f.read_bytes() for f in files if f.exists()}
                        a=lean(a_db,sql);b=sqlite(b_db,sql)
                        same=(a.returncode==0)==(b.returncode==0)
                        if a.returncode and b.returncode:
                            matching_errors+=1
                            assert before=={str(f):f.read_bytes() for f in files if f.exists()},sql
                        if not same:
                            failures.append(dict(mode=mode,explicit=explicit,indexed=indexed,sql=sql,lean=dict(code=a.returncode,stderr=a.stderr),sqlite=dict(code=b.returncode,stderr=b.stderr)));continue
                        a=lean(a_db,observation);b=sqlite(b_db,observation)
                        if a.returncode or b.returncode or a.stdout!=b.stdout:
                            failures.append(dict(mode=mode,explicit=explicit,indexed=indexed,sql=sql,lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=dict(code=b.returncode,stdout=b.stdout,stderr=b.stderr)));continue
                        inspector=case/'inspect.db';shutil.copyfile(a_db,inspector)
                        wal=pathlib.Path(str(a_db)+'-wal')
                        if wal.exists():shutil.copyfile(wal,str(inspector)+'-wal')
                        c=sqlite(inspector,observation+'PRAGMA integrity_check;')
                        if c.returncode or c.stdout!=b.stdout+'ok\n':
                            failures.append(dict(mode=mode,explicit=explicit,indexed=indexed,sql=sql,kind='SQLite image verification',actual=dict(code=c.returncode,stdout=c.stdout,stderr=c.stderr),expected=b.stdout+'ok\n'));continue
                        passed+=1
                    phases.append(dict(mode=mode,explicit_primary_key=explicit,indexed=indexed,updates=len(queries),passed=passed,matching_errors=matching_errors))
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,
        implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    if args.output:args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__':raise SystemExit(main())
