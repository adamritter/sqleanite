#!/usr/bin/env python3
"""Compare explicit single-column UNIQUE index constraints and file interchange.

Each statement starts from a separate fixture. Both journal modes read Lean
and SQLite origins (512/4096 bytes), explicit/implicit rowids, two unique keys,
NULLs and mixed storage classes. Check rows, schema uniqueness flags, independent
SQLite integrity and unchanged main/WAL bytes on failed statements.
"""
import argparse
import contextlib
import hashlib
import json
import os
import pathlib
import random
import shutil
import sqlite3
import struct
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def copy_image(source,target):
    shutil.copyfile(source,target)
    wal=pathlib.Path(str(source)+'-wal')
    if wal.exists():shutil.copyfile(wal,str(target)+'-wal')


def observe(path):
    with contextlib.closing(sqlite3.connect(path)) as c:
        c.text_factory=bytes
        integrity=c.execute('PRAGMA integrity_check').fetchall()
        def encode(v):
            if isinstance(v,float):return ['binary64',struct.pack('>d',v).hex()]
            if isinstance(v,bytes):return ['bytes',v.hex()]
            return v
        rows=[[encode(v) for v in r] for r in c.execute('SELECT rowid,typeof(a),a,typeof(b),b,n FROM t ORDER BY rowid')]
        indexes=sorted([[r[1].decode(),r[2],r[3].decode(),r[4]] for r in c.execute('PRAGMA index_list(t)')])
        return dict(rows=rows,indexes=indexes,integrity=[[v.decode() for v in r] for r in integrity])


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353600)
    p.add_argument('--random-cases',type=int,default=60)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed);failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-unique-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            for explicit in [False,True]:
                for origin in ['lean','sqlite-512','sqlite-4096']:
                    d=pathlib.Path(tmp)/(mode+f'-{explicit}-{origin}');d.mkdir()
                    setup='CREATE TABLE t('+('id INTEGER PRIMARY KEY,' if explicit else '')+'a BLOB,b TEXT,n INTEGER);'
                    setup+="INSERT INTO t(rowid,a,b,n) VALUES(1,1,'a',0),(2,2.5,'b',0),(3,'1','c',1),(4,X'31','d',1),(5,NULL,'e',2),(6,NULL,NULL,2),(7,9223372036854775807,'large',3);CREATE UNIQUE INDEX ua ON t(a);CREATE UNIQUE INDEX ub ON t(b);CREATE TABLE empty(a);"
                    queries=[
                        "INSERT INTO t(a,b,n) VALUES(1.0,'fresh',5);",
                        "INSERT INTO t(a,b,n) VALUES('1','fresh',5);",
                        "INSERT INTO t(a,b,n) VALUES(X'31','fresh',5);",
                        "INSERT INTO t(a,b,n) VALUES(NULL,NULL,5),(NULL,NULL,5);",
                        "INSERT INTO t(a,b,n) VALUES(9223372036854775808,'fresh',5);",
                        "INSERT INTO t(a,b,n) VALUES(-0.0,'fresh',5),(0,'next',6);",
                        "INSERT INTO t(a,b,n) VALUES(99,'fresh',5),(2.5,'other',6);",
                        "INSERT OR REPLACE INTO t(a,b,n) VALUES(1,'fresh',5);",
                        "INSERT OR REPLACE INTO t(rowid,a,b,n) VALUES(1,2.5,'c',5);",
                        "INSERT OR REPLACE INTO t(a,b,n) VALUES(NULL,'a',5),(2.5,'c',6);",
                        "REPLACE INTO t(rowid,a,b,n) VALUES(1,1,'a',5);",
                        "UPDATE t SET a=1 WHERE rowid=2;", "UPDATE t SET a=NULL;",
                        "UPDATE t SET b='same';", "UPDATE t SET a=a WHERE rowid<3;",
                        "UPDATE t SET a=a+1 WHERE rowid<3;", "UPDATE t SET a=1.0 WHERE rowid=1;",
                        "UPDATE t SET a=2.5 WHERE rowid=1;", "UPDATE t SET b='c' WHERE rowid=2;",
                        "UPDATE t SET a=CASE WHEN rowid=7 THEN 1 ELSE rowid+100 END;",
                        "UPDATE t SET a=a+0 WHERE rowid IN (1,3,4);",
                        "UPDATE t SET rowid=rowid+100,b=b||rowid;",
                        "UPDATE t SET rowid=100,a=1 WHERE rowid=2;",
                        "DELETE FROM t WHERE rowid=1;INSERT INTO t(a,b,n) VALUES(1,'a',9);",
                        "CREATE UNIQUE INDEX un ON t(n);", "CREATE UNIQUE INDEX ue ON empty(a);",
                        "CREATE UNIQUE INDEX ua2 ON t(a);",
                        "BEGIN;INSERT OR REPLACE INTO t(a,b,n) VALUES(1,'c',5);ROLLBACK;",
                        "BEGIN;UPDATE t SET a=NULL;ROLLBACK;"]
                    for _ in range(args.random_cases):
                        action=rng.randrange(3)
                        if action==0:
                            expr=rng.choice(['a','NULL','rowid+100','1','1.0',"'1'","X'31'",'a+1','a+0','-a'])
                            where=rng.choice(['',' WHERE rowid=1',' WHERE rowid=2',' WHERE rowid<4',' WHERE rowid>4',' WHERE rowid<0'])
                            queries.append(f'UPDATE t SET a={expr}{where};')
                        else:
                            value=rng.choice(['1','1.0','2.5',"'1'","X'31'",'NULL','99',str(rng.randrange(20,100))])
                            b=rng.choice(["'a'","'c'",'NULL',"'new'",f"'fresh{rng.randrange(99)}'"])
                            verb='INSERT OR REPLACE' if action==2 else 'INSERT'
                            queries.append(f'{verb} INTO t(a,b,n) VALUES({value},{b},9);')
                    def sqlite(db,sql):return subprocess.run([args.sqlite,'-batch','-bail',str(db)],input=sql,text=True,capture_output=True,timeout=180)
                    def lean(db,sql):
                        q=d/'query.sql';q.write_text(sql)
                        return subprocess.run([str(args.lean),mode,str(db),str(q)],text=True,capture_output=True,timeout=180)
                    a_base=d/'lean-base.db';b_base=d/'sqlite-base.db'
                    b=sqlite(b_base,setup);assert b.returncode==0,b.stderr
                    if origin=='lean':a=lean(a_base,setup)
                    else:a=sqlite(a_base,f'PRAGMA page_size={origin.split("-")[1]};'+setup)
                    if a.returncode:
                        failures.append(dict(mode=mode,explicit=explicit,origin=origin,kind='setup',code=a.returncode,stderr=a.stderr));continue
                    passed=0;matching_errors=0
                    for i,sql in enumerate(queries):
                        case=d/str(i);case.mkdir();a_db=case/'lean.db';b_db=case/'sqlite.db'
                        copy_image(a_base,a_db);copy_image(b_base,b_db)
                        files=[a_db,pathlib.Path(str(a_db)+'-wal')];before={str(f):f.read_bytes() for f in files if f.exists()}
                        a=lean(a_db,sql);b=sqlite(b_db,sql)
                        if a.returncode and b.returncode:
                            matching_errors+=1
                            assert before=={str(f):f.read_bytes() for f in files if f.exists()},sql
                        elif a.returncode or b.returncode:
                            failures.append(dict(mode=mode,explicit=explicit,origin=origin,sql=sql,lean=dict(code=a.returncode,stderr=a.stderr),sqlite=dict(code=b.returncode,stderr=b.stderr)));continue
                        inspector=case/'inspect.db';copy_image(a_db,inspector)
                        try:actual=observe(inspector);expected=observe(b_db)
                        except sqlite3.DatabaseError as e:
                            failures.append(dict(mode=mode,explicit=explicit,origin=origin,sql=sql,kind='SQLite read',error=str(e)));continue
                        if actual!=expected or actual['integrity']!=[['ok']]:
                            failures.append(dict(mode=mode,explicit=explicit,origin=origin,sql=sql,lean=actual,sqlite=expected));continue
                        q='SELECT rowid,hex(a),hex(b),n FROM t ORDER BY rowid;'
                        a=lean(a_db,q);b=sqlite(b_db,q)
                        if a.returncode or a.stdout!=b.stdout:
                            failures.append(dict(mode=mode,explicit=explicit,origin=origin,sql=sql,kind='Lean reopen',lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=b.stdout));continue
                        passed+=1
                    phases.append(dict(mode=mode,explicit_primary_key=explicit,origin=origin,statements=len(queries),passed=passed,matching_errors=matching_errors))
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,
        implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    if args.output:args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2));return bool(failures)


if __name__=='__main__':raise SystemExit(main())
