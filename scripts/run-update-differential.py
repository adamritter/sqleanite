#!/usr/bin/env python3
"""Compare row-dependent UPDATE using independently decoded stored values.

SQLite 3.53.4 is the SQL oracle. Python SQLite reads the resulting files to
compare storage classes, exact binary64 bits and raw TEXT/BLOB bytes. Both
production journal modes must preserve the whole file on failed statements.
"""
import argparse
import contextlib
import hashlib
import json
import os
import pathlib
import random
import sqlite3
import struct
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def observation(path):
    with contextlib.closing(sqlite3.connect(f'file:{path}?mode=ro',uri=True)) as c:
        c.text_factory=bytes
        def value(v):
            if v is None: return ['null']
            if isinstance(v,int): return ['integer',v]
            if isinstance(v,float): return ['real',struct.pack('>d',v).hex()]
            return ['bytes',v.hex()]
        return {name:[[value(v) for v in row] for row in c.execute(query)] for name,query in [
            ('t','SELECT id,typeof(a),a,typeof(b),b,typeof(r),r,typeof(s),s,typeof(u),u,n FROM t ORDER BY id'),
            ('tp','SELECT k,typeof(v),v FROM tp ORDER BY k')]}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353480)
    p.add_argument('--random-cases',type=int,default=40)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed)
    setup=['CREATE TABLE t(id INTEGER PRIMARY KEY,a INTEGER,b NUMERIC,r REAL,s TEXT,u BLOB,n NOT NULL);','BEGIN;']
    pool=['NULL',"'1'",'1.5','-2','0',"'x'",'9007199254740993']
    for i in range(1,121):
        setup.append(f"INSERT INTO t VALUES({i},{rng.randrange(-1000,1000)},{rng.choice(pool)},{rng.randrange(-1000,1000)}/7.0,'s-{i}',X'00FF',{i});")
    setup += ['COMMIT;','CREATE INDEX ta ON t(a);','CREATE INDEX ts ON t(s);',
              'CREATE TABLE empty(id INTEGER PRIMARY KEY,a INTEGER);',
              'CREATE TABLE tp(k TEXT PRIMARY KEY,v);',
              "INSERT INTO tp VALUES('a','hello'),('b',2);"]
    queries=[
        "UPDATE tp SET v=upper(v)||k WHERE length(k)>0;",
        'UPDATE t SET a=b,b=a WHERE id<=10;',
        'UPDATE t SET s=upper(s),n=n+1 WHERE id%2=0;',
        'UPDATE t SET r=r/3.0 WHERE id+0>110;',
        'UPDATE t SET u=CAST(s AS BLOB),s=hex(u) WHERE id%5=0;',
        'UPDATE t AS x SET s=upper(x.s),a=x.a+1 WHERE x.id%3=0;',
        'UPDATE t SET a=abs(-9223372036854775808),a=a+1 WHERE id<4;',
        'UPDATE empty SET a=abs(-9223372036854775808);',
        'UPDATE t SET a=abs(-9223372036854775808)+id WHERE 0;',
        'UPDATE t SET a=a+9223372036854775807 WHERE id>117;',
    ]
    assignments=['a=a+1','a=b,b=a','r=coalesce(b,r)/3.0','s=substr(s,1,8)||id',
                 'u=CAST(s AS BLOB)','b=CASE WHEN id%2 THEN a ELSE NULL END',
                 'a=CAST(s AS INTEGER)','b=b+2.5','s=lower(s)','n=n+1',
                 'a=a*2,b=b+1','a=length(u)','s=quote(b)','s=upper(s)',
                 'a=coalesce(a,0)-id','r=-r','u=zeroblob(id%9)']
    for _ in range(args.random_cases):
        condition=rng.choice([f'id%{rng.randrange(2,8)}={rng.randrange(2)}',
                              f'id>{rng.randrange(100,120)}','n+0>0',"instr(s,'1')>0",'id<0'])
        queries.append(f'UPDATE t SET {rng.choice(assignments)} WHERE {condition};')
    errors=['UPDATE t SET a=unknown_function(),a=a+1 WHERE id<4;', 'UPDATE t SET a=missing WHERE 0;', 'UPDATE empty SET a=missing;',
            'UPDATE t SET a=missing,a=2;', 'UPDATE t SET a=wrong.a;',
            'UPDATE t SET n=CASE WHEN id=120 THEN NULL ELSE n+1 END;',
            'UPDATE t SET a=CASE WHEN id=120 THEN abs(-9223372036854775808) ELSE 2 END;',
            'UPDATE t SET a=coalesce(a,unknown_function());']
    phases=[];failures=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-update-') as temp:
        for mode in ['--verified-file','--verified-wal-file']:
            cwd=pathlib.Path(temp)/mode;cwd.mkdir();lean=cwd/'lean.db';oracle=cwd/'sqlite.db'
            def run(sql):
                q=cwd/'query.sql';q.write_text(sql)
                a=subprocess.run([str(args.lean),mode,str(lean),str(q)],text=True,capture_output=True,timeout=180)
                b=subprocess.run([args.sqlite,'-batch','-bail',str(oracle)],input=sql,text=True,capture_output=True,timeout=180)
                return a,b
            a,b=run('\n'.join(setup));assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            passed=0
            for q in queries:
                a,b=run(q)
                try:
                    actual,expected=observation(lean),observation(oracle)
                except sqlite3.DatabaseError as error:
                    failure=dict(mode=mode,sql=q,error=str(error),lean_code=a.returncode,sqlite_code=b.returncode)
                    probe=subprocess.run([args.sqlite,'-readonly',str(lean),'PRAGMA integrity_check;'],text=True,capture_output=True)
                    failure['sqlite_integrity']=dict(code=probe.returncode,stdout=probe.stdout,stderr=probe.stderr)
                    if args.output:
                        saved=args.output.parent/(args.output.stem+'-failure')/mode
                        saved.mkdir(parents=True,exist_ok=True)
                        for artifact in cwd.iterdir():
                            if artifact.is_file(): (saved/artifact.name).write_bytes(artifact.read_bytes())
                        failure['local_artifacts']=str(saved)
                    failures.append(failure)
                    break
                if a.returncode!=b.returncode or a.returncode!=0 or actual!=expected:
                    failures.append(dict(mode=mode,sql=q,lean=dict(code=a.returncode,stderr=a.stderr),sqlite=dict(code=b.returncode,stderr=b.stderr),
                        different_rows={name:[dict(lean=x,sqlite=y) for x,y in zip(actual[name],expected[name]) if x!=y][:3] for name in ['t','tp']}))
                    break
                integrity=subprocess.check_output([args.sqlite,'-readonly',str(lean),'PRAGMA integrity_check;'],text=True).strip()
                assert integrity=='ok',(mode,q,integrity)
                passed += 1
            if passed != len(queries):
                phases.append(dict(mode=mode,updates=passed,requested_updates=len(queries),incomplete=True))
                continue
            for q in errors:
                before=observation(lean)
                raw={p.name:p.read_bytes() for p in [lean,pathlib.Path(str(lean)+'-wal')] if p.exists()}
                a,b=run(q)
                assert a.returncode!=0 and b.returncode!=0,(mode,q,a.stdout,a.stderr,b.stderr)
                assert observation(lean)==before and all((cwd/name).read_bytes()==data for name,data in raw.items()),(q,'failed UPDATE changed file')
            before=observation(lean)
            a,b=run('BEGIN; UPDATE t SET a=a+1,n=n+1 WHERE id%2=0; ROLLBACK;')
            assert a.returncode==b.returncode==0 and observation(lean)==observation(oracle)==before
            phases.append(dict(mode=mode,updates=passed,requested_updates=len(queries),rows_per_observation=122,expected_errors=len(errors),rollback=True))
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,
        implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),
        comparison='SQLite-decoded storage classes, exact binary64, TEXT/BLOB bytes after each UPDATE; integrity; failed-statement bytes; rollback.')
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__':
    raise SystemExit(main())
