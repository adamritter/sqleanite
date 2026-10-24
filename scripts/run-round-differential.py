#!/usr/bin/env python3
"""Compare SQLite 3.53.4 round at the CLI and persisted-value boundaries.

SQLite creates the oracle. Independent copies of both images are read for
storage classes, binary64 bits and integrity. Includes random finite bit
patterns, decimal midpoint neighbours, precision coercion, NULL and lazy paths.
"""
import argparse
import contextlib
import hashlib
import json
import math
import os
import pathlib
import random
import shutil
import sqlite3
import struct
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def corpus(rng, count):
    cases=[]
    values=['NULL','0','-0.0','0.5','-0.5','1.5','-1.5','2.675','1.005','9.995',
            '0.05','-0.05','0.04999999999999999','0.005','49.47','4.9406564584124654e-324',
            '2.2250738585072014e-308','1e-30','1.234567890123456789e-15','1e999','-1e999',
            '4503599627370495.5','4503599627370496','4503599627370497',
            '9223372036854775807',"'12.55x'","'junk'","'NaN'","'Inf'","X'31322E353578'",
            "X'FF'","CAST(X'312E32350078' AS TEXT)"]
    places=['NULL','-9223372036854775808','-1','0','1','2','15','16','17','18','20','30','31',
            '9223372036854775807','1.9',"'2e1'","'bad'","X'3330'"]
    for v in values:
        cases.append((v,'0',f'round({v})'))
        cases.extend((v,p,f'round({v},{p})') for p in places)
    for _ in range(count):
        p=rng.randrange(-3,35)
        kind=rng.randrange(3)
        if kind==0:
            value=struct.unpack('>d',rng.getrandbits(64).to_bytes(8,'big'))[0]
            if not math.isfinite(value):value=0.0
        elif kind==1:
            value=(rng.randrange(-10**15,10**15)+0.5)*10.0**(-rng.randrange(0,31))
            value=math.nextafter(value,rng.choice([math.inf,-math.inf]))
        else:
            value=rng.uniform(-100000,100000)
        v=repr(value);cases.append((v,str(p),f'round({v},{p})'))
    return cases


def snapshot(db,target):
    shutil.copyfile(db,target)
    wal=pathlib.Path(str(db)+'-wal')
    if wal.exists():shutil.copyfile(wal,str(target)+'-wal')
    with contextlib.closing(sqlite3.connect(target)) as c:
        assert c.execute('PRAGMA integrity_check').fetchall()==[('ok',)]
        def encode(v):
            if isinstance(v,float):return struct.pack('>d',v).hex()
            return v
        return [[i,kind,encode(v)] for i,kind,v in c.execute('SELECT id,typeof(v),v FROM r ORDER BY id')]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353580)
    p.add_argument('--random-cases',type=int,default=500)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed);cases=corpus(rng,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-round-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            d=pathlib.Path(tmp)/mode;d.mkdir();lean=d/'lean.db';oracle=d/'sqlite.db'
            def run(sql):
                query=d/'query.sql';query.write_text(sql)
                a=subprocess.run([str(args.lean),mode,str(lean),str(query)],text=True,capture_output=True,timeout=180)
                b=subprocess.run([args.sqlite,'-batch','-bail',str(oracle)],input=sql,text=True,capture_output=True,timeout=180)
                return a,b
            setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v,p);CREATE TABLE r(id INTEGER PRIMARY KEY,v);'
            a,b=run(setup);assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            for start in range(0,len(cases),200):
                source='BEGIN;'+''.join(f'INSERT INTO t VALUES({i},{v},{p});INSERT INTO r VALUES({i},{expr});' for i,(v,p,expr) in enumerate(cases[start:start+200],start+1))+'COMMIT;'
                a,b=run(source);assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            actual=snapshot(lean,d/'lean-copy.db');expected=snapshot(oracle,d/'sqlite-copy.db')
            assert len(actual)==len(expected)==len(cases)
            for i,(a,b) in enumerate(zip(actual,expected)):
                if a!=b:failures.append(dict(mode=mode,kind='persisted bits',expression=cases[i][2],lean=a,sqlite=b))
            queries=['SELECT id,round(v,p),typeof(round(v,p)) FROM t ORDER BY id;',
                     'SELECT id,round(v),typeof(round(v)) FROM t ORDER BY id;',
                     'SELECT sum(round(v,p)),count(round(v,p)) FROM t WHERE id<10;',
                     'SELECT round(abs(-9223372036854775808),2) LIMIT 0;',
                     'SELECT round(abs(-9223372036854775808),2) WHERE 0;',
                     'SELECT coalesce(7,round(abs(-9223372036854775808),2));',
                     'SELECT round(v,p) FROM t WHERE id<0;',
                     'SELECT round(NULL,abs(-9223372036854775808));',
                     'SELECT round(abs(-9223372036854775808),NULL);',
                     'SELECT round();','SELECT round(1,2,3);',
                     'SELECT round(missing,2) FROM t WHERE 0;',
                     'SELECT round(1,unknown_function()) WHERE 0;']
            matching_errors=0
            for sql in queries:
                a,b=run(sql)
                if a.returncode and b.returncode:matching_errors+=1
                elif a.returncode or b.returncode or a.stdout!=b.stdout:
                    failures.append(dict(mode=mode,kind='CLI',sql=sql,lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=dict(code=b.returncode,stdout=b.stdout,stderr=b.stderr)))
            phases.append(dict(mode=mode,stored_values=len(cases),queries=len(queries),matching_errors=matching_errors))
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
