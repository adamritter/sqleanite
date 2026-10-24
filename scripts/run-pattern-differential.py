#!/usr/bin/env python3
"""Compare LIKE/GLOB operators, functions and ESCAPE with SQLite 3.53.4.

Both production file modes are checked for exact stored values, SQLite image
integrity, row predicates/mutations, NULL/error ordering and pattern limits.
UTF-8 TEXT and arbitrary BLOB bytes are separate input families. Every mismatch
is retained; this is a bounded function test, not a whole-SQL coverage rate.
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
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def literal(s,blob=False):
    raw=s if isinstance(s,bytes) else s.encode()
    v="X'"+raw.hex()+"'"
    return v if blob else f'CAST({v} AS TEXT)'


def corpus(rng,count):
    cases=[]
    patterns=['','%','_','a%','%a','a_b','%_%','%a%b%','*','?','a*','*a','a?b','*?*',
              '[a-z]','[^a-z]','[]]','[^]]','[a-]','[-a]','[z-a]','[a--c]','[a-b-c]',
              '[','[]','[^]','[*]','[?]','*[]a]','*[a-z]*','Á%','🙂_','[α-ω]','%\x00x']
    values=['','a','A','ab','a_b','abc','z','-','?','*',']','α','Á','🙂a','a\x00z']
    for pat in patterns:
        for value in values:
            a,b=literal(pat),literal(value)
            cases.extend([f'like({a},{b})',f'glob({a},{b})',f'{b} NOT LIKE {a}',f'{b} NOT GLOB {a}'])
    for raw in [b'',b'\x00',b'\x80',b'\xbf',b'\xc0\x80',b'\xed\xa0\x80',b'\xff',b'\xff\xbf\xbf\xbf\xbf\xbf\xbf',b'a\xffb',b'\xef\xbf\xbe']:
        a=literal(raw,True)
        cases.extend([f'like({a},{a})',f'glob({a},{a})',f"{a} LIKE '_'",f"{a} GLOB '?'",f"{a} LIKE '%'",f"{a} GLOB '*'",f'like({a},NULL)',f'glob(NULL,{a})'])
    for pat in ['a\\%b','a\\_b','a\\\\b','a\\','%\\_%','%%','%_','__','_%','x%','xx','🙂%','%🙂_%']:
        for value in ['a%b','a_b','a\\b','abc','%','_','x','🙂','']:
            a,b=literal(pat),literal(value)
            for esc in ["'\\'","'%'","'_'","'x'","'🙂'",'NULL',"X'80'","CAST(X'5C0078' AS TEXT)"]:
                cases.append(f'{b} LIKE {a} ESCAPE {esc}')
    alphabet='abABzZ%_*?[]^-\\αÁ🙂\x00'
    for _ in range(count):
        blob=rng.randrange(5)==0
        if blob:
            pat=bytes(rng.randrange(256) for _ in range(rng.randrange(0,15)))
            value=bytes(rng.randrange(256) for _ in range(rng.randrange(0,15)))
        else:
            pat=''.join(rng.choices(alphabet,k=rng.randrange(0,18)))
            value=''.join(rng.choices(alphabet,k=rng.randrange(0,18)))
        a,b=literal(pat,blob),literal(value,blob)
        op=rng.choice(['LIKE','GLOB','NOT LIKE','NOT GLOB'])
        if rng.randrange(3)==0 and 'LIKE' in op:
            esc=literal(rng.choice(['\\','%','_','x','🙂']))
            cases.append(f'{b} {op} {a} ESCAPE {esc}')
        else:cases.append(f'{b} {op} {a}')
    cases += ["like(1,1)","glob(1.5,1.5)","like(NULL,NULL)","NULL LIKE '%'","NULL GLOB '*'",
              "like(replace(hex(zeroblob(25000)),'0','a'),'x')", "like('%',replace(hex(zeroblob(25000)),'0','a'))"]
    return cases


def snapshot(db,target):
    shutil.copyfile(db,target)
    wal=pathlib.Path(str(db)+'-wal')
    if wal.exists():shutil.copyfile(wal,str(target)+'-wal')
    with contextlib.closing(sqlite3.connect(target)) as c:
        assert c.execute('PRAGMA integrity_check').fetchall()==[('ok',)]
        return c.execute('SELECT id,typeof(v),v FROM r ORDER BY id').fetchall()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353590)
    p.add_argument('--random-cases',type=int,default=500)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();cases=corpus(random.Random(args.seed),args.random_cases);failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-pattern-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            d=pathlib.Path(tmp)/mode;d.mkdir();lean=d/'lean.db';oracle=d/'sqlite.db'
            def run(sql):
                query=d/'query.sql';query.write_text(sql)
                a=subprocess.run([str(args.lean),mode,str(lean),str(query)],text=True,capture_output=True,timeout=180)
                b=subprocess.run([args.sqlite,'-batch','-bail',str(oracle)],input=sql,text=True,capture_output=True,timeout=180)
                return a,b
            setup="CREATE TABLE r(id INTEGER PRIMARY KEY,v);CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,'abc'),(2,'ABC'),(3,'árvíz'),(4,NULL),(5,X'80'),(6,'a_c');CREATE INDEX tv ON t(v);"
            a,b=run(setup);assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            for start in range(0,len(cases),200):
                source='BEGIN;'+''.join(f'INSERT INTO r VALUES({i},{expr});' for i,expr in enumerate(cases[start:start+200],start+1))+'COMMIT;'
                a,b=run(source)
                if a.returncode or b.returncode:
                    failures.append(dict(mode=mode,kind='batch rejection',start=start,expressions=cases[start:start+200],lean=dict(code=a.returncode,stderr=a.stderr),sqlite=dict(code=b.returncode,stderr=b.stderr)));break
            actual=snapshot(lean,d/'lean-copy.db');expected=snapshot(oracle,d/'sqlite-copy.db')
            if len(actual)!=len(expected):failures.append(dict(mode=mode,kind='row count',lean=len(actual),sqlite=len(expected)))
            for i,(a,b) in enumerate(zip(actual,expected)):
                if a!=b:failures.append(dict(mode=mode,kind='stored value',expression=cases[i],lean=a,sqlite=b))
            queries=["SELECT id FROM t WHERE v LIKE 'a%' ORDER BY id;", "SELECT id,v GLOB '?*',v LIKE '%' FROM t ORDER BY id;",
                     "SELECT id FROM t WHERE v NOT LIKE 'a\\_%' ESCAPE '\\' ORDER BY id;",
                     "SELECT count(*) FROM t WHERE v LIKE 'a%';",
                     "UPDATE t SET v=upper(v) WHERE v GLOB '[a-z]*';SELECT id,hex(v) FROM t ORDER BY id;",
                     "DELETE FROM t WHERE v LIKE 'a%' ESCAPE 'x';SELECT id FROM t ORDER BY id;",
                     "SELECT 'abc' LIKE '%' ESCAPE '';", "SELECT NULL LIKE '%' ESCAPE '';",
                     "SELECT like(NULL,NULL,'ab');", "SELECT like('%',NULL,NULL);",
                     "SELECT glob();", "SELECT like('a');", "SELECT glob('a','a','!');",
                     "SELECT like('a','a',char(0));", "SELECT like('%','a',1.5);",
                     "SELECT like(replace(hex(zeroblob(25001)),'0','a'),NULL,NULL);",
                     "SELECT like(replace(hex(zeroblob(25001)),'0','a'),NULL,'');",
                     "SELECT like(replace(hex(zeroblob(25001)),'0','a'),'x') LIMIT 0;",
                     "SELECT 'a' LIKE missing ESCAPE 'x' WHERE 0;",
                     "SELECT like('a',abs(-9223372036854775808));"]
            matching_errors=0
            for sql in queries:
                files=[lean,pathlib.Path(str(lean)+'-wal')];before={str(f):f.read_bytes() for f in files if f.exists()}
                a,b=run(sql)
                if a.returncode and b.returncode:
                    matching_errors+=1
                    assert before=={str(f):f.read_bytes() for f in files if f.exists()},sql
                elif a.returncode or b.returncode or a.stdout!=b.stdout:
                    failures.append(dict(mode=mode,kind='CLI',sql=sql,lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=dict(code=b.returncode,stdout=b.stdout,stderr=b.stderr)))
            snapshot(lean,d/'lean-after.db');snapshot(oracle,d/'sqlite-after.db')
            phases.append(dict(mode=mode,requested_values=len(cases),stored_values=len(actual),queries=len(queries),matching_errors=matching_errors))
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
