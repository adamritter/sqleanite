#!/usr/bin/env python3
"""SQLite IN/NOT IN value, affinity, NULL, binding and error-order comparisons.

Exercises the production file reader with constant and row expressions, WHERE,
empty lists and deterministic RHS materialization. Every query is compared;
failures are retained, never silently omitted from passing counts.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353520)
    p.add_argument('--random-cases',type=int,default=150)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed)
    pool=['NULL','0','0.0','1','1.0','-2','2.5',"'1'","'x'","''","X'31'",'9007199254740993','9007199254740992.0']
    setup=['CREATE TABLE t(id INTEGER PRIMARY KEY,u,n NUMERIC,s TEXT,r REAL);','BEGIN;']
    for i in range(1,51):
        setup.append(f"INSERT INTO t VALUES({i},{rng.choice(pool)},{rng.choice(pool)},{rng.choice(pool)},{rng.choice(pool)});")
    setup+=['COMMIT;','CREATE INDEX tn ON t(n);','CREATE TABLE empty(id INTEGER PRIMARY KEY,v);']
    queries=[]
    lefts=['u','n','s','r','id','+n','CAST(u AS NUMERIC)','NULL','1',"'1'"]
    rights=pool+['u','n','s','r','id','CAST(u AS TEXT)','coalesce(n,u)','upper(s)']
    for _ in range(args.random_cases):
        expression=f"{rng.choice(lefts)} {rng.choice(['IN','NOT IN'])} ({','.join(rng.choices(rights,k=rng.randrange(7)))})"
        queries += [f'SELECT id,typeof({expression}),quote({expression}) FROM t ORDER BY id;',
                    f'SELECT id FROM t WHERE {expression} ORDER BY id {rng.choice(["ASC","DESC"])} LIMIT {rng.randrange(0,60)};']
    expressions=['NULL IN ()','NULL NOT IN ()','missing IN ()','CAST(missing AS INTEGER) IN ()',
        'unknown_function() IN ()','(missing+abs(1)) IN ()',
        'abs(-9223372036854775808) IN ()','abs(-9223372036854775808) NOT IN ()',
        '1 IN (1,abs(-9223372036854775808))','1 IN (1,2,abs(-9223372036854775808))',
        'NULL IN (abs(-9223372036854775808),1)','NULL NOT IN (1,NULL)',
        '1 IN (1,missing)','1 IN (1,2,missing)',
        "'1' IN (CAST('1' AS NUMERIC))","CAST('1' AS NUMERIC) IN ('1',NULL)",
        '1 IN (1,2,abs(-9223372036854775808)+id)',
        'id IN (id,abs(-9223372036854775808))','id NOT IN (id,abs(-9223372036854775808))']
    for expression in expressions:
        queries += [f'SELECT {expression} FROM t ORDER BY id LIMIT 1;',
                    f'SELECT id FROM t WHERE {expression} ORDER BY id LIMIT 1;',
                    f'SELECT {expression} FROM empty LIMIT 0;']
    queries += [
        'SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE id IN (1,2,abs(-9223372036854775808)) ORDER BY id LIMIT 1;',
        'SELECT id FROM empty WHERE id IN (1,abs(-9223372036854775808));',
        'SELECT id FROM empty WHERE id IN (1,2,abs(-9223372036854775808));',
        'SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) AND id=1 ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE id=1 AND id IN (1,abs(-9223372036854775808),id) ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE id=1 AND n IN (1,abs(-9223372036854775808),id) ORDER BY id LIMIT 1;',
        'SELECT id FROM empty WHERE id=1 AND id IN (1,abs(-9223372036854775808),id);',
        'SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) AND id IN (1) ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE id IN (1) AND id IN (1,abs(-9223372036854775808)) ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) AND rowid=1 ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) AND id>0 ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE n IN (1,abs(-9223372036854775808)) ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE n IN (1,abs(-9223372036854775808)) AND id=1 ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE id IN (1,abs(-9223372036854775808)) AND 0;',
        'SELECT id FROM t WHERE u IN (u,abs(-9223372036854775808)) ORDER BY id LIMIT 1;',
    ]
    failures=[];row_count=0;matching_errors=0
    with tempfile.TemporaryDirectory(prefix='sqleanite-in-list-') as tmp:
        d=pathlib.Path(tmp)
        def run(sql):
            q=d/'query.sql';q.write_text(sql)
            a=subprocess.run([str(args.lean),'--verified-file',str(d/'lean.db'),str(q)],text=True,capture_output=True,timeout=120)
            b=subprocess.run([args.sqlite,'-batch','-bail',str(d/'sqlite.db')],input=sql,text=True,capture_output=True,timeout=120)
            return a,b
        a,b=run('\n'.join(setup));assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
        before=(d/'lean.db').read_bytes()
        for query in queries:
            a,b=run(query)
            same=(a.returncode==b.returncode==0 and a.stdout==b.stdout) or (a.returncode!=0 and b.returncode!=0)
            if not same: failures.append(dict(sql=query,lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=dict(code=b.returncode,stdout=b.stdout,stderr=b.stderr)))
            if same and a.returncode: matching_errors+=1
            row_count+=len(a.stdout.splitlines())
        assert (d/'lean.db').read_bytes()==before
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,queries=len(queries),matching_errors=matching_errors,result_rows=row_count,failures=failures,
        implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    if args.output: args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__': raise SystemExit(main())
