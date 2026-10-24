#!/usr/bin/env python3
"""Compare SQL LIMIT/OFFSET slicing, DISTINCT, skipped expressions and binding.

Uses independent databases and compares result order and rejection status.
All counterexamples remain in the report, including syntax rejected by the
certified grammar. This suite does not represent whole-SQLite coverage.
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
    p.add_argument('--seed',type=int,default=353530)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed)
    setup=['CREATE TABLE t(id INTEGER PRIMARY KEY,v,b INTEGER);','BEGIN;']
    for i in range(1,41):
        setup.append(f"INSERT INTO t VALUES({i},{rng.choice(['NULL','0','1','1.0','2','-2'])},{rng.randrange(-10,11)});")
    setup+=['COMMIT;', 'CREATE TABLE empty(id INTEGER PRIMARY KEY,v);']
    queries=[]
    for _ in range(args.random_cases):
        distinct=rng.choice(['','DISTINCT ']);projection=rng.choice(['v','+v','id','id,v','id+1','hex(v)'])
        where=rng.choice(['',' WHERE id%2=0',' WHERE v+1>0',' WHERE id<0'])
        ordering=rng.choice(['',' ORDER BY id',' ORDER BY id DESC',' ORDER BY b DESC'])
        limit=rng.choice([0,1,2,5,50,2147483648,-1,-5]);offset=rng.choice([0,1,2,10,50,-1,-5])
        tail=rng.choice([f'LIMIT {limit} OFFSET {offset}',f'LIMIT {offset},{limit}'])
        queries.append(f'SELECT {distinct}{projection} FROM t{where}{ordering} {tail};')
    queries += [
        'SELECT id FROM t LIMIT 0 OFFSET NULL;',
        "SELECT id FROM t LIMIT 0 OFFSET 'ignored';",
        'SELECT id FROM t LIMIT NULL,0;',
        'SELECT id FROM t LIMIT 9223372036854775808,0;',
        'SELECT id FROM t LIMIT TRUE OFFSET FALSE;',
        'SELECT id FROM t LIMIT 0 OFFSET unknown_function();',
        'SELECT id FROM t LIMIT 0 OFFSET 9223372036854775808;',
        'SELECT id FROM t LIMIT 0 OFFSET -9223372036854775809;',
        'SELECT id FROM t LIMIT 1 OFFSET 0;', 'SELECT id FROM t LIMIT -1 OFFSET 1;',
        'SELECT id FROM t LIMIT 1 OFFSET -1;', 'SELECT id FROM t LIMIT 1,2;',
        'SELECT id FROM t LIMIT +1 OFFSET +1;', 'SELECT id FROM t LIMIT 9223372036854775808;',
        'SELECT id FROM t LIMIT -9223372036854775809;', 'SELECT id FROM t LIMIT 1 OFFSET 9223372036854775808;',
        'SELECT missing FROM t LIMIT 0 OFFSET 5;', 'SELECT missing FROM empty LIMIT 1 OFFSET 5;',
        'SELECT abs(-9223372036854775808) FROM t LIMIT 0 OFFSET 1;',
        'SELECT abs(-9223372036854775808) FROM t LIMIT 1 OFFSET 50;',
        'SELECT abs(-9223372036854775808) FROM t ORDER BY id LIMIT 1 OFFSET 50;',
        'SELECT abs(-9223372036854775808) FROM t LIMIT 1 OFFSET 1;',
        'SELECT DISTINCT abs(-9223372036854775808) FROM t LIMIT 1 OFFSET 50;',
        'SELECT id FROM t WHERE abs(-9223372036854775808) LIMIT 0 OFFSET 5;',
        'SELECT id FROM t WHERE abs(-9223372036854775808) LIMIT 1 OFFSET 50;',
    ]
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-limit-offset-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            d=pathlib.Path(tmp)/mode;d.mkdir()
            def run(sql):
                q=d/'query.sql';q.write_text(sql)
                a=subprocess.run([str(args.lean),mode,str(d/'lean.db'),str(q)],text=True,capture_output=True,timeout=120)
                b=subprocess.run([args.sqlite,'-batch','-bail',str(d/'sqlite.db')],input=sql,text=True,capture_output=True,timeout=120)
                return a,b
            a,b=run('\n'.join(setup));assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            files=[d/'lean.db',d/'lean.db-wal'];before={str(f):f.read_bytes() for f in files if f.exists()}
            matching_errors=0;rows=0
            for q in queries:
                a,b=run(q)
                same=(a.returncode==b.returncode==0 and a.stdout==b.stdout) or (a.returncode!=0 and b.returncode!=0)
                if not same: failures.append(dict(mode=mode,sql=q,lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=dict(code=b.returncode,stdout=b.stdout,stderr=b.stderr)))
                elif a.returncode: matching_errors+=1
                rows+=len(a.stdout.splitlines())
            assert before=={str(f):f.read_bytes() for f in files if f.exists()}
            phases.append(dict(mode=mode,queries=len(queries),result_rows=rows,matching_errors=matching_errors))
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


if __name__=='__main__': raise SystemExit(main())
