#!/usr/bin/env python3
"""Compare numeric GROUP BY and original aggregate representatives with SQLite.

Checks grouping equality, sorted group presentation, exact integer aggregates,
MIN/MAX tie storage classes, duplicate accumulator expressions, empty inputs,
and persisted-file preservation. General aggregate expressions and REAL SUM
are outside this current suite, not counted as supported cases.
"""
import argparse
import hashlib
import json
import pathlib
import random
import runpy
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]
HELPER=ROOT/'scripts/run-compound-differential.py'
helpers=runpy.run_path(str(HELPER))
run,marked=helpers['run'],helpers['marked']


def cases(seed,count):
    rng=random.Random(seed)
    pool=['NULL','0','0.0','-0.0','1','1.0','-1','-1.0','1.5',"'1'", "''", "'Á'",
          '9007199254740992','9007199254740992.0','9007199254740993',
          '-9223372036854775808','-9223372036854775808.0','1e999','-1e999','5e-324']
    setup=['CREATE TABLE t(id INTEGER PRIMARY KEY,v,w,x INTEGER,y INTEGER,tag TEXT);','BEGIN;']
    for i in range(1,251):
        x=rng.choice(['NULL']+[str(rng.randrange(-20,21)) for _ in range(4)])
        y=rng.choice(['NULL']+[str(rng.randrange(-20,21)) for _ in range(4)])
        setup.append(f"INSERT INTO t VALUES({i},{rng.choice(pool)},{rng.choice(pool[:10])},{x},{y},'{rng.choice(['a','b','c'])}');")
    setup += ['COMMIT;', 'CREATE TABLE empty(id INTEGER PRIMARY KEY,v,w,x INTEGER,y INTEGER,tag TEXT);',
              'CREATE TABLE overflows(id INTEGER PRIMARY KEY,g,v INTEGER);',
              'INSERT INTO overflows VALUES(1,1,9223372036854775807),(2,1,1);']
    queries=[]
    aggregate=['count(*)','count(x)','count(v)','sum(x)','sum(y)','min(x)','max(x)','min(y)','max(y)','min(id)','max(id)']
    patterns=[['count(*)'],['min(x)'],['max(x)'],['min(x)','max(x)','min(x)'],
              ['max(x)','min(x)','max(x)'],['count(*)','count(x)','sum(x)','min(x)','max(x)']]
    for group in ['v','w','v,w','w,v','v,tag','v,v']:
        for aggs in patterns:
            for table in ['t','empty']:
                queries.append(f"SELECT {group},{','.join(aggs)} FROM {table} GROUP BY {group};")
    for _ in range(count):
        keys=rng.choice([['v'],['w'],['v','w'],['v','tag'],['w','v']])
        outputs=keys.copy()
        rng.shuffle(outputs)
        aggs=rng.choices(aggregate,k=rng.randrange(1,7))
        where=f' WHERE id<={rng.randrange(-1,300)}' if rng.randrange(2) else ''
        queries.append(f"SELECT {','.join(outputs+aggs)} FROM t{where} GROUP BY {','.join(keys)};")
    for aggregate in ['min','max']:
        for column in ['v','w','x','y']:
            for where in ['', ' WHERE id<0',' WHERE id<=30']:
                queries.append(f'SELECT {aggregate}({column}) FROM t{where};')
    return '\n'.join(setup),queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default='/usr/bin/sqlite3')
    p.add_argument('--seed',type=int,default=353450)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args()
    setup,queries=cases(args.seed,args.random_cases)
    with tempfile.TemporaryDirectory(prefix='sqleanite-group-') as tmp:
        cwd=pathlib.Path(tmp)
        a,b=run(args,cwd,setup)
        assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
        before=(cwd/'lean.db').read_bytes()
        sql='\n'.join(f"SELECT '@@case:{i}';\n{q}" for i,q in enumerate(queries))
        a,b=run(args,cwd,sql)
        assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
        actual,expected=marked(a.stdout),marked(b.stdout)
        assert set(actual)==set(expected)==set(range(len(queries)))
        failures=[dict(sql=q,lean=actual[i],sqlite=expected[i]) for i,q in enumerate(queries) if actual[i]!=expected[i]]
        assert (cwd/'lean.db').read_bytes()==before
        errors=['SELECT v,sum(missing) FROM empty GROUP BY v;',
                'SELECT v,count(*) FROM empty GROUP BY missing;',
                'SELECT g,sum(v) FROM overflows GROUP BY g;']
        for q in errors:
            a,b=run(args,cwd,q)
            assert a.returncode!=0 and b.returncode!=0,(q,a.stdout,b.stdout)
            assert (cwd/'lean.db').read_bytes()==before
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,queries=len(queries),result_rows=sum(map(len,actual.values())),
                failures=failures,matching_errors=len(errors),implementation_sha256=digest.hexdigest(),
                executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
                harness_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [pathlib.Path(__file__),HELPER]},
                sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),
                comparison='CLI group multiplicities, aggregate values, ordering and original numeric/TEXT representatives; unchanged file')
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__':
    raise SystemExit(main())
