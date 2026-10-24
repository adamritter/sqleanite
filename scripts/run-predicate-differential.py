#!/usr/bin/env python3
"""Differential SQL WHERE scans: row expressions, truth, errors and LIMIT.

Uses independent persistent files and checks CLI values/multiplicities, not
binary64 output bits or full SQLite planner/error-order equivalence.
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
    setup=['CREATE TABLE t(id INTEGER PRIMARY KEY,v,w,n NUMERIC,s TEXT);','BEGIN;']
    for i in range(1,151):
        setup.append(f"INSERT INTO t VALUES({i},{rng.choice(pool)},{rng.choice(pool)},{rng.choice(pool)},{rng.choice(pool)});")
    setup += ['COMMIT;', 'CREATE TABLE empty(id INTEGER PRIMARY KEY,v,w,n NUMERIC,s TEXT);']
    conditions=['v','w','n','s','id+1>2','v+w','coalesce(n,0)','v=w','n=s','s=CAST(n AS INTEGER)',
        'typeof(v)=typeof(w)',"length(s)>2",'abs(CAST(n AS REAL))>1','sign(n)',"instr(s,'1')",'v IS w',
        'v IS NOT w','v BETWEEN w AND n','NOT (v AND w)','NOT (v OR w)','v AND NULL',
        'NULL AND v','v OR NULL','NULL OR v','v AND w OR n','v OR w AND n',
        '(v AND w) IS NULL','CASE WHEN v THEN w ELSE n END',"n='1'", "+n='1'",
        '1.0','0.0',"'1x'", "'x'",'NULL','NULL AND abs(-9223372036854775808)',
        '1 OR abs(-9223372036854775808)','0 AND abs(-9223372036854775808)']
    def expression(depth):
        if depth==0:
            return rng.choice(['v','w','n','s','NULL','0','1','0.0',"'x'", "'1x'",'id%3',
                'coalesce(n,0)','sign(v)','v=w','n=s','n=CAST(s AS REAL)','v IS NULL','length(s)'])
        if rng.randrange(3)==0:
            return f'NOT ({expression(depth-1)})'
        return f'({expression(depth-1)}) {rng.choice(["AND","OR","=","IS","<","+","-"])} ({expression(depth-1)})'
    conditions += [expression(rng.randrange(1,4)) for _ in range(count)]
    queries=[]
    for condition in conditions:
        direction=rng.choice(['ASC','DESC'])
        limit=rng.choice(['',' LIMIT 0',' LIMIT 1',' LIMIT 3',' LIMIT 50'])
        queries.append(f'SELECT id,typeof(v),hex(v),hex(quote(n)) FROM t WHERE {condition} ORDER BY id {direction}{limit};')
    for condition in conditions[:30]:
        queries.append(f'SELECT DISTINCT v FROM t WHERE {condition} ORDER BY v;')
        queries.append(f'SELECT id FROM empty WHERE {condition} ORDER BY id;')
    queries += [
        'SELECT 1 WHERE 0 AND abs(-9223372036854775808);',
        'SELECT 1 WHERE NULL AND abs(-9223372036854775808);',
        'SELECT 1 WHERE 1 OR abs(-9223372036854775808);',
        'SELECT id FROM t WHERE id=1 OR abs(-9223372036854775808) ORDER BY id LIMIT 1;',
        'SELECT id FROM t WHERE id=150 OR abs(-9223372036854775808) ORDER BY id DESC LIMIT 1;',
        'SELECT abs(-9223372036854775808) FROM t WHERE id+0 LIMIT 0;',
        'SELECT id FROM t WHERE abs(-9223372036854775808) LIMIT 0;',
        'SELECT id FROM t WHERE abs(-9223372036854775808) ORDER BY v LIMIT 0;',
        'SELECT DISTINCT id%2 FROM t WHERE id<3 OR abs(-9223372036854775808) ORDER BY id LIMIT 2;',
        'SELECT a.id+1 FROM t AS a WHERE a.id+1>149 ORDER BY a.id;',
    ]
    return '\n'.join(setup),queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default='/usr/bin/sqlite3')
    p.add_argument('--seed',type=int,default=353460)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args()
    setup,queries=cases(args.seed,args.random_cases)
    phases=[];failures=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-predicate-') as tmp:
        cwd=pathlib.Path(tmp)
        a,b=run(args,cwd,setup)
        assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
        for phase,index in [('unindexed',''),('indexed','CREATE INDEX ti ON t(n); CREATE INDEX ts ON t(s);')]:
            if index:
                a,b=run(args,cwd,index)
                assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            before=(cwd/'lean.db').read_bytes()
            sql='\n'.join(f"SELECT '@@case:{i}';\n{q}" for i,q in enumerate(queries))
            a,b=run(args,cwd,sql)
            assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            actual,expected=marked(a.stdout),marked(b.stdout)
            assert set(actual)==set(expected)==set(range(len(queries)))
            failures += [dict(phase=phase,sql=q,lean=actual[i],sqlite=expected[i]) for i,q in enumerate(queries) if actual[i]!=expected[i]]
            assert (cwd/'lean.db').read_bytes()==before
            phases.append(dict(name=phase,queries=len(queries),result_rows=sum(map(len,actual.values()))))
        known=[]
        for q in ['SELECT id FROM t WHERE id=1 OR abs(-9223372036854775808) LIMIT 1;',
                  'SELECT DISTINCT id%2 FROM t WHERE id<3 OR abs(-9223372036854775808) LIMIT 2;']:
            a,b=run(args,cwd,q)
            known.append(dict(sql=q,lean=dict(exit_code=a.returncode,stdout=a.stdout,stderr=a.stderr),
                sqlite=dict(exit_code=b.returncode,stdout=b.stdout,stderr=b.stderr),
                matches=(a.returncode==b.returncode and a.stdout==b.stdout),
                scope='Planner-dependent scan order without ORDER BY; retained diagnostic, not a passing conformance case.'))
        errors=['SELECT id FROM t WHERE abs(-9223372036854775808) AND 0;',
            'SELECT id FROM empty WHERE abs(-9223372036854775808);',
            'SELECT id FROM t WHERE id<0 AND abs(-9223372036854775808);',
            'SELECT 1 WHERE abs(-9223372036854775808) AND 0;',
            'SELECT id FROM empty WHERE missing+1;', 'SELECT id FROM t WHERE missing+1 LIMIT 0;',
            'SELECT id FROM t WHERE 0 OR unknown_function();', 'SELECT id FROM t WHERE wrong.id+1;',
            'SELECT t.id FROM t AS a WHERE a.id+1;', 'SELECT id FROM t WHERE id=1 OR abs(-9223372036854775808);',
            'SELECT id FROM t WHERE NOT (NULL AND abs(-9223372036854775808));',
            'SELECT missing FROM t WHERE 0;', 'SELECT id FROM t WHERE 1 ORDER BY missing LIMIT 0;']
        for q in errors:
            a,b=run(args,cwd,q)
            assert a.returncode!=0 and b.returncode!=0,(q,a.stdout,b.stdout)
            assert (cwd/'lean.db').read_bytes()==before
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,queries=sum(p['queries'] for p in phases),phases=phases,
                failures=failures,matching_errors=len(errors),planner_order_diagnostics=known,implementation_sha256=digest.hexdigest(),
                executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
                harness_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [pathlib.Path(__file__),HELPER]},
                sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),
                comparison='CLI rows, multiplicities, truth, LIMIT error suppression, binding and unchanged file; indexed/unindexed')
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__':
    raise SystemExit(main())
