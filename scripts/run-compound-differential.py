#!/usr/bin/env python3
"""Independent production-file SQL compound comparison with pinned SQLite.

Exact CLI row/multiplicity/representative comparison for numeric and UTF-8 TEXT
values, including empty arms, mixed operators and persisted table inputs.
Typed Core tests separately cover BLOB/TEXT separation. This is not a complete
SQL compatibility measure or a binary64-bit comparison of SELECT outputs.
"""
import argparse
import hashlib
import json
import pathlib
import random
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]


def run(args, cwd, sql):
    source = cwd / 'query.sql'
    source.write_text(sql)
    lean = subprocess.run([str(args.lean), '--verified-file', str(cwd/'lean.db'), str(source)],
                          text=True, capture_output=True, timeout=180)
    sqlite = subprocess.run([args.sqlite, '-batch', '-bail', str(cwd/'sqlite.db')],
                            input=sql, text=True, capture_output=True, timeout=180)
    return lean, sqlite


def marked(stdout):
    result, key = {}, None
    for line in stdout.splitlines():
        if line.startswith('@@case:'):
            key = int(line.removeprefix('@@case:'))
            result[key] = []
        else:
            assert key is not None, line
            result[key].append(line)
    return result


def cases(seed, count):
    rng = random.Random(seed)
    values = ['NULL', '0', '0.0', '-0.0', '1', '1.0', '-1', '-1.0', '1.5', "'1'", "''", "'z'", "'Á'",
              '9007199254740993', '9007199254740992.0', '-9223372036854775808',
              '-9223372036854775808.0', '9223372036854775807', '9223372036854775808.0',
              '1e999', '-1e999', '5e-324']
    values += [str(rng.randrange(-(2**63),2**63)) for _ in range(16)]
    values += [repr(float(v)) for v in values[-16:]]
    ops = ['UNION', 'UNION ALL', 'INTERSECT', 'EXCEPT']
    queries = [f'SELECT {a} {op} SELECT {b};' for a,b in [('1','1.0'),('1.0','1'),('NULL','NULL'),("'1'",'1')]
               for op in ops]
    for _ in range(count):
        width = rng.randint(1,3)
        arms = ['SELECT '+','.join(rng.choices(values,k=width)) + (' WHERE 0' if rng.randrange(8)==0 else '')
                for _ in range(rng.randint(2,5))]
        query = arms[0]
        for arm in arms[1:]:
            query += ' '+rng.choice(ops)+' '+arm
        queries.append(query+';')
    setup = []
    for table in ['a','b']:
        setup += [f'CREATE TABLE {table}(id INTEGER PRIMARY KEY,v,tag TEXT);', 'BEGIN;']
        for i in range(1,61):
            setup.append(f"INSERT INTO {table} VALUES({i},{rng.choice(values)},'{rng.choice(['x','y','z'])}');")
        setup += ['COMMIT;']
    for op in ops:
        for left,right in [('v','v'), ('v,tag','v,tag'), ('tag,v','tag,v'), ('+v','+v')]:
            for where in ['', ' WHERE id<0', ' WHERE id<=20', ' WHERE id>40']:
                queries.append(f'SELECT {left} FROM a{where} {op} SELECT {right} FROM b;')
    return '\n'.join(setup),queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default='/usr/bin/sqlite3')
    p.add_argument('--seed',type=int,default=353440)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args()
    setup,queries=cases(args.seed,args.random_cases)
    with tempfile.TemporaryDirectory(prefix='sqleanite-compound-') as tmp:
        cwd=pathlib.Path(tmp)
        actual,expected=run(args,cwd,setup)
        assert actual.returncode==expected.returncode==0,(actual.stderr,expected.stderr)
        before=(cwd/'lean.db').read_bytes()
        source='\n'.join(f"SELECT '@@case:{i}';\n{q}" for i,q in enumerate(queries))
        actual,expected=run(args,cwd,source)
        assert actual.returncode==expected.returncode==0,(actual.stderr,expected.stderr)
        actual,expected=marked(actual.stdout),marked(expected.stdout)
        assert set(actual)==set(expected)==set(range(len(queries)))
        failures=[dict(sql=q,lean=actual[i],sqlite=expected[i]) for i,q in enumerate(queries) if actual[i]!=expected[i]]
        assert (cwd/'lean.db').read_bytes()==before,'compound SELECT modified database'
        errors=['SELECT 1 UNION SELECT 1,2;', 'SELECT 1 WHERE 0 INTERSECT SELECT missing;',
                'SELECT 1 UNION SELECT abs(-9223372036854775808);']
        for query in errors:
            a,b=run(args,cwd,query)
            assert a.returncode!=0 and b.returncode!=0,(query,a.stdout,b.stdout)
            assert (cwd/'lean.db').read_bytes()==before
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,queries=len(queries),result_rows=sum(map(len,actual.values())),
                failures=failures,matching_errors=len(errors),implementation_sha256=digest.hexdigest(),
                executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
                harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),
                comparison='CLI multiplicity, ordering and numeric/TEXT representative rendering; unchanged persisted state')
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__':
    raise SystemExit(main())
