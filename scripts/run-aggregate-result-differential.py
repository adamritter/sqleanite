#!/usr/bin/env python3
"""Differential checks for scalar results containing aggregates and no-FROM aggregates.

Compare exact CLI bytes, explicit typeof results, and success/rejection status
against the pinned SQLite executable, on independent database images in both
file modes. Reads must preserve every main/WAL byte. Error wording is not
compared. This suite covers ordinary aggregates without GROUP BY, HAVING,
aggregate ORDER BY, bare source-column results or subqueries. No mismatches
are filtered or normalized.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', type=pathlib.Path, default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite', default=os.environ.get('SQLITE3_BIN', '/usr/bin/sqlite3'))
    p.add_argument('--seed', type=int, default=353620)
    p.add_argument('--random-cases', type=int, default=200)
    p.add_argument('--output', type=pathlib.Path)
    args = p.parse_args()
    rng = random.Random(args.seed)
    pool = ['NULL', '0', '0.0', '-0.0', '1', '1.0', '-2', '2.5', '3', "'1'", "'1.0'", "'xyz'", "X'31'", '1e100', '5e-324']
    setup = ['CREATE TABLE t(id INTEGER PRIMARY KEY,v,w INTEGER);', 'BEGIN;']
    for i in range(1, 73):
        setup.append(f'INSERT INTO t VALUES({i},{rng.choice(pool)},{rng.randrange(-10,11)});')
    setup += ['COMMIT;', 'CREATE TABLE empty(id INTEGER PRIMARY KEY,v,w);',
              'CREATE TABLE ov(id INTEGER PRIMARY KEY,v);INSERT INTO ov VALUES(1,9223372036854775807),(2,1);']
    functions = ['count', 'sum', 'avg', 'total', 'min', 'max']
    arguments = ['v', '+v', 'v+1', 'v*2', 'w', 'w%3', 'CASE WHEN w>0 THEN v ELSE NULL END', 'length(v)', 'id IN (1,2,3)', 'id%4', '1', 'NULL']
    def term():
        if rng.randrange(8) == 0:
            return 'count(*)'
        return f"{rng.choice(functions)}({rng.choice(['', 'DISTINCT '])}{rng.choice(arguments)})"
    def wrap(a, b):
        return rng.choice([f'{a}+{b}', f'{a}/{b}', f'coalesce({a},{b})', f'round({a},2)',
                           f'typeof({a})', f'quote({a})', f'abs({a})', f'{a} IS NULL',
                           f'{a} IN (NULL,{b},0)', f'CASE WHEN {a}>0 THEN {b} ELSE -7 END',
                           f'{a}||{b}', f'length({a})', f'min({a},{b})', f'0 AND {a}',
                           f'{a}="1"', f'{a} LIKE \'%1%\'', f'CAST({a} AS TEXT)'])
    queries = []
    for _ in range(args.random_cases):
        a, b = term(), term()
        expr = wrap(a, b)
        if rng.randrange(3) == 0:
            expr = wrap(expr, term())
        projections = ','.join([expr, f'typeof({expr})', rng.choice(['42', "'x'", term()])])
        where = rng.choice(['', ' WHERE v+1>2', ' WHERE w%3=1', ' WHERE id IN (1,2,3,50)',
                            ' WHERE id<0', ' WHERE v IS NULL', ' WHERE w BETWEEN -3 AND 3'])
        tail = rng.choice(['', ' LIMIT 0', ' LIMIT 1 OFFSET 0', ' LIMIT -1 OFFSET 1', ' LIMIT 0 OFFSET NULL'])
        queries.append(f"SELECT {rng.choice(['','DISTINCT '])}{projections} FROM t{where}{tail};")
    for expression in ['count(*)', 'count()', 'count(NULL)', 'sum(7)', 'avg(7)', 'total(7)',
                       'min(7)', 'max(7)', 'count(DISTINCT 1)', 'count(*)+sum(2)',
                       'coalesce(sum(NULL),count(*))', 'round(avg(1.25),1)',
                       "sum('12xyz')", "total(X'3132')", 'typeof(sum(1))',
                       'sum(abs(-9223372036854775808))', 'count(*)+abs(-9223372036854775808)']:
        for where in ['', ' WHERE 0', ' WHERE NULL', ' WHERE 1']:
            for tail in ['', ' LIMIT 0', ' LIMIT 1 OFFSET 1']:
                queries.append(f'SELECT {expression}{where}{tail};')
    for table in ['t', 'empty']:
        for expr in ['count(*)+1', '0 AND sum(v)', 'CASE WHEN 0 THEN sum(v) ELSE count(*) END',
                     'count(*)+abs(-9223372036854775808)', '0 AND count(abs(-9223372036854775808))',
                     'count(*)+missing', 'count(*)+unknown_function()', 'count(sum(v))+1',
                     'coalesce(sum(*),0)', 'count(DISTINCT v,w)+1', 'count(unknown.v)+1']:
            for tail in ['', ' LIMIT 0', ' LIMIT 1 OFFSET 1']:
                queries.append(f'SELECT {expr} FROM {table}{tail};')
    for expr in ['sum(v)+abs(-9223372036854775808)', 'CASE WHEN 0 THEN sum(v) ELSE 1 END',
                 '1 OR sum(v)', '0 AND sum(v)', 'count(*)+sum(v)']:
        for tail in ['', ' LIMIT 0', ' LIMIT 1 OFFSET 1']:
            queries.append(f'SELECT {expr} FROM ov{tail};')
    for expr in ['count(missing)+1', 'sum(rowid)+1', 'count(*)+missing',
                 'count(*)+unknown_function()', 'count(sum(1))+1', 'sum(*)+1']:
        for tail in ['', ' LIMIT 0', ' LIMIT 1 OFFSET 1']:
            queries.append(f'SELECT {expr}{tail};')
    queries += ['SELECT sum(x.v)+count(*),42 FROM t AS x WHERE x.w>0;',
                'SELECT sum(t.v)+count(*) FROM t AS x LIMIT 0;',
                'SELECT 0 AND count(missing) FROM empty;',
                'SELECT count(*)+1 WHERE missing;',
                'SELECT count(*)+1 WHERE abs(-9223372036854775808) LIMIT 0;']
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-aggregate-results-') as tmp:
        for mode in ['--verified-file', '--verified-wal-file']:
            d = pathlib.Path(tmp)/mode
            d.mkdir()
            def run(sql):
                q = d/'query.sql'
                q.write_text(sql)
                a = subprocess.run([str(args.lean), mode, str(d/'lean.db'), str(q)], capture_output=True, timeout=120)
                b = subprocess.run([args.sqlite, '-batch', '-bail', str(d/'sqlite.db')], input=sql.encode(), capture_output=True, timeout=120)
                return a, b
            a, b = run('\n'.join(setup))
            assert a.returncode == b.returncode == 0, (a.stderr, b.stderr)
            files = [d/'lean.db', d/'lean.db-wal', d/'sqlite.db', d/'sqlite.db-wal']
            def snapshot():
                return {str(f): f.read_bytes() for f in files if f.exists()}
            before = snapshot()
            matching_errors, rows = 0, 0
            for sql in queries:
                a, b = run(sql)
                same = (a.returncode == b.returncode == 0 and a.stdout == b.stdout) or (a.returncode != 0 and b.returncode != 0)
                if not same:
                    def outcome(r):
                        return dict(code=r.returncode, stdout=r.stdout.decode('latin-1'), stderr=r.stderr.decode('latin-1'))
                    failures.append(dict(mode=mode, sql=sql, lean=outcome(a), sqlite=outcome(b)))
                elif a.returncode:
                    matching_errors += 1
                rows += len(a.stdout.splitlines())
            assert before == snapshot(), 'aggregate reads changed database or WAL bytes'
            phases.append(dict(mode=mode, queries=len(queries), result_rows=rows, matching_errors=matching_errors))
    digest = hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean')) + [ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report = dict(seed=args.seed, random_cases=args.random_cases, phases=phases, failures=failures,
                  implementation_sha256=digest.hexdigest(), executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
                  harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                  sqlite_version=subprocess.check_output([args.sqlite, '--version'], text=True).strip(), comparison=__doc__.strip())
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
