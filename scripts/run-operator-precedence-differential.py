#!/usr/bin/env python3
"""Compare expression precedence and NULL-test spellings against pinned SQLite.

Exact CLI bytes and typeof values are compared on independent images in both
file modes. Generated operator pairs, NOT, BETWEEN, LIKE ESCAPE, and NULL-test
spellings are not filtered based on acceptance. Error wording is not compared.
No claim is made here about collations, JSON, subqueries, or boolean-name binding.
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
    p.add_argument('--seed', type=int, default=353630)
    p.add_argument('--repetitions', type=int, default=2)
    p.add_argument('--output', type=pathlib.Path)
    args = p.parse_args()
    rng = random.Random(args.seed)
    literals = ['-3', '-1', '0', '1', '2', '3', '0.5', 'NULL', "'1'", "'2'", "'x'", "X'31'"]
    ops = ['+', '-', '*', '/', '%', '||', '&', '|', '<<', '>>', '=', '!=', '<', '<=', '>', '>=', 'IS', 'IS NOT', 'AND', 'OR', 'LIKE', 'GLOB']
    cases = []
    def add(group, expression, source=''):
        cases.append((group, f'SELECT {expression},typeof({expression}){source};'))
    def arg():
        return '('+rng.choice(literals)+')'
    for _ in range(args.repetitions):
        for op in ops:
            for other in ops:
                add('binary-pair', f'{arg()} {op} {arg()} {other} {arg()}')
        for op in ops:
            add('not-prefix', f'NOT {arg()} {op} {arg()}')
            add('between-upper', f'{arg()} BETWEEN {arg()} AND {arg()} {op} {arg()}')
            add('between-lower', f'{arg()} BETWEEN {arg()} {op} {arg()} AND {arg()}')
            add('not-between-upper', f'{arg()} NOT BETWEEN {arg()} AND {arg()} {op} {arg()}')
            add('like-escape', f"'a' LIKE 'a' ESCAPE 'x' {op} {arg()}")
            add('not-like-escape', f"'a' NOT LIKE 'a' ESCAPE 'x' {op} {arg()}")
    for spelling in ['IS NULL', 'IS (NULL)', 'IS ((NULL))', 'IS NOT NULL', 'IS NOT (NULL)', 'ISNULL', 'NOTNULL', 'NOT NULL']:
        for value in literals:
            add('null-test', f'({value}) {spelling}')
            add('null-postfix', f'({value}) {spelling}+1')
        add('null-table', f'v {spelling}', ' FROM t ORDER BY id')
    for spelling in ['IS DISTINCT FROM', 'IS NOT DISTINCT FROM']:
        for value in literals:
            for other in ['NULL', '1', '2']:
                add('is-distinct', f'({value}) {spelling} ({other})')
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-operator-precedence-') as tmp:
        for mode in ['--verified-file', '--verified-wal-file']:
            d = pathlib.Path(tmp)/mode
            d.mkdir()
            def run(sql):
                q = d/'query.sql'
                q.write_text(sql)
                a = subprocess.run([str(args.lean), mode, str(d/'lean.db'), str(q)], capture_output=True, timeout=120)
                b = subprocess.run([args.sqlite, '-batch', '-bail', str(d/'sqlite.db')], input=sql.encode(), capture_output=True, timeout=120)
                return a, b
            a, b = run('CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,NULL),(2,1),(3,2);')
            assert a.returncode == b.returncode == 0, (a.stderr, b.stderr)
            files = [d/'lean.db', d/'lean.db-wal', d/'sqlite.db', d/'sqlite.db-wal']
            def snapshot():
                return {str(f): f.read_bytes() for f in files if f.exists()}
            before = snapshot()
            matching_errors = 0
            for group, sql in cases:
                a, b = run(sql)
                same = (a.returncode == b.returncode == 0 and a.stdout == b.stdout) or (a.returncode != 0 and b.returncode != 0)
                if not same:
                    def outcome(r):
                        return dict(code=r.returncode, stdout=r.stdout.decode('latin-1'), stderr=r.stderr.decode('latin-1'))
                    failures.append(dict(mode=mode, group=group, sql=sql, lean=outcome(a), sqlite=outcome(b)))
                elif a.returncode:
                    matching_errors += 1
            assert before == snapshot(), 'expression queries changed database or WAL bytes'
            phases.append(dict(mode=mode, queries=len(cases), matching_errors=matching_errors))
    digest = hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean')) + [ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report = dict(seed=args.seed, repetitions=args.repetitions, phases=phases, failures=failures,
                  implementation_sha256=digest.hexdigest(), executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
                  harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                  sqlite_version=subprocess.check_output([args.sqlite, '--version'], text=True).strip(), comparison=__doc__.strip())
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
