#!/usr/bin/env python3
"""Compare DISTINCT source representatives, source ordering and LIMIT.

Includes ordinary and expression projections, primary-key scan directions,
post-DISTINCT sorting, both production file modes and reopen/index paths.
This is query-output and read-preservation evidence, not a coverage percentage.
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


def run(args, directory, mode, sql):
    source = directory / 'query.sql'
    source.write_text(sql)
    a = subprocess.run([str(args.lean), mode, str(directory/'lean.db'), str(source)],
                       capture_output=True, text=True, timeout=180)
    b = subprocess.run([args.sqlite, '-batch', '-bail', str(directory/'sqlite.db')],
                       input=sql, capture_output=True, text=True, timeout=180)
    assert a.returncode == b.returncode == 0, (a.stderr, b.stderr)
    return a.stdout, b.stdout


def split(text):
    rows = {}
    key = None
    for line in text.splitlines():
        if line.startswith('@@case:'):
            key = int(line[7:])
            rows[key] = []
        else:
            assert key is not None
            rows[key].append(line)
    return rows


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', type=pathlib.Path, default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite', default=os.environ.get('SQLITE3_BIN', '/usr/bin/sqlite3'))
    p.add_argument('--seed', type=int, default=353490)
    p.add_argument('--random-cases', type=int, default=50)
    p.add_argument('--output', type=pathlib.Path)
    args = p.parse_args()
    rng = random.Random(args.seed)
    setup = ['CREATE TABLE t(id INTEGER PRIMARY KEY,g INTEGER,v,b INTEGER);', 'BEGIN;']
    queries = []
    for group in range(args.random_cases):
        for index in range(15):
            v = rng.choice(['NULL', '0', '1', '1.0', '2', '2.0', "'1'", "''", '-1'])
            setup.append(f'INSERT INTO t VALUES({group*15+index+1},{group},{v},{rng.randrange(-5,6)});')
        for projection in ['v', '+v', 'v,+v']:
            for ordering in ['b', 'b DESC', 'b DESC,id', 'id', 'id DESC']:
                for limit in ['', ' LIMIT 0', ' LIMIT 1', ' LIMIT 4']:
                    queries.append(f'SELECT DISTINCT {projection} FROM t WHERE g={group} ORDER BY {ordering}{limit};')
    setup.append('COMMIT;')
    marked = '\n'.join(f"SELECT '@@case:{i}';\n{sql}" for i, sql in enumerate(queries))
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-distinct-order-') as tmp:
        for mode in ['--verified-file', '--verified-wal-file']:
            directory = pathlib.Path(tmp)/mode
            directory.mkdir()
            run(args, directory, mode, '\n'.join(setup))
            for indexed in [False, True]:
                if indexed:
                    run(args, directory, mode, 'CREATE INDEX tg ON t(g);')
                files = [directory/'lean.db', directory/'lean.db-wal']
                before = {str(f): f.read_bytes() for f in files if f.exists()}
                actual, expected = map(split, run(args, directory, mode, marked))
                assert set(actual) == set(expected) == set(range(len(queries)))
                for i, sql in enumerate(queries):
                    if actual[i] != expected[i]:
                        failures.append(dict(mode=mode, indexed=indexed, sql=sql,
                                             lean=actual[i], sqlite=expected[i]))
                assert before == {str(f): f.read_bytes() for f in files if f.exists()}
                phases.append(dict(mode=mode, indexed=indexed, queries=len(queries),
                                   result_rows=sum(map(len, actual.values()))))
    digest = hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report = dict(seed=args.seed, random_cases=args.random_cases, phases=phases,
                  queries=sum(x['queries'] for x in phases), failures=failures,
                  implementation_sha256=digest.hexdigest(),
                  executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
                  harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                  sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),
                  comparison=__doc__.strip())
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
