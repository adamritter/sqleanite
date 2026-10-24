#!/usr/bin/env python3
"""SQLite boolean keywords, IS truth tests, and shadowing by real column names.

Compare exact CLI bytes, explicit typeof results, and rejection status on
independent images in both file modes. Reads must preserve database/WAL bytes.
All generated failures are retained. This suite covers constant and single-table
expressions; it does not claim alias, join, grouping, or collation completeness.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import shutil
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', type=pathlib.Path, default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite', default=os.environ.get('SQLITE3_BIN', '/usr/bin/sqlite3'))
    p.add_argument('--seed', type=int, default=353640)
    p.add_argument('--random-cases', type=int, default=120)
    p.add_argument('--output', type=pathlib.Path)
    args = p.parse_args()
    rng = random.Random(args.seed)
    values = ['NULL', '0', '0.0', '1', '2', '-1', '0.5', "'0'", "'1'", "'2'", "'xyz'", "X'31'", "X'FF'", '1e999']
    setup = ['CREATE TABLE t(id INTEGER PRIMARY KEY,v);',
             'CREATE TABLE s(id INTEGER PRIMARY KEY,true TEXT,false INTEGER,v);',
             'CREATE TABLE empty(id INTEGER PRIMARY KEY,true,false,v);']
    for i in range(1, 25):
        setup += [f'INSERT INTO t VALUES({i},{rng.choice(values)});',
                  f'INSERT INTO s VALUES({i},{rng.choice(values)},{rng.choice(values)},{rng.choice(values)});']
    queries = []
    for value in values:
        for rhs in ['TRUE', 'FALSE', '(TRUE)', '((FALSE))', '+TRUE', 'TRUE+0', 'FALSE+1']:
            for op in ['IS', 'IS NOT', 'IS DISTINCT FROM', 'IS NOT DISTINCT FROM', '=']:
                e = f'({value}) {op} {rhs}'
                queries.append(f'SELECT {e},typeof({e});')
    for table in ['t', 's']:
        for expression in ['TRUE', 'FALSE', 'v IS TRUE', 'v IS (FALSE)', 'v IS NOT TRUE',
                           'v IS NOT ((FALSE))', 'v IS TRUE+0', 'v=TRUE', 'TRUE=v',
                           'CAST(TRUE AS TEXT)=v', 'TRUE AND FALSE', 'TRUE OR FALSE',
                           'NOT TRUE', 'v IN (TRUE,FALSE)', 'CASE TRUE WHEN v THEN 1 ELSE 2 END']:
            queries.append(f'SELECT id,{expression},typeof({expression}) FROM {table} ORDER BY id;')
            queries.append(f'SELECT id FROM {table} WHERE {expression} ORDER BY id;')
        queries += [f'SELECT sum(TRUE),sum(FALSE),count(TRUE),total(v IS FALSE) FROM {table};',
                    f'SELECT sum(v IS TRUE)+count(*) FROM {table};']
    for _ in range(args.random_cases):
        table = rng.choice(['t', 's'])
        expression = rng.choice(['v', 'TRUE', 'FALSE', 'v+TRUE', 'coalesce(v,FALSE)', 'abs(v)'])
        rhs = rng.choice(['TRUE', 'FALSE', '(TRUE)', '+FALSE', 'TRUE+0'])
        op = rng.choice(['IS', 'IS NOT', '=', '!=', '<', '>='])
        where = rng.choice(['', ' WHERE v IS TRUE', ' WHERE TRUE', ' WHERE FALSE', ' WHERE id=TRUE', ' WHERE id IN (TRUE,FALSE,7)'])
        queries.append(f'SELECT id,{expression} {op} {rhs} FROM {table}{where} ORDER BY id;')
    queries += ['SELECT TRUE,FALSE,typeof(TRUE),typeof(FALSE);',
                'SELECT FALSE AND abs(-9223372036854775808);',
                'SELECT TRUE OR abs(-9223372036854775808);',
                'SELECT FALSE AND missing;', 'SELECT TRUE OR unknown_function();',
                'SELECT TRUE() LIMIT 0;', 'SELECT __sqlean_boolean_true() LIMIT 0;',
                'SELECT true.foo;', 'SELECT count(*) WHERE FALSE;',
                'SELECT 1 LIMIT TRUE;', 'SELECT 1 LIMIT FALSE;',
                'SELECT s.true,s.false FROM s ORDER BY id;',
                'SELECT TRUE,FALSE,v IS TRUE FROM empty WHERE TRUE;',
                'SELECT sum(TRUE),count(FALSE) FROM empty;',
                'SELECT FALSE AND missing FROM empty LIMIT 0;']
    writes = [
        'UPDATE s SET v=TRUE WHERE id<10;',
        'UPDATE s SET true=FALSE WHERE v IS TRUE;',
        'UPDATE s SET false=TRUE WHERE id IN (TRUE,FALSE,7);',
        'UPDATE s SET v=CASE WHEN FALSE THEN TRUE ELSE v END;',
        'UPDATE s SET v=FALSE, false=TRUE WHERE id=2;',
        'DELETE FROM s WHERE TRUE;', 'DELETE FROM s WHERE FALSE;',
        'DELETE FROM s WHERE v IS TRUE;', 'DELETE FROM s WHERE id=TRUE;',
        'INSERT INTO s(true,false,v) VALUES(TRUE,FALSE,TRUE);',
        'INSERT INTO t(v) VALUES(TRUE),(FALSE);',
        'CREATE INDEX on_true ON s(TRUE); UPDATE s SET true=FALSE WHERE id=2;',
        'UPDATE s SET v=TRUE, false=abs(-9223372036854775808);',
        'UPDATE s SET v=missing WHERE FALSE;',
        'DELETE FROM s WHERE unknown_function() OR TRUE;']
    observation = ('SELECT id,true,typeof(true),false,typeof(false),quote(v),typeof(v) FROM s ORDER BY id;'
                   'SELECT id,quote(v),typeof(v) FROM t ORDER BY id;')
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-booleans-') as tmp:
        for mode in ['--verified-file', '--verified-wal-file']:
            d = pathlib.Path(tmp)/mode
            d.mkdir()
            def run(sql, location=None):
                base = location or d
                q = base/'query.sql'
                q.write_text(sql)
                a = subprocess.run([str(args.lean), mode, str(base/'lean.db'), str(q)], capture_output=True, timeout=120)
                b = subprocess.run([args.sqlite, '-batch', '-bail', str(base/'sqlite.db')], input=sql.encode(), capture_output=True, timeout=120)
                return a, b
            a, b = run('\n'.join(setup))
            assert a.returncode == b.returncode == 0, (a.stderr, b.stderr)
            files = [d/'lean.db', d/'lean.db-wal', d/'sqlite.db', d/'sqlite.db-wal']
            def snapshot():
                return {str(f): f.read_bytes() for f in files if f.exists()}
            before = snapshot()
            matching_errors = 0
            for sql in queries:
                a, b = run(sql)
                same = (a.returncode == b.returncode == 0 and a.stdout == b.stdout) or (a.returncode != 0 and b.returncode != 0)
                if not same:
                    def outcome(r):
                        return dict(code=r.returncode, stdout=r.stdout.decode('latin-1'), stderr=r.stderr.decode('latin-1'))
                    failures.append(dict(mode=mode, sql=sql, lean=outcome(a), sqlite=outcome(b)))
                elif a.returncode:
                    matching_errors += 1
            assert before == snapshot(), 'boolean expression reads changed database/WAL bytes'
            for index, sql in enumerate(writes):
                directory = d/f'write-{index}'
                directory.mkdir()
                for f in files:
                    if f.exists():
                        shutil.copyfile(f, directory/f.name)
                a, b = run(sql+observation, directory)
                same = (a.returncode == b.returncode == 0 and a.stdout == b.stdout) or (a.returncode != 0 and b.returncode != 0)
                if not same:
                    failures.append(dict(mode=mode, sql=sql+observation,
                        lean=dict(code=a.returncode, stdout=a.stdout.decode('latin-1'), stderr=a.stderr.decode('latin-1')),
                        sqlite=dict(code=b.returncode, stdout=b.stdout.decode('latin-1'), stderr=b.stderr.decode('latin-1'))))
                elif a.returncode:
                    matching_errors += 1
                    for original in files[:2]:
                        current = directory/original.name
                        assert current.exists() == original.exists()
                        if current.exists():
                            assert current.read_bytes() == original.read_bytes(), 'failed statement changed database bytes'
                if not a.returncode and not b.returncode:
                    inspect = directory/'inspect'
                    inspect.mkdir()
                    for suffix in ['', '-wal']:
                        original = directory/('lean.db'+suffix)
                        if original.exists():
                            shutil.copyfile(original, inspect/('copy.db'+suffix))
                    observed = subprocess.run([args.sqlite, '-batch', '-bail', str(inspect/'copy.db')],
                        input=(observation+'PRAGMA integrity_check;').encode(), capture_output=True, timeout=120)
                    if observed.returncode or observed.stdout != b.stdout+b'ok\n':
                        failures.append(dict(mode=mode, sql=sql, external_sqlite=observed.stdout.decode('latin-1'),
                                             external_error=observed.stderr.decode('latin-1'), expected=(b.stdout+b'ok\n').decode('latin-1')))
            phases.append(dict(mode=mode, queries=len(queries), writes=len(writes), matching_errors=matching_errors))
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
