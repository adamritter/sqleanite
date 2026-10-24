#!/usr/bin/env python3
"""Compare quoted column references and single-source qualifier binding.

Exact CLI output, rejection status and unchanged input bytes are compared on
independent files in both modes. The pinned SQLite CLI disables DQS fallback;
unknown quoted identifiers must therefore reject. All mismatches are retained.
Successful writes are independently observed with the pinned SQLite CLI and
integrity-checked; rejected writes preserve bytes. This suite does not establish
complete alias, schema-name or grouping behavior.
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
    p.add_argument('--seed', type=int, default=353660)
    p.add_argument('--random-cases', type=int, default=100)
    p.add_argument('--output', type=pathlib.Path)
    args = p.parse_args()
    rng = random.Random(args.seed)
    def quoted(name, style):
        if style == 0:
            return '"'+name.replace('"', '""')+'"'
        if style == 1:
            return '['+name+']'
        return '`'+name.replace('`', '``')+'`'
    setup = ('CREATE TABLE t(id INTEGER PRIMARY KEY, "select" TEXT, [value name],true INTEGER,v);'
             "INSERT INTO t VALUES(1,'a',2,0,3),(2,'b',NULL,1,4),(3,'c',7,2,5);"
             'CREATE TABLE empty(id INTEGER PRIMARY KEY,v);')
    queries = []
    for name in ['id', 'select', 'value name', 'true', 'v', 'missing']:
        for style in range(3):
            ref = quoted(name, style)
            for table in ['t', 't AS x']:
                queries += [f'SELECT {ref},typeof({ref}) FROM {table} ORDER BY id;',
                            f'SELECT id FROM {table} WHERE {ref}>1 ORDER BY id;',
                            f'SELECT count({ref}),max({ref}) FROM {table};',
                            f'SELECT {ref} FROM {table} LIMIT 0;',
                            f'SELECT {ref} FROM {table} ORDER BY {ref};']
    for qualifier in ['t', 'x', 'missing']:
        for name in ['id', 'v', 'missing']:
            for style in range(3):
                ref = qualifier+'.'+quoted(name, style)
                for table in ['t', 't AS x']:
                    queries += [f'SELECT {ref} FROM {table};', f'SELECT {ref} FROM {table} LIMIT 0;',
                                f'SELECT id FROM {table} WHERE {ref}=1;', f'SELECT id FROM {table} ORDER BY {ref};']
    for _ in range(args.random_cases):
        ref = quoted(rng.choice(['id', 'v', 'true', 'value name']), rng.randrange(3))
        expr = rng.choice([f'{ref}+1', f'coalesce({ref},0)', f'typeof({ref})', f'{ref} IS TRUE',
                           f'CASE WHEN {ref} THEN 1 ELSE 2 END'])
        queries.append(f'SELECT {expr} FROM t WHERE {ref} IN (0,1,3,7) ORDER BY id;')
    for name in ['missing', 'v']:
        for style in range(3):
            ref = quoted(name, style)
            queries += [f'SELECT {ref};', f'SELECT 0 AND {ref};', f'SELECT 0 AND {ref} FROM empty;',
                        f'SELECT 1 OR {ref} FROM empty;', f'SELECT {ref} FROM empty LIMIT 0;']
    for qualifier in ['t', 'x', 'missing']:
        for table in ['t', 't AS x']:
            for ref in [qualifier+'.id', qualifier+'.v']:
                queries += [f'SELECT count({ref}),max({ref}) FROM {table};',
                            f'SELECT {ref},count(*) FROM {table} GROUP BY {ref};',
                            f'SELECT 0 AND {ref} FROM {table};']
            queries += [f'SELECT {qualifier}.* FROM {table} WHERE id=1;',
                        f'SELECT {qualifier}.* FROM {table} LIMIT 0;']
    for style in range(3):
        ref = quoted('v', style)
        queries += [f'SELECT {ref},sum({ref}),count({ref}) FROM t GROUP BY {ref};',
                    f'SELECT {ref},sum({ref}) FROM t AS x GROUP BY {ref};']
    # A primary-key equality exercises the reopened page-directed fast path.
    for ref in ['t.id', 'x.id', 'missing.id', 't.v', 'x.v', 'missing.v']:
        for table in ['t', 't AS x']:
            queries += [f'SELECT {ref} FROM {table} WHERE id=1;',
                        f'SELECT id FROM {table} WHERE id=1 ORDER BY {ref};']
    writes = []
    for table in ['t', 't AS x']:
        for qualifier in ['', 't.', 'x.', 'missing.']:
            for style in range(3):
                ref = qualifier+quoted('v', style)
                writes += [f'UPDATE {table} SET v={ref}+1 WHERE id=1;',
                           f'UPDATE {table} SET v=8 WHERE {ref}=3;',
                           f'DELETE FROM {table} WHERE {ref}=3;']
    writes += ['UPDATE empty SET v=missing.v WHERE 0;',
               'DELETE FROM empty WHERE missing.v=1;',
               'UPDATE empty SET v=0 AND "missing";',
               'DELETE FROM empty WHERE 0 AND "missing";',
               'UPDATE t SET v="v"+1, "select"="select"||\'x\' WHERE "id"=1;',
               'UPDATE t AS x SET v=x.v+1 WHERE x.id=2;']
    observation = 'SELECT id,"select",typeof("select"),"value name",typeof("value name"),true,typeof(true),v,typeof(v) FROM t ORDER BY id;'
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-quoted-names-') as tmp:
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
            a, b = run(setup)
            assert a.returncode == b.returncode == 0, (a.stderr, b.stderr)
            files = [d/'lean.db', d/'lean.db-wal', d/'sqlite.db', d/'sqlite.db-wal']
            def snapshot():
                return {str(f): f.read_bytes() for f in files if f.exists()}
            before = snapshot()
            errors = 0
            for sql in queries:
                a, b = run(sql)
                same = (a.returncode == b.returncode == 0 and a.stdout == b.stdout) or (a.returncode != 0 and b.returncode != 0)
                if not same:
                    failures.append(dict(mode=mode, sql=sql,
                        lean=dict(code=a.returncode, stdout=a.stdout.decode('latin-1'), stderr=a.stderr.decode('latin-1')),
                        sqlite=dict(code=b.returncode, stdout=b.stdout.decode('latin-1'), stderr=b.stderr.decode('latin-1'))))
                elif a.returncode:
                    errors += 1
            assert snapshot() == before, 'quoted-name reads changed database/WAL bytes'
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
                    errors += 1
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
            phases.append(dict(mode=mode, queries=len(queries), writes=len(writes), matching_errors=errors))
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
