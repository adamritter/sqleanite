#!/usr/bin/env python3
"""Large values across scalar evaluation, main/WAL persistence and SQLite-created
files. SQL/CLI comparison uses the selected pinned SQLite executable; Python's
SQLite independently observes complete stored bytes and integrity after closing
each connection. Timeouts and process failures are retained, never counted as passes.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import sqlite3
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def observe(path):
    connection = sqlite3.connect(path)
    connection.text_factory = bytes
    try:
        rows = [(i, kind.decode(), len(value), digest(value)) for i, kind, value in
                connection.execute('SELECT id,typeof(v),CAST(v AS BLOB) FROM t ORDER BY id')]
        integrity = [row[0].decode() for row in connection.execute('PRAGMA integrity_check')]
        return dict(rows=rows, integrity=integrity)
    finally:
        connection.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sqlite', default=os.environ.get('SQLITE3_BIN', '/usr/bin/sqlite3'))
    parser.add_argument('--lean', type=pathlib.Path, default=ROOT / '.lake/build/bin/sqleanite')
    parser.add_argument('--seed', type=int, default=353690)
    parser.add_argument('--random-cases', type=int, default=3)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    parser.add_argument('--timeout', type=int, default=180)
    parser.add_argument('--stored-bytes', type=int, default=1000000)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    cases = [999999, 1000000, 1000001, 1048577, 2000003]
    cases += [rng.randrange(1000002, 1500000) for _ in range(args.random_cases)]
    failures, phases, comparisons = [], [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-large-values-') as temp:
        root = pathlib.Path(temp)

        def run(mode, folder, sql):
            folder.mkdir(exist_ok=True)
            query = folder / 'query.sql'
            query.write_text(sql)
            outcomes = []
            commands = [[str(args.lean), mode, str(folder/'lean.db'), str(query)],
                        [args.sqlite, '-batch', '-bail', str(folder/'sqlite.db')]]
            for index, command in enumerate(commands):
                try:
                    result = subprocess.run(command, input=sql.encode() if index else None,
                                            capture_output=True, timeout=args.timeout)
                    outcomes.append(dict(code=result.returncode, stdout=result.stdout.decode('latin-1'),
                                         stderr=result.stderr.decode('latin-1')))
                except subprocess.TimeoutExpired:
                    outcomes.append(dict(timeout_seconds=args.timeout))
            return outcomes

        def compare(mode, folder, sql, label):
            lean, reference = run(mode, folder, sql)
            same = ('code' in lean and 'code' in reference and
                    ((lean['code'] == reference['code'] == 0 and lean['stdout'] == reference['stdout']) or
                     (lean['code'] > 0 and reference['code'] > 0)))
            comparisons.append(dict(mode=mode, phase=label, matched=same, sql=sql,
                                    matching_error=same and lean['code'] != 0))
            if not same:
                failures.append(dict(mode=mode, fixture=folder.name, phase=label, sql=sql, lean=lean, sqlite=reference))
            return same and lean['code'] == 0

        for mode in ['--verified-file', '--verified-wal-file']:
            folder = root / mode
            scalar_queries = 0
            for n in cases:
                for expression in [f'length(zeroblob({n}))', f'length(hex(zeroblob({n//2})))',
                                   f'length(concat(hex(zeroblob({n//2})),\'xyz\'))',
                                   f'length(substr(zeroblob({n}),-17))']:
                    compare(mode, folder, f'SELECT {expression};', 'scalar')
                    scalar_queries += 1
            errors = ['zeroblob(1000000001)', 'zeroblob(9223372036854775807)',
                      'zeroblob(1e999)']
            for expr in errors:
                compare(mode, folder, f'SELECT {expr};', 'oversize')
            phases.append(dict(mode=mode, phase='scalar', queries=scalar_queries, oversize_cases=len(errors)))
            for kind in ['blob', 'text', 'raw-text']:
                destination = root / (mode+'-'+kind)
                n = args.stored_bytes + rng.randrange(1, 20000)
                expression = {'blob': f"X'80FF00'||zeroblob({n})||X'41'",
                              'text': f"'árvíz🙂'||hex(zeroblob({n//2}))||'z'",
                              'raw-text': f"X'FF80'||zeroblob({n})||X'C0AF'"}[kind]
                expression = f'CAST(({expression}) AS {"BLOB" if kind == "blob" else "TEXT"})'
                setup = f'CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,{expression});'
                if compare(mode, destination, setup, 'write-'+kind):
                    a, b = observe(destination/'lean.db'), observe(destination/'sqlite.db')
                    if a != b or a['integrity'] != ['ok']:
                        failures.append(dict(mode=mode, phase='stored-'+kind, lean=a, sqlite=b))
                    select = 'SELECT id,typeof(v),length(CAST(v AS BLOB)),hex(substr(CAST(v AS BLOB),1,12)),hex(substr(CAST(v AS BLOB),-12)) FROM t;'
                    compare(mode, destination, select, 'reopen-'+kind)
                    compare(mode, destination, 'CREATE INDEX tv ON t(v); SELECT id FROM t ORDER BY v LIMIT 1;', 'index-'+kind)
                    update = f'UPDATE t SET v=CAST(v||\'tail-{args.seed}\' AS {"BLOB" if kind == "blob" else "TEXT"}) WHERE id=1;'
                    if compare(mode, destination, update, 'update-'+kind):
                        a, b = observe(destination/'lean.db'), observe(destination/'sqlite.db')
                        if a != b or a['integrity'] != ['ok']:
                            failures.append(dict(mode=mode, phase='updated-bytes-'+kind, lean=a, sqlite=b))
                    compare(mode, destination, 'DELETE FROM t WHERE id=1; SELECT count(*) FROM t;', 'delete-'+kind)
                    if observe(destination/'lean.db') != observe(destination/'sqlite.db'):
                        failures.append(dict(mode=mode, phase='deleted-'+kind))
                phases.append(dict(mode=mode, phase='persistence-'+kind, value_bytes_at_least=n))
            for page_size in [512, 4096, 65536]:
                destination = root / f'{mode}-foreign-{page_size}'
                destination.mkdir()
                n = args.stored_bytes + rng.randrange(1, 30000)
                setup = f'PRAGMA page_size={page_size}; CREATE TABLE t(id INTEGER PRIMARY KEY,v); INSERT INTO t VALUES(1,zeroblob({n})); INSERT INTO t VALUES(2,hex(zeroblob({n//2})));'
                result = subprocess.run([args.sqlite, '-batch', '-bail', str(destination/'sqlite.db')], input=setup.encode(), capture_output=True)
                assert result.returncode == 0, result.stderr
                (destination/'lean.db').write_bytes((destination/'sqlite.db').read_bytes())
                before = (destination/'lean.db').read_bytes()
                compare(mode, destination, 'SELECT id,typeof(v),length(v),hex(substr(CAST(v AS BLOB),-8)) FROM t ORDER BY id;', 'foreign-read')
                if (destination/'lean.db').read_bytes() != before:
                    failures.append(dict(mode=mode, phase='foreign-read-mutated', page_size=page_size))
                if compare(mode, destination, "UPDATE t SET v=v||'tail' WHERE id=2;", 'foreign-update'):
                    a, b = observe(destination/'lean.db'), observe(destination/'sqlite.db')
                    if a != b or a['integrity'] != ['ok']:
                        failures.append(dict(mode=mode, phase='foreign-updated-bytes', page_size=page_size, lean=a, sqlite=b))
                phases.append(dict(mode=mode, phase='foreign-read-update', page_size=page_size, blob_bytes=n))
    source = hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        source.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report = dict(seed=args.seed, random_cases=args.random_cases, stored_bytes=args.stored_bytes, phases=phases, comparisons=comparisons, failures=failures,
                  implementation_sha256=source.hexdigest(), executable_sha256=digest(args.lean.read_bytes()),
                  harness_sha256=digest(pathlib.Path(__file__).read_bytes()),
                  sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),
                  observer_sqlite_version=sqlite3.sqlite_version, comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(phases=len(phases),failures=len(failures),report=str(args.output))))
    return bool(failures)

if __name__ == '__main__':
    raise SystemExit(main())
