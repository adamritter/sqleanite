#!/usr/bin/env python3
"""Cold-read admission with mixed scripts, committed prefixes and read-only batches.

Fixed script shapes and newly seeded rows/literals run through both public file
engines. Compare complete output, success/error status, first diagnostic, stored
catalog and typed rows, integrity and reopening against pinned SQLite 3.53.4.
No outcome-dependent input filtering. SQLite and Lean alternate as file creator.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import random
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'helpers', ROOT / 'scripts/run-json-position-differential.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)


def quote(value):
    return "'" + value.replace("'", "''") + "'"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, required=True)
    parser.add_argument('--count', type=int, default=128)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    sqlite = os.environ.get('SQLITE3_BIN', 'sqlite3')
    binary = ROOT / '.lake/build/bin/sqleanite'
    source = helpers.digest()
    executable = hashlib.sha256(binary.read_bytes()).hexdigest()

    def run(command, sql):
        try:
            result = subprocess.run(command, input=sql.encode(), capture_output=True,
                                    timeout=30)
            return dict(code=result.returncode, stdout=result.stdout.decode('latin1'),
                        stderr=result.stderr.decode('latin1'))
        except subprocess.TimeoutExpired as result:
            return dict(code=124, stdout=(result.stdout or b'').decode('latin1'),
                        stderr=(result.stderr or b'').decode('latin1'), timed_out=True)

    def csql(path, sql):
        return run([sqlite, '-batch', '-bail', str(path)], sql)

    assert csql(':memory:', 'SELECT sqlite_version();')['stdout'] == '3.53.4\n'
    inputs = []
    for index in range(12 + args.count):
        fixed = index < 12
        ids = list(range(1, 7)) if fixed else sorted(rng.sample(range(-400, 401), rng.randrange(5, 9)))
        rows = [(key, 'fixed;' + str(key) if fixed else ''.join(
            rng.choice("abcXYZ09 ;'é") for _ in range(rng.randrange(2, 24)))) for key in ids]
        group = index % 12
        first, middle, last = ids[0], ids[len(ids) // 2], ids[-1]
        extra = last + 1000
        marker = quote('new;literal' if fixed else 'new;' + str(rng.randrange(10**12)))
        point = f'SELECT id,v FROM t WHERE id={first};'
        end = 'SELECT id,v FROM t ORDER BY id;'
        scripts = [
            [point, f'SELECT id,v FROM t WHERE id>={middle} ORDER BY id DESC LIMIT 3;',
             f'SELECT id FROM t WHERE id={last};'],
            [f'SELECT {marker};', point, end],
            [point, "SELECT date('now',NULL);", end],
            [point, f'INSERT INTO t VALUES({extra},{marker});', end],
            [point, f'UPDATE t SET v={marker} WHERE id>={middle};', end],
            [point, 'BEGIN;', f'UPDATE t SET v={marker};', 'ROLLBACK;', end],
            [point, 'SELECT absent_column FROM t;', end],
            [point, 'SELECT id FROM t WHERE id=;', end],
            ['-- comment with ;\n' + point,
             f'SELECT v AS "semi;alias" FROM t WHERE id={middle}; /* ; */', end],
            [f'SELECT a.id,a.v,b.id FROM t a JOIN u b ON a.id=b.id WHERE a.id>={middle} ORDER BY a.id;', point],
            [point, 'PRAGMA user_version=731;', 'PRAGMA user_version;', end],
            [point, f'DELETE FROM t WHERE id={middle};', end],
        ]
        page_size = (512 << ((index // 2) % 8)) if index % 2 == 0 else None
        setup = ((f'PRAGMA page_size={page_size};' if page_size else '') +
                 'CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);'
                 'CREATE TABLE u(id INTEGER PRIMARY KEY);' +
                 ''.join(f'INSERT INTO t VALUES({key},{quote(value)});' for key, value in rows) +
                 ''.join(f'INSERT INTO u VALUES({key});' for key in ids[::2]))
        inputs.append(dict(group=group, fixed=fixed, rows=rows, page_size=page_size,
                           creator='sqlite' if index % 2 == 0 else 'lean', setup=setup,
                           sql='\n'.join(scripts[group]) + '\n'))

    observation = ('PRAGMA integrity_check;PRAGMA user_version;'
                   'SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;'
                   'SELECT id,typeof(v),quote(v),hex(CAST(v AS BLOB)) FROM t ORDER BY id;'
                   'SELECT id FROM u ORDER BY id;')
    reopen_sql = 'SELECT id,typeof(v),quote(v) FROM t ORDER BY id;'
    cases = []
    with tempfile.TemporaryDirectory(prefix='sqleanite-cold-chunks-') as tmp:
        folder = Path(tmp)
        for index, entry in enumerate(inputs):
            base = folder / f'{index}-base.db'
            made = (csql(base, entry['setup']) if entry['creator'] == 'sqlite' else
                    run([str(binary), '--verified-file', str(base)], entry['setup']))
            assert made['code'] == 0, (entry, made)
            entry['actual_page_size'] = csql(base, 'PRAGMA page_size;')
            for mode in ['--verified-file', '--verified-wal-file']:
                left = folder / f'{index}{mode}-lean.db'
                right = folder / f'{index}{mode}-sqlite.db'
                shutil.copyfile(base, left)
                shutil.copyfile(base, right)
                lean = run([str(binary), mode, str(left)], entry['sql'])
                reference = csql(right, entry['sql'])
                observed_lean, observed_sqlite = csql(left, observation), csql(right, observation)
                reopened_lean = run([str(binary), mode, str(left)], reopen_sql)
                reopened_sqlite = csql(right, reopen_sql)
                matched = (not lean.get('timed_out', False) and helpers.same(lean, reference)
                           and observed_lean == observed_sqlite
                           and observed_lean['code'] == 0
                           and observed_lean['stdout'].startswith('ok\n')
                           and helpers.same(reopened_lean, reopened_sqlite))
                cases.append(dict(input=index, mode=mode, lean=lean, sqlite=reference,
                                  observation_lean=observed_lean, observation_sqlite=observed_sqlite,
                                  reopened_lean=reopened_lean, reopened_sqlite=reopened_sqlite,
                                  matched=matched))
    assert source == helpers.digest()
    assert executable == hashlib.sha256(binary.read_bytes()).hexdigest()
    report = dict(seed=args.seed, comparison=__doc__.strip(), inputs=inputs, cases=cases,
                  failures=sum(not case['matched'] for case in cases),
                  implementation_sha256=source, executable_sha256=executable,
                  harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  helper_sha256=hashlib.sha256((ROOT / 'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),
                  sqlite_version=subprocess.check_output([sqlite, '--version'], text=True).strip())
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(cases=len(cases), failures=report['failures'])))
    return bool(report['failures'])


if __name__ == '__main__':
    raise SystemExit(main())
