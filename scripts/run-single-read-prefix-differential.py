#!/usr/bin/env python3
"""Public single-source scalar output/error-prefix differential checks.

C-created rowid tables cover NULL, duplicate values, different column affinities,
integer overflow positions, DISTINCT, sorting, LIMIT/OFFSET and aliases. Compare
all stdout even when both programs fail; retain every input and negative result.
Fixed SQL templates and presence patterns mix with seeded data/windows, so a new
seed is fresh data evaluation, not a claim that every SQL template is unseen.
"""
import argparse
import hashlib
import itertools
import json
import os
import random
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def digest(root):
    value = hashlib.sha256()
    for path in sorted((root / 'SQLeanite').rglob('*.lean')) + [root / 'Main.lean']:
        value.update(str(path.relative_to(root)).encode() + b'\0' + path.read_bytes())
    return value.hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=354710)
    parser.add_argument('--fixtures', type=int, default=4)
    parser.add_argument('--random-cases', type=int, default=24)
    parser.add_argument('--implementation-root', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = args.implementation_root.resolve()
    binary = root / '.lake/build/bin/sqleanite'
    sqlite = os.environ.get('SQLITE3_BIN', 'sqlite3')
    rng = random.Random(args.seed)
    before_source = digest(root)
    before_binary = hashlib.sha256(binary.read_bytes()).hexdigest()
    cases, fixtures = [], []

    def run(command, sql):
        result = subprocess.run(command, input=sql.encode(), capture_output=True, timeout=120)
        return dict(code=result.returncode, stdout=result.stdout.decode('latin1'),
                    stderr=result.stderr.decode('latin1'))

    def csql(path, sql):
        return run([sqlite, '-batch', '-bail', str(path)], sql)

    def snapshot(path):
        return {suffix: hashlib.sha256(Path(str(path) + suffix).read_bytes()).hexdigest()
                for suffix in ['', '-wal'] if Path(str(path) + suffix).exists()}

    overflow = 'abs(-9223372036854775808)'
    projections = ['id,abs(k)', 'abs(k)', 'DISTINCT abs(k)', 'k', 'DISTINCT k',
        f'CASE WHEN k BETWEEN 1 AND {overflow} THEN 7 ELSE 9 END',
        f'CASE WHEN k NOT BETWEEN 1 AND {overflow} THEN 7 ELSE 9 END',
        'iif(k<0,abs(k),k)', 'CASE WHEN k<0 THEN abs(k) ELSE k END',
        'CASE k WHEN 0 THEN 7 ELSE abs(k) END', 'id,coalesce(k,abs(id))',
        'DISTINCT iif(k=0,0,abs(k))', '1']
    wheres = ['', f' WHERE k NOT BETWEEN 1 AND {overflow}',
        ' WHERE k>=0 OR abs(k)', ' WHERE id<3 OR abs(k)',
        ' WHERE CASE WHEN k<0 THEN abs(k) ELSE 1 END']
    tails = ['', ' ORDER BY id', ' ORDER BY id DESC', ' ORDER BY k,id',
        ' ORDER BY k DESC,id', ' LIMIT 0', ' LIMIT 1', ' LIMIT 2 OFFSET 1',
        ' ORDER BY id DESC LIMIT 2 OFFSET 1']
    queries = [f'SELECT {projection} FROM t{where}{tail};'
               for projection, where, tail in itertools.product(projections, wheres, tails)]
    queries += [
        'SELECT abs(k) AS v FROM t WHERE id<3 OR v>0;',
        'SELECT abs(k) AS v FROM t ORDER BY v LIMIT 2;',
        'SELECT sum(abs(k)) FROM t;',
        'SELECT k,count(*) FROM t GROUP BY k;',
        'SELECT missing,abs(k) FROM t;',
        'SELECT not_a_function(k) FROM t LIMIT 0;',
        'SELECT abs(k) COLLATE missing FROM t ORDER BY 1;',
        'SELECT abs(k) FROM t WHERE 0;',
        'SELECT abs(k) FROM t WHERE 0 AND missing;',
        'SELECT abs(k) FROM t WHERE abs(-9223372036854775808) AND id=0;',
        'SELECT abs(k) FROM t WHERE id=0 AND abs(-9223372036854775808);']
    for _ in range(args.random_cases):
        projection = rng.choice(projections)
        where = rng.choice(wheres)
        order = rng.choice(['', ' ORDER BY id', ' ORDER BY id DESC', ' ORDER BY k,id'])
        queries.append(f'SELECT {projection} FROM t{where}{order} LIMIT {rng.randrange(5)} OFFSET {rng.randrange(5)};')

    with tempfile.TemporaryDirectory(prefix='sqleanite-single-prefix-') as tmp:
        for fixture in range(args.fixtures):
            folder = Path(tmp) / str(fixture)
            folder.mkdir()
            base = folder / 'base.db'
            page_size = [512, 4096, 65536][fixture % 3]
            affinity = ['INTEGER', 'NUMERIC', 'TEXT', 'BLOB', 'REAL', ''][fixture % 6]
            setup = f'PRAGMA page_size={page_size};CREATE TABLE t(id INTEGER PRIMARY KEY,k {affinity});'
            bad = rng.randrange(1, 7)
            values = [str(rng.randrange(-4, 5)) for _ in range(6)]
            values[1] = values[0]
            values[4] = 'NULL'
            if fixture % 4 != 3:
                values[bad - 1] = '-9223372036854775808'
            if fixture % 8 != 7:
                for index, value in enumerate(values, 1):
                    setup += f'INSERT INTO t VALUES({index},{value});'
            created = csql(base, setup)
            assert created['code'] == 0, created
            for mode in ['--verified-file', '--verified-wal-file']:
                left, right = folder / (mode + '-lean.db'), folder / (mode + '-c.db')
                shutil.copyfile(base, left)
                shutil.copyfile(base, right)
                before_left, before_right = snapshot(left), snapshot(right)
                for sql in queries:
                    lean = run([str(binary), mode, str(left)], sql)
                    reference = csql(right, sql)
                    unchanged = snapshot(left) == before_left and snapshot(right) == before_right
                    matched = (bool(lean['code']) == bool(reference['code']) and
                               lean['stdout'] == reference['stdout'] and unchanged)
                    cases.append(dict(fixture=fixture, mode=mode, sql=sql, lean=lean,
                                      sqlite=reference, unchanged=unchanged, matched=matched))
                observation = 'PRAGMA integrity_check;SELECT id,typeof(k),hex(k) FROM t ORDER BY id;'
                lo, ro = csql(left, observation), csql(right, observation)
                matched = (snapshot(left) == before_left and snapshot(right) == before_right and
                           lo['code'] == ro['code'] == 0 and lo['stdout'] == ro['stdout'] and
                           lo['stdout'].startswith('ok\n'))
                fixtures.append(dict(fixture=fixture, mode=mode, page_size=page_size,
                    setup=setup, observation_lean=lo, observation_sqlite=ro, matched=matched))
    assert digest(root) == before_source, 'Production source changed during evaluation'
    assert hashlib.sha256(binary.read_bytes()).hexdigest() == before_binary, 'Executable changed during evaluation'
    failures = sum(not c['matched'] for c in cases) + sum(not f['matched'] for f in fixtures)
    report = dict(seed=args.seed, random_cases=args.random_cases, cases=cases, fixtures=fixtures,
        failures=failures, implementation_sha256=before_source, executable_sha256=before_binary,
        harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([sqlite, '--version'], text=True).strip(), comparison=__doc__.strip())
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(cases=len(cases), fixtures=len(fixtures), failures=failures)))
    return bool(failures)

if __name__ == '__main__':
    raise SystemExit(main())
