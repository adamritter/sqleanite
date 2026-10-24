#!/usr/bin/env python3
"""Exercise byte-preserving TEXT and SQLite's permissive UTF-8 string routines.

Each scalar result is inserted into a real file. Independent SQLite readers
compare storage class, exact IEEE-754 bits and original TEXT/BLOB bytes, then
check integrity. CLI bytes and success/rejection status are compared as well.
Both production file modes are exercised; unsupported results remain failures.
Error wording is not compared. There is no Unicode repair or normalization.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import shutil
import sqlite3
import struct
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean', type=pathlib.Path, default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite', default=os.environ.get('SQLITE3_BIN', '/usr/bin/sqlite3'))
    p.add_argument('--seed', type=int, default=353650)
    p.add_argument('--random-cases', type=int, default=100)
    p.add_argument('--output', type=pathlib.Path)
    args = p.parse_args()
    rng = random.Random(args.seed)
    def blob(b):
        return "X'"+b.hex()+"'"
    def txt(b):
        return 'CAST('+blob(b)+' AS TEXT)'
    payloads = [b'', b'\xff', b'\x80\x81A', b'A\x80\x81B', b'\xc0\xaf', b'\xed\xa0\x80',
                b'\xf4\x90\x80\x80', b'\xfe\x80\x80\x80\x80\x80\x80', b'A\0\xffB',
                b'12\xff', b'12\0\xff', b' 1.5\xff', b"\xff'\x80", b'\xc3\xa9\xff', b'\xe2\x82', bytes(range(1,33)), b'\r\n\r\t\n',
                b'9007199254740993\0\xff', b'9223372036854775807\0\xff']
    payloads += [bytes(rng.randrange(256) for _ in range(rng.randrange(1, 14))) for _ in range(args.random_cases)]
    expressions = []
    for b in payloads:
        x = txt(b)
        expressions += [x, f'length({x})', f'octet_length({x})', f'unicode({x})', f'quote({x})',
                        f'upper({x})', f'lower({x})', f'CAST({x} AS BLOB)', f'CAST({x} AS INTEGER)',
                        f'CAST({x} AS REAL)', f'CAST({x} AS NUMERIC)', f'{x}+0', f'{x}||\'x\'',
                        f"concat('a',{x},'b')", f"concat_ws({x},'a','','b')",
                        f'{x}={txt(b)}', f'{x} IS {blob(b)}',
                        f'substr({x},{rng.randrange(-8,9)},{rng.randrange(-8,9)})',
                        f'instr({x},{txt(b[1:3])})', f'instr({blob(b)},{txt(b[1:3])})',
                        f'trim({x},{txt(b[:2])})', f'ltrim({x},{txt(b[:2])})', f'rtrim({x},{txt(b[-2:])})',
                        f'replace({x},{txt(b[:1])},{txt(bytes([255]))})', f'unhex({x})',
                        f'unhex({txt(b"41"+b+b"42")},{x})']
    expressions += [f'char({n})' for n in [0,127,128,2047,2048,55295,55296,56319,56320,57343,57344,65534,65535,1114111,1114112,-1]]
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-raw-text-') as tmp:
        for mode in ['--verified-file', '--verified-wal-file']:
            d = pathlib.Path(tmp)/mode
            d.mkdir()
            def run(sql):
                q = d/'query.sql'
                q.write_text(sql)
                a = subprocess.run([str(args.lean), mode, str(d/'lean.db'), str(q)], capture_output=True, timeout=120)
                b = subprocess.run([args.sqlite, '-batch', '-bail', str(d/'sqlite.db')], input=sql.encode(), capture_output=True, timeout=120)
                return a, b
            a, b = run('CREATE TABLE output(id INTEGER PRIMARY KEY,v);')
            assert a.returncode == b.returncode == 0
            errors = 0
            for i, expression in enumerate(expressions):
                a, b = run(f'INSERT INTO output VALUES({i+1},{expression}); SELECT v,typeof(v) FROM output WHERE id={i+1};')
                same = (a.returncode == b.returncode == 0 and a.stdout == b.stdout) or (a.returncode != 0 and b.returncode != 0)
                if not same:
                    failures.append(dict(mode=mode, id=i+1, expression=expression,
                        lean=dict(code=a.returncode, stdout=a.stdout.decode('latin-1'), stderr=a.stderr.decode('latin-1')),
                        sqlite=dict(code=b.returncode, stdout=b.stdout.decode('latin-1'), stderr=b.stderr.decode('latin-1'))))
                elif a.returncode:
                    errors += 1
            inspect = d/'inspect'
            inspect.mkdir()
            for suffix in ['', '-wal']:
                source = d/('lean.db'+suffix)
                if source.exists():
                    shutil.copyfile(source, inspect/('copy.db'+suffix))
            def stored(path):
                connection = sqlite3.connect(path)
                connection.text_factory = bytes
                integrity = connection.execute('PRAGMA integrity_check').fetchall()
                assert integrity == [(b'ok',)], integrity
                def value(v):
                    if isinstance(v, float):
                        return {'real_bits': struct.pack('>d', v).hex()}
                    if isinstance(v, bytes):
                        return {'bytes': v.hex()}
                    return v
                result = {row[0]: [row[1].decode(), value(row[2])] for row in connection.execute('SELECT id,typeof(v),v FROM output')}
                connection.close()
                return result
            observed, expected = stored(inspect/'copy.db'), stored(d/'sqlite.db')
            difference = {str(key): dict(lean=observed.get(key), sqlite=expected.get(key))
                          for key in sorted(observed.keys() | expected.keys()) if observed.get(key) != expected.get(key)}
            if difference:
                failures.append(dict(mode=mode, storage_differences=difference))
            phases.append(dict(mode=mode, expressions=len(expressions), matching_errors=errors,
                               lean_stored=len(observed), sqlite_stored=len(expected), storage_differences=len(difference)))
    digest = hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean')) + [ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report = dict(seed=args.seed, random_cases=args.random_cases, phases=phases, failures=failures,
                  implementation_sha256=digest.hexdigest(), executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
                  harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                  sqlite_version=subprocess.check_output([args.sqlite, '--version'], text=True).strip(),
                  sqlite_storage_observer_version=sqlite3.sqlite_version, comparison=__doc__.strip())
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
