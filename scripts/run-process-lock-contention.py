#!/usr/bin/env python3
"""Fresh subprocess contention against the public writer lock. Every worker
inserts a distinct row; pinned SQLite checks the complete rows and file integrity.
This is stress evidence, not a proof of the OS lock refinement.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
import pathlib
import random
import subprocess
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=353700)
    parser.add_argument('--rounds', type=int, default=12)
    parser.add_argument('--workers', type=int, default=16)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    executable = ROOT/'.lake/build/bin/sqleanite'
    sqlite = os.environ['SQLITE3_BIN']
    rng = random.Random(args.seed)
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-contention-') as tmp:
        for mode in ['--verified-file', '--verified-wal-file']:
            folder = pathlib.Path(tmp)/mode
            folder.mkdir()
            database = folder/'test.db'
            setup = folder/'setup.sql'
            setup.write_text('CREATE TABLE t(id INTEGER PRIMARY KEY,v);')
            result = subprocess.run([str(executable),mode,str(database),str(setup)],capture_output=True,timeout=120)
            assert result.returncode == 0, result.stderr
            rows = []
            for round_ in range(args.rounds):
                jobs = []
                for worker in range(args.workers):
                    key = round_*args.workers+worker
                    value = rng.randrange(-1000000,1000000)
                    rows.append((key,value))
                    source = folder/f'worker-{key}.sql'
                    source.write_text(f'INSERT INTO t VALUES({key},{value});')
                    jobs.append((source, rng.random()/200))
                def run(job):
                    source, delay = job
                    time.sleep(delay)
                    try:
                        result = subprocess.run([str(executable),mode,str(database),str(source)],capture_output=True,timeout=120)
                        return dict(file=source.name,code=result.returncode,stderr=result.stderr.decode())
                    except subprocess.TimeoutExpired:
                        return dict(file=source.name,timeout_seconds=120)
                with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
                    outcomes = list(pool.map(run,jobs))
                failures.extend(dict(mode=mode,round=round_,**outcome) for outcome in outcomes if outcome.get('code') != 0)
            observed = subprocess.run([sqlite,'-batch','-bail',str(database),'PRAGMA integrity_check; SELECT id,v FROM t ORDER BY id;'],capture_output=True,timeout=120)
            expected = 'ok\n'+''.join(f'{key}|{value}\n' for key,value in sorted(rows))
            if observed.returncode or observed.stdout.decode() != expected:
                failures.append(dict(mode=mode,phase='complete-rows',code=observed.returncode,stdout=observed.stdout.decode(),stderr=observed.stderr.decode()))
            if (folder/'test.db.sqleanite-lock').exists():
                failures.append(dict(mode=mode,phase='lock-not-released'))
            phases.append(dict(mode=mode,workers=args.workers,rounds=args.rounds,insertions=len(rows),expected_rows_sha256=hashlib.sha256(expected.encode()).hexdigest()))
    source=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        source.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,phases=phases,failures=failures,implementation_sha256=source.hexdigest(),
                executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),
                harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(insertions=sum(p['insertions'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':
    raise SystemExit(main())
