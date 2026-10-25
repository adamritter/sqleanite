#!/usr/bin/env python3
"""Live CREATE INDEX and reopened-catalog UPDATE order against pinned SQLite.

Both public file modes; independently observed persisted row values, storage
classes and integrity after each case. This is a planner-order regression,
not an exhaustive planner or SQLite equivalence claim.
"""
import argparse, hashlib, itertools, json, os, random, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--sqlite', default=os.environ.get('SQLITE3_BIN', 'sqlite3'))
    p.add_argument('--seed', type=int, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args(); rng = random.Random(a.seed); cases = []
    binary = str(ROOT / '.lake/build/bin/sqleanite')
    def run(args, sql):
        r = subprocess.run(args, input=sql.encode(), capture_output=True, timeout=120)
        return dict(code=r.returncode, stdout=r.stdout.decode('latin1'), stderr=r.stderr.decode('latin1'))
    definitions = {'tu': 'CREATE UNIQUE INDEX tu ON t(u);', 'tw': 'CREATE INDEX tw ON t(w);', 'tv': 'CREATE INDEX tv ON t(v);'}
    observation = 'PRAGMA integrity_check;\nSELECT id,typeof(v),hex(v),typeof(u),hex(u),typeof(w),hex(w) FROM t ORDER BY id;'
    with tempfile.TemporaryDirectory(prefix='sqleanite-update-index-order-') as tmp:
        for fixture in range(4):
            us = list(range(1, 8)); ws = list(range(1, 8)); rng.shuffle(us); rng.shuffle(ws)
            values = ','.join(f"({i},'v{8-i}',{u},{w})" for i, (u, w) in enumerate(zip(us, ws), 1))
            for names in [('tu', 'tw'), ('tw', 'tu'), *itertools.permutations(definitions)]:
                for rebuild in [False, True]:
                    setup = 'CREATE TABLE t(id INTEGER PRIMARY KEY,v,u INTEGER,w INTEGER);\n'
                    setup += '\n'.join(definitions[n] for n in names) + '\n'
                    if rebuild:
                        setup += f'DROP INDEX {names[0]};\n{definitions[names[0]]}\n'
                    setup += f'INSERT INTO t VALUES {values};\n'
                    update = 'UPDATE OR IGNORE t SET u=100 WHERE u>0 AND w>0;\nSELECT id FROM t WHERE u=100;'
                    for mode in ['--verified-file', '--verified-wal-file']:
                        for reopen in [False, True]:
                            folder = Path(tmp) / str(len(cases)); folder.mkdir()
                            lean = folder / 'lean.db'; ref = folder / 'sqlite.db'
                            lc = [binary, mode, str(lean)]; rc = [a.sqlite, '-batch', '-bail', str(ref)]
                            phases = [setup, update] if reopen else [setup + update]
                            results = [(run(lc, phase), run(rc, phase)) for phase in phases]
                            lo = run([a.sqlite, '-batch', '-bail', str(lean)], observation)
                            ro = run([a.sqlite, '-batch', '-bail', str(ref)], observation)
                            matched = all(l['code'] == r['code'] == 0 and l['stdout'] == r['stdout'] for l, r in results)
                            matched &= lo['code'] == ro['code'] == 0 and lo['stdout'] == ro['stdout'] and lo['stdout'].startswith('ok\n')
                            cases.append(dict(fixture=fixture, indexes=names, rebuild_first=rebuild, mode=mode, reopen=reopen,
                                              phases=phases, results=results, observed_lean=lo, observed_sqlite=ro, matched=matched))
    d = hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean')) + [ROOT/'Main.lean']:
        d.update(str(path.relative_to(ROOT)).encode() + b'\0' + path.read_bytes())
    report = dict(seed=a.seed, cases=cases, failures=sum(not c['matched'] for c in cases),
                  implementation_sha256=d.hexdigest(), executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),
                  harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  sqlite_version=subprocess.check_output([a.sqlite, '--version'], text=True).strip(), comparison=__doc__.strip())
    a.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(cases=len(cases), failures=report['failures'])))
    return bool(report['failures'])
if __name__ == '__main__':
    raise SystemExit(main())
