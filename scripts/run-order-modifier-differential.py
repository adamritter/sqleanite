#!/usr/bin/env python3
"""Compare explicit ordering collations and NULL placement.

Compare exact CLI bytes and rejection status against pinned SQLite on
independent files in both modes. Database and WAL bytes must survive every
read unchanged. Cases include raw TEXT/NUL, numeric classes and aliases.
Matching rejections do not compare error wording. Every mismatch is retained.
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
    p.add_argument('--seed', type=int, default=353680)
    p.add_argument('--random-cases', type=int, default=200)
    p.add_argument('--output', type=pathlib.Path)
    args = p.parse_args()
    rng = random.Random(args.seed)
    setup = ['CREATE TABLE t(id INTEGER PRIMARY KEY,v,n);']
    values = ["NULL", "'A'", "'a'", "'Ab'", "'aB'", "'ab '", "'ab  '", "' '", "''", "'B'", "'b'",
              "'Á'", "'á'", "'ß'", "X'41'", "X'61'", "0", "1", "1.0", "2", "'2'",
              "CAST(X'610042' AS TEXT)", "CAST(X'410062' AS TEXT)", "CAST(X'6100' AS TEXT)",
              "CAST(X'FF41' AS TEXT)", "CAST(X'FF61' AS TEXT)"]
    for i,value in enumerate(values+[rng.choice(values) for _ in range(30)],1):
        setup.append(f'INSERT INTO t VALUES({i},{value},{rng.choice(["NULL","-1","0","1","2.0"])});')
    queries=[]
    collations=['',' COLLATE BINARY',' COLLATE NOCASE',' COLLATE RTRIM',' COLLATE missing']
    directions=['',' ASC',' DESC']
    nulls=['',' NULLS FIRST',' NULLS LAST']
    for column in ['v','n']:
        for collation in collations:
            for direction in directions:
                for null_order in nulls:
                    order=column+collation+direction+null_order
                    queries += [f'SELECT id,v,n FROM t ORDER BY {order},id;',
                                f'SELECT id,v,n FROM t ORDER BY {order} LIMIT 5 OFFSET 2;',
                                f'SELECT {column} AS x,id FROM t ORDER BY x{collation}{direction}{null_order};']
    for _ in range(args.random_cases):
        order=rng.choice(['v','n','lower(v)',"v||''"])+rng.choice(collations[:4])+rng.choice(directions)+rng.choice(nulls)
        queries.append(f'SELECT id,v,n FROM t WHERE id>{rng.randrange(0,20)} ORDER BY {order} LIMIT {rng.randrange(0,9)};')
    queries += ['SELECT id FROM t ORDER BY id DESC NULLS FIRST,abs(-9223372036854775808) LIMIT 1;',
                'SELECT 1 ORDER BY 1 NULLS FIRST;', 'SELECT 1 ORDER BY 1 COLLATE NOCASE;',
                'SELECT 1 ORDER BY 1 COLLATE missing LIMIT 0;']
    queries += ['SELECT v FROM t ORDER BY 0 AND v;',
                'SELECT v FROM t ORDER BY 0 AND lower(1) COLLATE BINARY;',
                'SELECT v FROM t ORDER BY 0 AND abs(-9223372036854775808) COLLATE BINARY;',
                'SELECT v FROM t ORDER BY 1 COLLATE missing COLLATE BINARY;',
                'SELECT v FROM t ORDER BY v COLLATE missing COLLATE NOCASE;',
                'SELECT v FROM t ORDER BY 1 OR v;',
                'SELECT v FROM t ORDER BY FALSE AND v;',
                'SELECT v FROM t ORDER BY 0 AND unknown_function() COLLATE BINARY;']
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-order-modifier-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            d=pathlib.Path(tmp)/mode; d.mkdir()
            def run(sql):
                q=d/'query.sql'; q.write_text(sql)
                a=subprocess.run([str(args.lean),mode,str(d/'lean.db'),str(q)],capture_output=True,timeout=120)
                b=subprocess.run([args.sqlite,'-batch','-bail',str(d/'sqlite.db')],input=sql.encode(),capture_output=True,timeout=120)
                return a,b
            a,b=run('\n'.join(setup))
            assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            files=[d/'lean.db',d/'lean.db-wal',d/'sqlite.db',d/'sqlite.db-wal']
            def snapshot(): return {str(f):f.read_bytes() for f in files if f.exists()}
            before=snapshot(); errors=0
            for sql in queries:
                a,b=run(sql)
                same=(a.returncode==b.returncode==0 and a.stdout==b.stdout) or (a.returncode!=0 and b.returncode!=0)
                if not same:
                    def outcome(r): return dict(code=r.returncode,stdout=r.stdout.decode('latin-1'),stderr=r.stderr.decode('latin-1'))
                    failures.append(dict(mode=mode,sql=sql,lean=outcome(a),sqlite=outcome(b)))
                elif a.returncode: errors+=1
            assert before==snapshot(),'ORDER BY reads changed main/WAL bytes'
            phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors))
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,
                implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
                harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    if args.output: args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__':
    raise SystemExit(main())
