#!/usr/bin/env python3
"""Compare SUM/AVG/TOTAL state transitions against pinned SQLite.

Fresh groups mix storage classes, overflow, cancellation, subnormals, infinity,
NULLs and numeric-prefix text/blob conversion. Compare outputs and rejection
status in both production file modes; every failure is retained. This suite is
not a measurement of whole-SQLite coverage or arbitrary aggregate expressions.
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


def fixtures(seed, count):
    rng = random.Random(seed)
    groups = [[], ['NULL'], ['1','2','NULL'], ['1.5','2.5'], ['1','1.0'],
              ['9223372036854775807','1'], ['9223372036854775807','1','0.0'],
              ['0.0','9223372036854775807','1'], ['-9223372036854775808','-1'],
              ['-9223372036854775808','-1','1.0'], ['1e308','1.0','-1e308'],
              ['1e999','1'], ['-1e999','1'], ['1e999','-1e999'],
              ['1e308','1e308','-1e308'], ['5e-324','5e-324'], ['-0.0','0.0'],
              ["'1'","'2'"], ["'1.0'","'2e0'"], ["'12xyz'","'3'"],
              ["'9223372036854775807'","'1'"], ["X'3132'","X'31322e35'"],
              ["X'3132ff'","X'ff'"], ["CAST(X'31320033' AS TEXT)","'1'"],
              ["'invalid'",'NULL'], ['4503599627370497.0','-4503599627370496','1'],
              ['9007199254740993','-9007199254740992','0.0'],
              ['0.0','9007199254740993','-9007199254740992'],
              ['9223372036854775807','9223372036854775807','-9223372036854775808','0.0']]
    pool = ['NULL','0','1','-1','0.0','-0.0','1.5','-2.5','1e-200','1e200',
            '5e-324','1e999','-1e999','9223372036854775807','-9223372036854775808',
            '9007199254740993','4503599627370497',"'1'","'1.0'","'1e0'","'12xyz'",
            "'12.5xyz'","'  -3  '","''","'abc'","X'3132'","X'31322e35'","X'00'",
            "CAST(X'31320033' AS TEXT)","'9223372036854775808'"]
    for _ in range(count):
        groups.append(rng.choices(pool,k=rng.randrange(0,22)))
    setup = ['CREATE TABLE t(id INTEGER PRIMARY KEY,g INTEGER,v);','BEGIN;']
    rowid = 0
    for g,values in enumerate(groups):
        for v in values:
            rowid += 1
            setup.append(f'INSERT INTO t VALUES({rowid},{g},{v});')
    setup.append('COMMIT;')
    queries = [f'SELECT {fn}(v) FROM t WHERE g={g};'
               for g in range(len(groups)) for fn in ['sum','avg','total']]
    queries += [f'SELECT g,{fn}(v) FROM t WHERE g={g} GROUP BY g;'
                for g in range(min(len(groups),45)) for fn in ['sum','avg','total']]
    queries += ['SELECT id,g,v FROM t ORDER BY id;',
                'SELECT g,count(v),avg(v),total(v),min(v),max(v) FROM t GROUP BY g;',
                'SELECT avg(missing) FROM t WHERE id<0;',
                'SELECT total(missing) FROM t WHERE id<0;']
    return '\n'.join(setup), queries, len(groups)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353540)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--output',type=pathlib.Path)
    args = p.parse_args()
    setup,queries,groups = fixtures(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-numeric-aggregates-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            d=pathlib.Path(tmp)/mode;d.mkdir()
            def run(sql):
                q=d/'query.sql';q.write_text(sql)
                a=subprocess.run([str(args.lean),mode,str(d/'lean.db'),str(q)],text=True,encoding="latin-1",capture_output=True,timeout=120)
                b=subprocess.run([args.sqlite,'-batch','-bail',str(d/'sqlite.db')],input=sql,text=True,encoding="latin-1",capture_output=True,timeout=120)
                return a,b
            a,b=run(setup);assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            files=[d/'lean.db',d/'lean.db-wal'];before={str(f):f.read_bytes() for f in files if f.exists()}
            matching_errors=0;rows=0
            for sql in queries:
                a,b=run(sql)
                same=(a.returncode==b.returncode==0 and a.stdout==b.stdout) or (a.returncode!=0 and b.returncode!=0)
                if not same:
                    failures.append(dict(mode=mode,sql=sql,lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=dict(code=b.returncode,stdout=b.stdout,stderr=b.stderr)))
                elif a.returncode: matching_errors+=1
                rows+=len(a.stdout.splitlines())
            assert before=={str(f):f.read_bytes() for f in files if f.exists()}
            phases.append(dict(mode=mode,queries=len(queries),result_rows=rows,matching_errors=matching_errors))
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,groups=groups,phases=phases,failures=failures,
        implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    if args.output: args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__': raise SystemExit(main())
