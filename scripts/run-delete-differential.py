#!/usr/bin/env python3
"""Differential DELETE with scalar predicates, indexes and statement atomicity.

Every case starts with a fresh copy of independently created databases. Pinned
SQLite compares retained values and integrity. Errors preserve database/WAL
bytes, and transaction rollback is checked in both production file modes.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353500)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed)
    setup=['CREATE TABLE t(id INTEGER PRIMARY KEY,a INTEGER,b NUMERIC,s TEXT);','BEGIN;']
    for i in range(1,121):
        b=rng.choice(['NULL','1','1.5',"'x'",'0','-5'])
        setup.append(f"INSERT INTO t VALUES({i},{rng.randrange(-100,100)},{b},'s-{i}');")
    setup += ['COMMIT;', 'CREATE INDEX ta ON t(a);','CREATE INDEX ts ON t(s);',
              'CREATE TABLE empty(id INTEGER PRIMARY KEY,a INTEGER);',
              'CREATE TABLE tp(k TEXT PRIMARY KEY,v);',"INSERT INTO tp VALUES('a',1),('b',NULL),('ccc',2);"]
    queries=[
        'DELETE FROM t WHERE id IN (1,3,5);',
        "DELETE FROM tp WHERE k IN ('a','b');",
        'DELETE FROM t WHERE a NOT IN (1,NULL,2);',
        'DELETE FROM t WHERE missing+1 AND 0;', 'DELETE FROM t WHERE 0 AND wrong.id;',
        'DELETE FROM t WHERE a+1>0;', 'DELETE FROM t AS x WHERE x.id%3=0;',
        "DELETE FROM tp WHERE length(k)>1 OR v+0=1;",
        'DELETE FROM t WHERE 0 AND abs(-9223372036854775808);',
        'DELETE FROM t WHERE NOT (NULL OR a+0>0);',
        'DELETE FROM t WHERE a+0>0 OR NULL;',
        'DELETE FROM t WHERE id+0>0;',
        'DELETE FROM empty WHERE abs(-9223372036854775808)+id;',
        'DELETE FROM t WHERE NULL AND abs(-9223372036854775808);',
    ]
    for _ in range(args.random_cases):
        condition=rng.choice([f'id%{rng.randrange(2,10)}={rng.randrange(2)}',
            f'a+{rng.randrange(-50,50)}>0',f'id+0>{rng.randrange(0,125)}',
            "coalesce(b,a)>1", "instr(s,'1')>0", 'a+b<0',
            "s=CAST(id AS TEXT)", 'NOT(a+0>=0 AND b+0)', 'b IS NULL OR id%2=0',
            f'length(s)={rng.randrange(3,6)}'])
        queries.append(f'DELETE FROM t WHERE {condition};')
    errors=['DELETE FROM empty WHERE id IN (1,abs(-9223372036854775808));', 'DELETE FROM t WHERE id=1 OR abs(-9223372036854775808);',
            'DELETE FROM t WHERE abs(-9223372036854775808) AND 0;',
            'DELETE FROM t WHERE unknown_function(a);','DELETE FROM t WHERE wrong.a+1;',
            'DELETE FROM t WHERE unknown_function(id) AND 0;', 'DELETE FROM empty WHERE missing+1;',
            'DELETE FROM empty WHERE abs(-9223372036854775808);']
    observation='SELECT id,typeof(a),quote(a),typeof(b),quote(b),hex(s) FROM t ORDER BY id; SELECT k,typeof(v),quote(v) FROM tp ORDER BY k; PRAGMA integrity_check;'
    failures,phases=[],[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-delete-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            d=pathlib.Path(tmp)/mode;d.mkdir()
            def run(sql):
                q=d/'query.sql';q.write_text(sql)
                a=subprocess.run([str(args.lean),mode,str(d/'lean.db'),str(q)],text=True,capture_output=True,timeout=180)
                b=subprocess.run([args.sqlite,'-batch','-bail',str(d/'sqlite.db')],input=sql,text=True,capture_output=True,timeout=180)
                return a,b
            def observe(name):
                return subprocess.check_output([args.sqlite,'-batch','-bail','-readonly',str(d/name),observation],text=True)
            a,b=run('\n'.join(setup));assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            base={p.name:p.read_bytes() for p in d.iterdir() if p.name in ['lean.db','lean.db-wal','sqlite.db']}
            def restore():
                for p in d.iterdir():
                    if p.name.startswith(('lean.db','sqlite.db')) and p.is_file(): p.unlink()
                for name,data in base.items(): (d/name).write_bytes(data)
            for sql in queries:
                restore();a,b=run(sql)
                if a.returncode!=0 or b.returncode!=0:
                    failures.append(dict(mode=mode,sql=sql,lean=a.stderr,sqlite=b.stderr));continue
                actual,expected=observe('lean.db'),observe('sqlite.db')
                if actual!=expected or not actual.endswith('ok\n'):
                    failures.append(dict(mode=mode,sql=sql,lean=actual,sqlite=expected))
            for sql in errors:
                restore();a,b=run(sql)
                assert a.returncode!=0 and b.returncode!=0,(mode,sql,a.stdout,a.stderr,b.stderr)
                assert all((d/name).read_bytes()==data for name,data in base.items() if name.startswith('lean.db')),(mode,sql,'failure changed bytes')
                assert observe('lean.db')==observe('sqlite.db'),(mode,sql,'failure changed rows')
            restore();a,b=run('BEGIN; DELETE FROM t WHERE a+1>0; ROLLBACK;')
            assert a.returncode==b.returncode==0 and observe('lean.db')==observe('sqlite.db')
            phases.append(dict(mode=mode,deletes=len(queries),matching_errors=len(errors),rollback=True))
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
