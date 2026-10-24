#!/usr/bin/env python3
"""Compare ORDER BY expressions, output aliases, ordinals and LIMIT timing.

SQL runs on independent files in both production modes against the pinned
SQLite CLI. Exact output bytes and success/rejection are compared without row
sorting or normalization. Reads must leave main/WAL bytes unchanged. All
mismatches are retained; matching errors do not compare diagnostic wording.
This is a bounded single-source and source-free ordering corpus, not SQL-wide
or planner-wide equivalence.
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
    p.add_argument('--seed', type=int, default=353670)
    p.add_argument('--random-cases', type=int, default=200)
    p.add_argument('--output', type=pathlib.Path)
    args = p.parse_args()
    rng = random.Random(args.seed)
    setup = ['CREATE TABLE t(id INTEGER PRIMARY KEY,v,w,ntext TEXT);',
             'CREATE TABLE empty(id INTEGER PRIMARY KEY,v,w,ntext TEXT);',
             'CREATE TABLE errors(id INTEGER PRIMARY KEY,v,w);',
             'CREATE TABLE faults(id INTEGER PRIMARY KEY,v,w);',
             'INSERT INTO errors VALUES(1,1,2),(2,-9223372036854775808,1),(3,3,0);']
    values = ['NULL','0','1','2','-3','0.5',"'4'","'xyz'","X'41'",'9007199254740993','9007199254740992.0']
    texts = ["'A'","'b'","'a'","'c'","''",'NULL']
    for i in range(1,31):
        setup.append(f'INSERT INTO t VALUES({i},{rng.choice(values)},{rng.randrange(-4,5)},{rng.choice(texts)});')
    for i in range(1,25):
        value = '-9223372036854775808' if rng.randrange(5)==0 else str(rng.randrange(-25,26))
        setup.append(f'INSERT INTO faults VALUES({i},{value},{rng.randrange(-6,7)});')
    columns = ['id,v,w', 'id AS v,v AS id,w', 'id,v+1 AS score', '*',
               'v AS k,typeof(v)', 'id,CASE WHEN w<0 THEN v ELSE w END AS score']
    orders = ['v+1','-id','w','lower(ntext)','score','k','1','2','3','0','-1','+1','1.0',
              '(1)','((2))','5','v','id','t.v','coalesce(v,0)','v*0+id',
              'CASE WHEN w THEN v ELSE id END', 'w+1,id DESC','"v"',
              '2147483647','2147483648','-2147483648','+(-1)','"score"','v COLLATE BINARY','(v COLLATE BINARY)+1']
    queries = []
    for projection in columns:
        for ordering in orders:
            for suffix in ['', ' LIMIT 4 OFFSET 2', ' LIMIT 0']:
                queries.append(f'SELECT {projection} FROM t ORDER BY {ordering}{suffix};')
    for _ in range(args.random_cases):
        projection = rng.choice(columns)
        distinct = 'DISTINCT ' if rng.randrange(3)==0 else ''
        ordering = rng.choice(orders)+rng.choice(['',' DESC'])
        where = rng.choice(['',' WHERE id>8',' WHERE w<0',' WHERE 0'])
        limit = rng.choice(['',' LIMIT 1',' LIMIT 7 OFFSET 3',' LIMIT 0',' LIMIT -1 OFFSET 2'])
        queries.append(f'SELECT {distinct}{projection} FROM t{where} ORDER BY {ordering}{limit};')
    for table in ['t','empty']:
        queries += [f'SELECT v AS k FROM {table} ORDER BY k;',
                    f'SELECT v AS id,id AS v FROM {table} ORDER BY id;',
                    f'SELECT v AS id,id AS v FROM {table} ORDER BY t.id;',
                    f'SELECT * FROM {table} ORDER BY 4;',
                    f'SELECT id FROM {table} ORDER BY 2 LIMIT 0;',
                    f'SELECT id FROM {table} ORDER BY unknown_function() LIMIT 0;',
                    f'SELECT id FROM {table} ORDER BY missing LIMIT 0;']
    for expression in ['abs(v)','id,abs(v)','id,CASE WHEN id=2 THEN abs(v) ELSE v END']:
        for ordering in ['id','w','-w','v+0','2']:
            for limit in ['', ' LIMIT 1',' LIMIT 1 OFFSET 1',' LIMIT 1 OFFSET 2',' LIMIT 0']:
                queries.append(f'SELECT {expression} FROM errors ORDER BY {ordering}{limit};')
    queries += ['SELECT 3 AS x,1 AS y ORDER BY x;', 'SELECT 3,1 ORDER BY 2;',
                'SELECT 3,1 ORDER BY 3 LIMIT 0;', 'SELECT 3,1 ORDER BY 1+1;',
                'SELECT abs(-9223372036854775808) ORDER BY 1 LIMIT 0;',
                'SELECT abs(-9223372036854775808) ORDER BY 1 LIMIT 1 OFFSET 1;']
    queries += ['SELECT id AS v FROM t ORDER BY v+0;',
                'SELECT v AS x,w AS x,id FROM t ORDER BY x;',
                'SELECT id FROM errors ORDER BY id DESC,abs(v) LIMIT 1;',
                'SELECT id FROM errors WHERE id=2 ORDER BY abs(v);',
                'SELECT id AS z FROM t WHERE id=2 ORDER BY z+1;',
                'SELECT 1 ORDER BY 2147483648;', 'SELECT 1 ORDER BY -2147483648;',
                'SELECT 1 ORDER BY abs(-9223372036854775808);',
                'SELECT 1 ORDER BY unknown_function() LIMIT 0;']
    for ordering in ['w','-w','w,id DESC','id DESC,abs(v)','abs(v)']:
        for limit in [0,1,3,8]:
            for offset in [0,1,4]:
                for where in ['', ' WHERE id>8']:
                    queries.append(f'SELECT id,abs(v) FROM faults{where} ORDER BY {ordering} LIMIT {limit} OFFSET {offset};')
    failures, phases = [], []
    with tempfile.TemporaryDirectory(prefix='sqleanite-order-expression-') as tmp:
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
