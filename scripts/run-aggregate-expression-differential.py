#!/usr/bin/env python3
"""Compare bound scalar aggregate arguments, DISTINCT and expression WHERE.

The final result is compared byte-for-byte and errors by rejection status.
Input images are independent and reads must preserve their bytes. This covers
ordinary single-table aggregate terms, not nested result expressions, grouping,
HAVING or aggregate ORDER BY. All generated mismatches remain in the report.
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
    p.add_argument('--seed',type=int,default=353550)
    p.add_argument('--random-cases',type=int,default=200)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed)
    pool=['NULL','0','0.0','-0.0','1','1.0','-2','2.5','3',"'1'","'1.0'","'xyz'","X'31'",'1e100','5e-324']
    setup=['CREATE TABLE t(id INTEGER PRIMARY KEY,v,w INTEGER);','BEGIN;']
    for i in range(1,101): setup.append(f'INSERT INTO t VALUES({i},{rng.choice(pool)},{rng.randrange(-10,11)});')
    setup+=['COMMIT;','CREATE TABLE empty(id INTEGER PRIMARY KEY,v,w);',
            'CREATE TABLE ov(id INTEGER PRIMARY KEY,v);INSERT INTO ov VALUES(1,9223372036854775807),(2,1);']
    functions=['count','sum','avg','total','min','max'];expressions=['v','+v','v+1','v*2','w','w%3','CASE WHEN w>0 THEN v ELSE NULL END','length(v)','id IN (1,2,3)','id%4','1','NULL']
    queries=[]
    for _ in range(args.random_cases):
        terms=[]
        for _ in range(rng.randrange(1,6)):
            if rng.randrange(8)==0: terms.append('count(*)')
            else: terms.append(f"{rng.choice(functions)}({rng.choice(['','DISTINCT '])}{rng.choice(expressions)})")
        where=rng.choice(['',' WHERE v+1>2',' WHERE w%3=1',' WHERE id IN (1,2,3,50)',' WHERE id<0',' WHERE v IS NULL',' WHERE w BETWEEN -3 AND 3',' WHERE id=1 AND v+1>0'])
        tail=rng.choice(['',' LIMIT 0',' LIMIT 1 OFFSET 0',' LIMIT -1 OFFSET 1',' LIMIT 0 OFFSET NULL'])
        distinct=rng.choice(['','DISTINCT '])
        queries.append(f"SELECT {distinct}{','.join(terms)} FROM t{where}{tail};")
    for table in ['t','empty']:
        for term in ['count(abs(-9223372036854775808))','sum(abs(-9223372036854775808))','count(missing)','count(unknown_function())','count(sum(v))','sum(*)','count()','count(DISTINCT v,w)']:
            for tail in ['', ' LIMIT 0', ' LIMIT 1 OFFSET 1']:
                queries.append(f'SELECT {term} FROM {table}{tail};')
    queries += ['SELECT count(*) FROM t WHERE abs(-9223372036854775808);',
                'SELECT count(*) FROM empty WHERE abs(-9223372036854775808);',
                'SELECT count(*) FROM t WHERE abs(-9223372036854775808) LIMIT 0;',
                'SELECT sum(v),count(*) FROM ov;', 'SELECT sum(v) FROM ov LIMIT 0;',
                'SELECT sum(v) FROM ov LIMIT 1 OFFSET 1;',
                'SELECT count(DISTINCT v),sum(DISTINCT +v),avg(DISTINCT v),total(DISTINCT v) FROM t;',
                'SELECT count(x.v+1),total(x.w) FROM t AS x WHERE x.w+1>2;',
                'SELECT count(t.v) FROM t AS x LIMIT 0;']
    queries += [f'SELECT {fn}({q}.v) FROM t AS x{tail};'
                for fn in functions for q in ['x','t','unknown'] for tail in ['', ' LIMIT 0']]
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-aggregate-expressions-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            d=pathlib.Path(tmp)/mode;d.mkdir()
            def run(sql):
                q=d/'query.sql';q.write_text(sql)
                a=subprocess.run([str(args.lean),mode,str(d/'lean.db'),str(q)],text=True,encoding='latin-1',capture_output=True,timeout=120)
                b=subprocess.run([args.sqlite,'-batch','-bail',str(d/'sqlite.db')],input=sql,text=True,encoding='latin-1',capture_output=True,timeout=120)
                return a,b
            a,b=run('\n'.join(setup));assert a.returncode==b.returncode==0,(a.stderr,b.stderr)
            files=[d/'lean.db',d/'lean.db-wal'];before={str(f):f.read_bytes() for f in files if f.exists()}
            matching_errors=0;rows=0
            for sql in queries:
                a,b=run(sql)
                same=(a.returncode==b.returncode==0 and a.stdout==b.stdout) or (a.returncode!=0 and b.returncode!=0)
                if not same: failures.append(dict(mode=mode,sql=sql,lean=dict(code=a.returncode,stdout=a.stdout,stderr=a.stderr),sqlite=dict(code=b.returncode,stdout=b.stdout,stderr=b.stderr)))
                elif a.returncode: matching_errors+=1
                rows+=len(a.stdout.splitlines())
            assert before=={str(f):f.read_bytes() for f in files if f.exists()}
            phases.append(dict(mode=mode,queries=len(queries),result_rows=rows,matching_errors=matching_errors))
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


if __name__=='__main__':raise SystemExit(main())
