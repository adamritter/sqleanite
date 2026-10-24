#!/usr/bin/env python3
"""Compare aggregate ORDER BY/HAVING, aliases and evaluation order.

Compare exact CLI bytes and ordinary positive error status against pinned SQLite.
Keep every mismatch, including unsupported syntax and evaluation-order differences.
Verify that read queries preserve all main/WAL bytes. NUL suffixes are not visible
through CLI output; complete byte representatives are separate Core examples.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def corpus(seed, count):
    rng = random.Random(seed)
    values = ['NULL','1','1.0','2','-3',"'4'","'x'","'A'","'a'","X'31'"]
    setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v);'+''.join(f'INSERT INTO t VALUES({i},{v});' for i,v in enumerate(values+rng.choices(values,k=10),1))
    setup+='CREATE TABLE e(id INTEGER PRIMARY KEY,v);CREATE TABLE o(id INTEGER PRIMARY KEY,v);INSERT INTO o VALUES(1,9223372036854775807),(2,1);'
    results=['count(*)','count(v)','sum(v)','avg(v)','total(v)','min(v)','max(v)','coalesce(sum(v),0)','sum(v)+count(*)','min(v COLLATE NOCASE)']
    orders=['1','x DESC','abs(-9223372036854775808)','v','count(*)','sum(abs(-9223372036854775808))','min(v) COLLATE NOCASE','1 NULLS LAST','1 COLLATE missing']
    havings=['1','0','NULL','count(*)>1','x IS NOT NULL','x>2','sum(v)>0','abs(-9223372036854775808)>0']
    queries=[]
    for table in ['t','e','o']:
        for result in results:
            for order in orders:
                queries.append(f'SELECT {result} AS x FROM {table} ORDER BY {order};')
                queries.append(f'SELECT {result} AS x FROM {table} ORDER BY {order} LIMIT 0;')
            for having in havings:
                queries.append(f'SELECT {result} AS x FROM {table} HAVING {having};')
    for _ in range(count):
        result=rng.choice(results);table=rng.choice(['t','e','o']);having=rng.choice(havings);order=rng.choice(orders)
        tail=rng.choice(['',' LIMIT 0',' LIMIT 1 OFFSET 1',' LIMIT -1 OFFSET 2'])
        queries.append(f'SELECT {result} AS x FROM {table} HAVING {having} ORDER BY {order}{tail};')
    for result in ['count(*)','sum(1)','min(2)','avg(1)+count(*)']:
        for having in ['1','0','NULL','count(*)=1','x>0']:
            queries += [f'SELECT {result} AS x HAVING {having} ORDER BY x;',f'SELECT {result} AS x WHERE 0 HAVING {having} ORDER BY 1;']
        queries += [f'SELECT {result} ORDER BY abs(-9223372036854775808);',f'SELECT {result} ORDER BY sum(abs(-9223372036854775808));']
    queries += [
      'SELECT 1 ORDER BY sum(abs(-9223372036854775808));',
      'SELECT 1 WHERE 0 ORDER BY count(*);',
      'SELECT 1 ORDER BY sum(missing);',
      'SELECT 1 ORDER BY count(*),no_function(1);',
      'SELECT 1 ORDER BY count(*) COLLATE missing;',
      'SELECT count(*),0 AND 0x10000000000000000 ORDER BY 1;',
      'SELECT count(*) AS c FROM t HAVING c>2;',
      'SELECT sum(v) AS v FROM t HAVING v>2;',
      'SELECT count(*) FROM e HAVING v IS NULL;',
      'SELECT count(*) FROM t ORDER BY missing;',
      'SELECT count(*) FROM t ORDER BY 2;',
      'SELECT count(*) FROM t ORDER BY no_function(v);',
      'SELECT count(*) FROM t ORDER BY min(v COLLATE missing);',
      'SELECT count(*) FROM t HAVING missing LIMIT 0;',
      'SELECT 1 FROM t ORDER BY count(*);',
      'SELECT 1 ORDER BY count(*);',
      'SELECT 1 HAVING count(*)>0;',
      'SELECT DISTINCT count(*) FROM t HAVING count(*)>0 ORDER BY 1;',
      'SELECT sum(v) FROM o HAVING 0;',
      'SELECT count(*) FROM o HAVING 0 ORDER BY sum(v);',
      'SELECT v,count(*) FROM t GROUP BY v HAVING count(*)>1 ORDER BY count(*) DESC;',
    ]
    return setup,queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353790)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-aggregate-tail-') as tmp:
        for mode in ['--verified-file','--verified-wal-file']:
            folder=Path(tmp)/mode;folder.mkdir()
            def run(sql):
                q=folder/'query.sql';q.write_text(sql)
                l=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(folder/'lean.db'),str(q)],capture_output=True,timeout=120)
                r=subprocess.run([args.sqlite,'-batch','-bail',str(folder/'sqlite.db')],input=sql.encode(),capture_output=True,timeout=120)
                return l,r
            l,r=run(setup);assert l.returncode==r.returncode==0,(l.stderr,r.stderr)
            def snapshot():return {f.name:f.read_bytes() for f in folder.iterdir() if f.name in ['lean.db','lean.db-wal','sqlite.db','sqlite.db-wal']}
            before=snapshot();errors=0
            for sql in queries:
                l,r=run(sql);same=(l.returncode==r.returncode==0 and l.stdout==r.stdout) or (l.returncode>0 and r.returncode>0)
                if not same:
                    def out(x):return dict(code=x.returncode,stdout=x.stdout.decode('latin1'),stderr=x.stderr.decode('latin1'))
                    failures.append(dict(mode=mode,sql=sql,lean=out(l),sqlite=out(r)))
                elif l.returncode:errors+=1
            assert before==snapshot(),'compound read changed input bytes'
            phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors))
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
