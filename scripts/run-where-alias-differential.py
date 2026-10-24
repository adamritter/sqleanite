#!/usr/bin/env python3
"""Compare single-source and source-free WHERE aliases with source-name precedence.

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


def corpus(seed,count):
    rng=random.Random(seed)
    vals=['NULL','1','1.0','2','-3',"'4'","'x'",'9223372036854775807','-9223372036854775808']
    setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v,x INTEGER,"true" INTEGER);CREATE TABLE n(id INTEGER PRIMARY KEY,v);CREATE TABLE e(id INTEGER PRIMARY KEY,v);CREATE TABLE tx(id INTEGER PRIMARY KEY,v TEXT);'
    for i,v in enumerate(vals+rng.choices(vals,k=10),1):
        setup+=f'INSERT INTO t VALUES({i},{v},{i%2},{i%3});INSERT INTO n VALUES({i},{v});INSERT INTO tx VALUES({i},{v});'
    projections=['v AS k','v+1 AS k','abs(v) AS k','typeof(v) AS k','v AS x','v AS true',
      'id AS k,id+1 AS k','count(*) AS k','sum(v) AS k','v AS k,k AS y']
    conditions=['k>1','k IS NULL','k=1',"k='1'",'k IN (1,2,3)','k=1 OR abs(-9223372036854775808)',
      'k=1 AND abs(-9223372036854775808)','x=0','true','true IS TRUE','"k" IS NOT NULL','t.k>0']
    queries=[]
    for table in ['t','n','tx','e']:
      for result in projections:
        for condition in ['k>1','k IS NULL','x=0','true']:
          queries.append(f'SELECT {result} FROM {table} WHERE {condition};')
    for _ in range(count):
      result=rng.choice(projections);table=rng.choice(['t','n','tx','e']);condition=rng.choice(conditions)
      order=rng.choice(['',' ORDER BY id DESC',' ORDER BY k',' ORDER BY 1']);window=rng.choice(['',' LIMIT 0',' LIMIT 2 OFFSET 1'])
      queries.append(f'SELECT {result} FROM {table} WHERE {condition}{order}{window};')
    for result in ['1 AS k','0 AS k','NULL AS k','1 AS true','count(*) AS k','abs(-9223372036854775808) AS k']:
      for condition in ['k>0','k IS NULL','true','k=0 OR abs(-9223372036854775808)']:
        queries.append(f'SELECT {result} WHERE {condition};')
        queries.append(f'SELECT {result} WHERE {condition} LIMIT 0;')
    queries += [
      'SELECT TRUE AS true WHERE true;',
      'SELECT TRUE AS true FROM n WHERE true LIMIT 1;',
      'SELECT count(*) AS k FROM n WHERE 0 AND k>0 GROUP BY v;',
      'SELECT v AS k FROM n WHERE missing.k=1;',
      'SELECT v AS k FROM n WHERE n.k=1;',
      'SELECT v AS k FROM n AS s WHERE k=1 ORDER BY s.id;',
      'SELECT v AS k FROM n AS s WHERE n.v=1;',
      'SELECT v+1 AS v FROM n WHERE v=1;',
      'SELECT 0 AS true WHERE true;',
      'SELECT 0 AS true WHERE true IS TRUE;',
      'SELECT 1 AS k WHERE 0 AND missing;',
      'SELECT 1 AS k WHERE 0 AND no_function(k);',
      'SELECT count(*) AS k FROM n WHERE 0 AND k>0;',
      'SELECT count(*) AS k WHERE 0 AND k>0;',
      'SELECT k AS k FROM n WHERE k>0;',
      'SELECT v AS k FROM n WHERE k>0 GROUP BY k HAVING count(*)>0;',
    ]
    return setup,queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353830)
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
            assert before==snapshot(),'alias read changed input bytes'
            phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors))
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
