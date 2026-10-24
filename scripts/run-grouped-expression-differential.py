#!/usr/bin/env python3
"""Compare grouped expressions, HAVING, ORDER BY, DISTINCT and evaluation order.

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
    rng=random.Random(seed)
    vals=['NULL','1','1.0','2','-3',"'4'","'a'","'A'","'a '","X'31'"]
    setup='CREATE TABLE t(id INTEGER PRIMARY KEY,g,v,w TEXT);CREATE TABLE e(id INTEGER PRIMARY KEY,g,v,w TEXT);'
    for i,g in enumerate(vals+rng.choices(vals,k=20),1):
        setup+=f"INSERT INTO t VALUES({i},{g},{rng.choice(['NULL','1','1.0','-2','5'])},'row{i}');"
    setup+="CREATE TABLE o(id INTEGER PRIMARY KEY,g,v,w TEXT);INSERT INTO o VALUES(1,1,9223372036854775807,'a'),(2,1,1,'b'),(3,2,2,'c'),(4,3,3,'d');"
    projections=['g,count(*) AS x','g,id,w,min(v) AS x','g,id,w,min(v),max(v),min(v) AS x',
      'g,sum(v)+count(*) AS x','g,count(DISTINCT v) AS x','g,min(v COLLATE NOCASE) AS x',
      'g+0 AS k,count(*) AS x','lower(g) AS k,count(*) AS x','g COLLATE NOCASE AS k,count(*) AS x',
      'count(*) AS x','abs(-9223372036854775808)+count(*) AS x']
    groups=['g','g COLLATE NOCASE','g COLLATE RTRIM','g+0','lower(g)','g,v']
    havings=['',' HAVING 0',' HAVING NULL',' HAVING 1',' HAVING count(*)>1',' HAVING x>1',' HAVING g IS NOT NULL',
      ' HAVING g>1',' HAVING g>1 AND count(*)>0',' HAVING g>1 OR count(*)>1',
      ' HAVING abs(-9223372036854775808)>0']
    orders=['',' ORDER BY 1',' ORDER BY 1 DESC',' ORDER BY x DESC',' ORDER BY count(*) DESC,g',
      ' ORDER BY g',' ORDER BY g DESC',' ORDER BY g NULLS LAST',' ORDER BY abs(-9223372036854775808)']
    windows=['',' LIMIT 0',' LIMIT 1',' LIMIT 2 OFFSET 1']
    queries=[]
    for table in ['t','e','o']:
      for projection in projections:
        for group in groups[:3]:
          queries.append(f'SELECT {projection} FROM {table} GROUP BY {group} HAVING count(*)>0 ORDER BY x DESC;')
    for _ in range(count):
      projection=rng.choice(projections);table=rng.choice(['t','e','o']);group=rng.choice(groups)
      having=rng.choice(havings);order=rng.choice(orders);window=rng.choice(windows)
      distinct=rng.choice(['','DISTINCT ']);where=rng.choice(['',' WHERE id>2',' WHERE 0'])
      queries.append(f'SELECT {distinct}{projection} FROM {table}{where} GROUP BY {group}{having}{order}{window};')
    queries += [
      "SELECT g||'',max(id),g FROM t GROUP BY g||'' COLLATE NOCASE;",
      "SELECT g||'',max(id),g FROM t GROUP BY 1 COLLATE NOCASE;",
      "SELECT g||'',max(id),g FROM t GROUP BY 1 COLLATE NOCASE ORDER BY 1;",
      "SELECT +g,+g,max(id),typeof(+g) FROM t GROUP BY +g;",
      "SELECT +g,max(id),typeof(+g) FROM t GROUP BY +g;",
      "SELECT g,count(*) FROM t GROUP BY g ORDER BY g NULLS FIRST LIMIT 1;",
      'SELECT g+0 AS k,count(*) FROM t GROUP BY k;',
      'SELECT g+0 AS k,count(*) FROM t GROUP BY 1;',
      'SELECT g+0 AS k,count(*) FROM t GROUP BY 1 COLLATE NOCASE;',
      'SELECT g+0,g+0,count(*),min(id),max(id) FROM t GROUP BY g+0;',
      'SELECT count(*) AS g FROM t GROUP BY g;',
      'SELECT count(*) AS g FROM t GROUP BY 1;',
      'SELECT count(*) FROM t GROUP BY missing LIMIT 0;',
      'SELECT count(*) FROM t GROUP BY g COLLATE missing LIMIT 0;',
      'SELECT g,sum(v) FROM o GROUP BY g HAVING 0;',
      'SELECT g,sum(v) FROM o GROUP BY g HAVING NULL;',
      'SELECT g,sum(v) FROM o GROUP BY g HAVING g>1;',
      'SELECT g,sum(v) FROM o GROUP BY g HAVING g>1 OR count(*)=1;',
      'SELECT g,sum(v) FROM o GROUP BY g ORDER BY g DESC LIMIT 1;',
      'SELECT g,sum(v) FROM o GROUP BY g ORDER BY g ASC LIMIT 1;',
      'SELECT g,count(*) FROM t GROUP BY g ORDER BY count(*) DESC;',
      'SELECT DISTINCT count(*) FROM t GROUP BY g ORDER BY 1 DESC LIMIT 2;',
      'SELECT g,abs(-9223372036854775808) FROM t GROUP BY g LIMIT 1 OFFSET 100;',
      'SELECT g,abs(-9223372036854775808) FROM t GROUP BY g HAVING 0;',
      'SELECT g,count(*) FROM t WHERE 0 GROUP BY g HAVING abs(-9223372036854775808)>0;',
      'SELECT count(*) GROUP BY 1+0 HAVING count(*)>0;',
    ]
    for expression in ["g||''",'+g','CAST(g AS TEXT)','lower(g)']:
      for group in ['1','k',expression]:
        for order in ['', ' ORDER BY 1',' ORDER BY 1 COLLATE NOCASE', ' ORDER BY k DESC LIMIT 2 OFFSET 1']:
          for distinct in ['', 'DISTINCT ']:
            queries.append(f'SELECT {distinct}{expression} AS k,max(id),g FROM t GROUP BY {group} COLLATE NOCASE{order};')
    queries += [
      'SELECT g+1 AS k,count(*) FROM t WHERE k>1 GROUP BY k;',
      'SELECT g AS x,count(*) FROM t WHERE x IS NOT NULL GROUP BY x;',
      'SELECT count(*) AS x FROM t WHERE x>1 GROUP BY g;',
      'SELECT g,count(*) AS x FROM t GROUP BY g HAVING x>1 ORDER BY x DESC NULLS LAST LIMIT 2;',
    ]
    return setup,queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353810)
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
            assert before==snapshot(),'grouped read changed input bytes'
            phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors))
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
