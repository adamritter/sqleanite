#!/usr/bin/env python3
"""Compare compound ORDER BY/LIMIT through both production file modes.

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
    values = ['NULL', '1', '1.0', '0', '-1', "'A'", "'a'", "'a '", "'B'", "'b'", "X'41'", "CAST(X'410062' AS TEXT)", "CAST(X'610042' AS TEXT)"]
    setup = ''
    for table in ['t', 'u']:
        setup += f'CREATE TABLE {table}(id INTEGER PRIMARY KEY,v);'
        setup += ''.join(f'INSERT INTO {table} VALUES({i},{v});' for i,v in enumerate(values + rng.choices(values,k=10),1))
    queries = []
    ops = ['UNION ALL','UNION','INTERSECT','EXCEPT']
    for op in ops:
        for coll in ['', ' COLLATE BINARY', ' COLLATE NOCASE', ' COLLATE RTRIM']:
            for order in ['1','2','x','v','v||\'\'','2 DESC,1','1 NULLS LAST','1 DESC NULLS FIRST','1 COLLATE NOCASE','1 COLLATE RTRIM DESC']:
                for tail in ['', ' LIMIT 3 OFFSET 2', ' LIMIT 0']:
                    queries.append(f'SELECT v{coll} AS x,id%3 AS k FROM t {op} SELECT v,id%2 FROM u ORDER BY {order}{tail};')
            for limit in ['0','1','5','-1','1 OFFSET 1','2 OFFSET 50','2,3']:
                queries.append(f'SELECT v{coll} FROM t {op} SELECT v FROM u LIMIT {limit};')
        queries += [f'SELECT 1 AS a,2 AS b {op} SELECT 3 AS c,0 AS d ORDER BY d;',f'SELECT 1 AS a,2 AS b {op} SELECT 3 AS c,0 AS a ORDER BY a;',f'SELECT v||\'\' AS x FROM t {op} SELECT v FROM u ORDER BY v||\'\';',f'SELECT v AS x FROM t {op} SELECT v FROM u ORDER BY t.v;',f'SELECT min(v) AS x FROM t {op} SELECT max(v) FROM u ORDER BY x DESC;',f'SELECT v,count(*) FROM t GROUP BY v {op} SELECT v,count(*) FROM u GROUP BY v ORDER BY 2 DESC,1;',f'SELECT 1 {op} SELECT abs(-9223372036854775808) LIMIT 0;',f'SELECT 1 {op} SELECT missing LIMIT 0;',f'SELECT 1 {op} SELECT 1,2 LIMIT 0;',f'SELECT 1 COLLATE missing {op} SELECT 2 LIMIT 0;']
    for _ in range(count):
        width=rng.randint(1,3)
        arms=[]
        for _ in range(rng.randint(2,5)):
            cols=[rng.choice(values)+rng.choice(['',' COLLATE NOCASE',' COLLATE RTRIM']) for _ in range(width)]
            arms.append('SELECT '+','.join(cols)+(' WHERE 0' if rng.randrange(8)==0 else ''))
        q=arms[0]
        for arm in arms[1:]: q+=' '+rng.choice(ops)+' '+arm
        q+=' ORDER BY '+','.join(str(i)+rng.choice(['',' DESC',' NULLS LAST',' DESC NULLS FIRST']) for i in rng.sample(range(1,width+1),rng.randint(1,width)))
        q+=rng.choice(['',' LIMIT 0',' LIMIT 1',' LIMIT 2 OFFSET 1',' LIMIT -1 OFFSET 2'])
        queries.append(q+';')
    queries += [
      'SELECT CASE WHEN 1 THEN 2 END UNION SELECT 3 ORDER BY CASE WHEN 1 THEN 4 END;',
      'SELECT 1+(2*3) UNION SELECT 4 ORDER BY (1+2)*3;',
      'SELECT 1.0 UNION ALL SELECT 2 ORDER BY 1.0;',
      'SELECT CAST(1 AS TEXT) UNION ALL SELECT 2 ORDER BY CAST(1 AS TEXT);',
      'SELECT v+1 AS x FROM t UNION ALL SELECT 2 ORDER BY x;',
      'SELECT v+1 AS x FROM t UNION ALL SELECT 2 ORDER BY v+1;',
      'SELECT 1 UNION ALL SELECT abs(-9223372036854775808) LIMIT 1;',
      'SELECT abs(-9223372036854775808) UNION ALL SELECT 2 LIMIT 1 OFFSET 1;',
      'SELECT 1 UNION SELECT 1 UNION ALL SELECT abs(-9223372036854775808) LIMIT 1;',
      'SELECT 1 WHERE 0 INTERSECT SELECT abs(-9223372036854775808) LIMIT 1;',
      'SELECT 1 WHERE 0 INTERSECT SELECT abs(-9223372036854775808) ORDER BY 1;',
      'SELECT abs(-9223372036854775808) FROM t UNION ALL SELECT 1 LIMIT 1 OFFSET 24;',
      'SELECT v FROM t UNION ALL SELECT v FROM u ORDER BY 0 LIMIT 0;',
      'SELECT v FROM t UNION ALL SELECT v FROM u ORDER BY missing LIMIT 0;',
      'SELECT v FROM t UNION SELECT v FROM u ORDER BY v+1;',
      'SELECT 1.0 UNION SELECT 2 ORDER BY 1.00;',
      'SELECT 1.0 UNION SELECT 2 ORDER BY 1.0;',
      'SELECT v FROM t UNION ALL SELECT v FROM u ORDER BY 1 COLLATE missing LIMIT 0;',
      'SELECT a.v FROM t AS a JOIN t AS b ON a.id=b.id UNION SELECT v FROM u ORDER BY 1 DESC LIMIT 4;',
      "SELECT 'A' COLLATE NOCASE INTERSECT SELECT 'a' ORDER BY 1 COLLATE BINARY;",
      "SELECT 'A' COLLATE BINARY INTERSECT SELECT 'a' ORDER BY 1 COLLATE NOCASE;",
      "SELECT 'A' COLLATE NOCASE UNION SELECT 'a' ORDER BY 1 DESC;",
      'SELECT 1 AS x UNION ALL SELECT 2 ORDER BY +x;',
      'SELECT 1 AS x UNION ALL SELECT 2 ORDER BY +1;',
    ]
    return setup,queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353760)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-compound-tail-') as tmp:
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
