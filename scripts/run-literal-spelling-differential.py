#!/usr/bin/env python3
"""Compare REAL token spelling in expression identity and ordinary evaluation.

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
    spellings = ['1.0','1.00','1e0','1E0','1e+0','1e00','0.0','00.0','0.00','1.25','1.250','12.5e-1','2.0','2e0']
    setup = 'CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1.0),(2,2.0),(3,NULL);'
    queries = []
    for a in spellings:
        for b in spellings:
            for template in ['{}','abs({})','CAST({} AS TEXT)','CASE WHEN 1 THEN {} END']:
                left,right=template.format(a),template.format(b)
                queries.append(f'SELECT {left} UNION ALL SELECT 99 ORDER BY {right};')
    for _ in range(count):
        a,b=rng.choices(spellings,k=2)
        queries += [f'SELECT v+{a} AS x FROM t UNION ALL SELECT {b} ORDER BY v+{b};',
                    f'SELECT {a}+{b} UNION SELECT 3 ORDER BY {a}+{b};',
                    f'SELECT {a}={b},{a}+{b},typeof({a}),quote({a});']
    queries += [
      'SELECT 1.0 AS x UNION ALL SELECT 2 ORDER BY x;',
      'SELECT 1.0 AS x,abs(1.0) FROM t UNION ALL SELECT 2,3 ORDER BY abs(x);',
      'SELECT 1.0 AS x,abs(1.00) FROM t UNION ALL SELECT 2,3 ORDER BY abs(x);',
      'SELECT 0 AND 1.0 UNION ALL SELECT 2 ORDER BY 0 AND 1.00;',
      'SELECT v+1.0 FROM t UNION SELECT 2 ORDER BY v+1.00;',
      'SELECT v+1.0 FROM t UNION SELECT 2 ORDER BY v+1.0;',
      'SELECT -1.0 UNION SELECT 2 ORDER BY -1.00;',
      'SELECT 1.0 COLLATE BINARY UNION ALL SELECT 2 ORDER BY 1.00;',
      'SELECT 1.0,1.00 UNION ALL SELECT 2,3 ORDER BY 1.00;',
      'SELECT 1.0 UNION SELECT 1.00 ORDER BY 1.00;',
      'SELECT 1e999 UNION ALL SELECT 2 ORDER BY 1E999;',
      'SELECT 1e999 UNION ALL SELECT 2 ORDER BY 1e999;',
    ]
    return setup,queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353770)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-literal-spelling-') as tmp:
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
