#!/usr/bin/env python3
"""Compare LIKELY, UNLIKELY and LIKELIHOOD SQL behavior in both file modes.

Successful reads compare exact CLI bytes, including typed/hex projections.
Errors compare positive exit status, not exact codes/messages. Read queries must
preserve main/WAL bytes. This checks semantic behavior, not planner performance.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]


def corpus(seed,count):
    rng=random.Random(seed)
    values=['NULL','0','1','1.0','-2','1.25',"'1'","'x'","'A'","'a'","X'31'"]
    setup=''
    for table,affinity in [('t',''),('tx','TEXT'),('tn','NUMERIC')]:
        setup+=f'CREATE TABLE {table}(id INTEGER PRIMARY KEY,v {affinity},g);'
        for i,v in enumerate(values+rng.choices(values,k=8),1):setup+=f'INSERT INTO {table} VALUES({i},{v},{i%3});'
    setup+='CREATE TABLE e(id INTEGER PRIMARY KEY,v,g);'
    probabilities=['0','1','0.0','1.0','.5','5e-1','0e999','1e-999','1e999','1.01','+0.5','-0.0',
        '0.5 COLLATE binary',"'0.5'",'NULL','v','CAST(0.5 AS REAL)','0.5+0.0','(0.5)']
    wrappers=['likely({})','unlikely({})']+['likelihood({},'+p+')' for p in probabilities]
    queries=[]
    for table in ['t','tx','tn','e']:
        for wrapper in wrappers:
            expression=wrapper.format('v')
            queries.append(f'SELECT id,typeof({expression}),hex({expression}) FROM {table} ORDER BY id;')
            queries.append(f"SELECT id FROM {table} WHERE {expression}=1 ORDER BY id;")
            queries.append(f"SELECT id FROM {table} WHERE {expression} IN ('1',2) ORDER BY id;")
            queries.append(f'SELECT {expression},count(*) FROM {table} GROUP BY 1 ORDER BY 1;')
    for _ in range(count):
        table=rng.choice(['t','tx','tn','e']); wrapper=rng.choice(wrappers)
        value=rng.choice(['v','v COLLATE NOCASE','CAST(v AS TEXT)','CAST(v AS NUMERIC)',
            'v=1','v IS NULL','v IS NOT NULL','v=1 AND abs(-9223372036854775808)',
            'v=1 OR abs(-9223372036854775808)','NULL AND abs(-9223372036854775808)',
            'count(*)','min(v)','group_concat(v)'])
        expression=wrapper.format(value)
        result=rng.choice([f'typeof({expression}),hex({expression}) AS x',f'{expression} AS x',
            f'{expression}=1 AS x',f"{expression}='1' AS x",f'id,{expression} AS x'])
        where=rng.choice(['', ' WHERE 0',' WHERE id=1',' WHERE '+wrapper.format('v=1')])
        group=rng.choice(['',' GROUP BY g',' GROUP BY '+wrapper.format('v')])
        having=rng.choice(['',' HAVING '+wrapper.format('count(*)>0')]) if group else ''
        tail=rng.choice(['',' ORDER BY x',' LIMIT 0',' LIMIT 1 OFFSET 1'])
        queries.append(f'SELECT {result} FROM {table}{where}{group}{having}{tail};')
    for wrapper in ['likely({})','unlikely({})','likelihood({},0.5)']:
        for expr in ['0','1','NULL','0 AND abs(-9223372036854775808)','1 OR abs(-9223372036854775808)',
            '0 AND missing','CAST(1 AS TEXT)',"CAST('1' AS INTEGER)"]:
            v=wrapper.format(expr)
            queries += [f'SELECT {v};',f'SELECT {v} AND abs(-9223372036854775808);',
                f'SELECT {v} OR abs(-9223372036854775808);',f'SELECT 1 WHERE {v};']
    queries += [
        'SELECT likely();','SELECT unlikely(1,2);','SELECT likelihood(1);','SELECT likely(*) FROM e LIMIT 0;',
        'SELECT likelihood(1,0) LIMIT 0;','SELECT 0 AND likelihood(1,0);','SELECT 1 OR likelihood(1,0);',
        "SELECT likely(CAST(1 AS TEXT))=1,unlikely(CAST(1 AS INTEGER))='1';",
        "SELECT likely(v) FROM tx UNION SELECT v FROM tn ORDER BY likely(v);",
        'SELECT v FROM t ORDER BY likely(1);', 'SELECT v,count(*) FROM t GROUP BY likely(1);',
        'SELECT count(*) FROM t GROUP BY likely(1);', 'SELECT likely(count(*)) AS x FROM t HAVING x>0;',
        'SELECT likely(DISTINCT v) FROM t ORDER BY id;', 'SELECT likelihood(DISTINCT v,0.5) FROM t ORDER BY id;',
        'SELECT likely(v) AS x FROM t WHERE x>0 ORDER BY id;',
        'SELECT likely(likely(v)) FROM tx WHERE unlikely(likely(v))=1;',
        'SELECT likely(abs(-9223372036854775808)) FROM e;',
        'SELECT 1 WHERE likely(NULL AND abs(-9223372036854775808));',
        'SELECT 1 WHERE NOT likely(NULL AND abs(-9223372036854775808));',
        'SELECT 1 WHERE unlikely(0 AND abs(-9223372036854775808));',
        'SELECT 1 WHERE likely(1 OR abs(-9223372036854775808));',
        'SELECT 1 WHERE (NULL AND abs(-9223372036854775808)) COLLATE binary;',
        'SELECT 1 WHERE NOT ((NULL AND abs(-9223372036854775808)) COLLATE binary);',
        'SELECT 1 WHERE likely(NULL AND abs(-9223372036854775808)) COLLATE binary;',
        'SELECT 1 WHERE (1 OR abs(-9223372036854775808)) COLLATE missing;',
        'SELECT likelihood(7,0x10000000000000000) LIMIT 0;',
        'SELECT likelihood(7,1e-9999);',

    ]
    return setup,queries

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353870)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-probability-') as tmp:
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
            assert before==snapshot(),'aggregate read changed input bytes'
            phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors))
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
