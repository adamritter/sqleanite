#!/usr/bin/env python3
"""Compare GROUP_CONCAT and STRING_AGG through both production file modes.

Compare exact CLI bytes and matching positive error status, not error wording or
codes. Hex projections include every result byte, including NUL and invalid UTF-8.
All read queries must preserve main/WAL bytes. Cases include variable separators,
DISTINCT collations, empty input, scalar wrappers, grouping and evaluation timing.
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
    values=['NULL',"''",'1','1.0','-2','1.25','1.0e300',"'A'","'a'","'a '","'b'","X'410042'","X'FF80'","X'31'"]
    separators=['NULL',"''", "','", "'::'", '7', '1.0', "X'00FF'", "'é'"]
    setup=''
    for table,affinity in [('t',''),('tx','TEXT'),('tn','NUMERIC')]:
        setup+=f'CREATE TABLE {table}(id INTEGER PRIMARY KEY,g,v {affinity},s);'
        for i,v in enumerate(values+rng.choices(values,k=10),1):
            sep=rng.choice(separators)
            setup+=f'INSERT INTO {table} VALUES({i},{i%4},{v},{sep});'
    setup+='CREATE TABLE e(id INTEGER PRIMARY KEY,g,v,s);'
    setup+="CREATE TABLE n(id INTEGER PRIMARY KEY,g,v,s);INSERT INTO n VALUES(1,0,NULL,'a'),(2,0,NULL,NULL);"
    setup+="CREATE TABLE z(id INTEGER PRIMARY KEY,g,v,s);INSERT INTO z VALUES(1,0,'','x'),(2,0,'',NULL),(3,1,'','y');"
    aggregates=['group_concat(v)',"group_concat(v,'|')",'group_concat(v,s)', 'string_agg(v,s)',
        'group_concat(DISTINCT v)', 'group_concat(DISTINCT v COLLATE NOCASE)',
        'group_concat(DISTINCT v COLLATE RTRIM)', 'group_concat(v COLLATE missing)',
        'group_concat(CASE WHEN id%2=0 THEN v END,s)', 'group_concat(hex(v),s)',
        'group_concat(v,NULL)', 'string_agg(v,7)', 'group_concat(v,abs(-9223372036854775808))',
        "group_concat(v,CASE WHEN id=1 THEN abs(-9223372036854775808) ELSE ',' END)",
        'group_concat(v,s COLLATE missing)', 'group_concat(DISTINCT v,s)', 'string_agg(DISTINCT v,s)',
        'group_concat()', 'group_concat(*)', 'string_agg(v)', 'group_concat(v,s,g)',
        'group_concat(missing)', 'group_concat(sum(v))', 'group_concat(DISTINCT v COLLATE missing)']
    queries=[]
    for table in ['t','tx','tn','e','n','z']:
        for aggregate in aggregates:
            queries.append(f'SELECT typeof({aggregate}),hex({aggregate}) FROM {table};')
            queries.append(f'SELECT g,hex({aggregate}) AS x FROM {table} GROUP BY g ORDER BY g;')
    for _ in range(count):
        table=rng.choice(['t','tx','tn','e','n','z']);aggregate=rng.choice(aggregates)
        result=rng.choice([f'hex({aggregate}) AS x', f'id,hex({aggregate}) AS x',
            f'min(id),hex({aggregate}) AS x', f'typeof({aggregate}),hex({aggregate}) AS x',
            f'hex({aggregate}) AS x,count(*)',f'hex({aggregate}) AS x,abs(-9223372036854775808)'])
        where=rng.choice(['',' WHERE 0',' WHERE id>3',' WHERE v IS NULL',' WHERE id=1'])
        group=rng.choice(['',' GROUP BY g',' GROUP BY id%3'])
        having=rng.choice(['',' HAVING count(*)>0',' HAVING x IS NOT NULL',' HAVING 0',' HAVING NULL'])
        order=rng.choice(['',' ORDER BY x',' ORDER BY min(id) DESC',' ORDER BY abs(-9223372036854775808)'])
        limit=rng.choice(['',' LIMIT 0',' LIMIT 1',' LIMIT 1 OFFSET 1',' LIMIT 2 OFFSET 20'])
        queries.append(f'SELECT {result} FROM {table}{where}{group}{having}{order}{limit};')
    queries += [
        "SELECT hex(group_concat(X'FF0080'));", "SELECT typeof(group_concat(NULL)),hex(group_concat(''));",
        "SELECT group_concat('x') WHERE 0;", "SELECT string_agg('x','|');",
        "SELECT group_concat(DISTINCT 'a' COLLATE NOCASE);", "SELECT group_concat(NULL,abs(-9223372036854775808));",
        "SELECT group_concat('x',abs(-9223372036854775808));", "SELECT group_concat(NULL,abs(-9223372036854775808)) LIMIT 0;",
        "SELECT group_concat(0 AND 0x10000000000000000);", "SELECT group_concat(0 AND missing) FROM e;",
        "SELECT group_concat(0 AND no_function(1)) FROM e;", "SELECT group_concat(v,s) FROM t ORDER BY 1 LIMIT 1 OFFSET 1;",
        "SELECT group_concat(v,s) AS x FROM t HAVING x IS NOT NULL;", "SELECT count(*) FROM t ORDER BY group_concat(v,s);",
        "SELECT hex(group_concat(v,s)) FROM t UNION SELECT hex(group_concat(v,s)) FROM tx ORDER BY 1;",
        "SELECT g,hex(group_concat(v,s)) AS x FROM t GROUP BY g ORDER BY x DESC LIMIT 2;",
        "SELECT 'group_concat'(v,s) FROM t;", 'SELECT "string_agg"(v,s) FROM t;',
    ]
    return setup,queries

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353850)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-string-aggregate-') as tmp:
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
