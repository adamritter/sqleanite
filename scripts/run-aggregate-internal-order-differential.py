#!/usr/bin/env python3
"""Compare aggregate-internal ORDER BY in both production file modes.

Successful reads compare exact CLI bytes, with hex projections for string bytes.
Errors compare positive status, not exact codes/messages. Input main/WAL bytes
must remain unchanged. DISTINCT representative replacement and MIN/MAX's ignored
ordering are included; this does not measure query-planner performance.
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
    values=['NULL','1','1.0','-2','1e100','-1e100',"'A'","'a'","'a '","X'31'","CAST(X'410078' AS TEXT)","CAST(X'610079' AS TEXT)","CAST(X'FF80' AS TEXT)"]
    setup=''
    for table,affinity in [('t',''),('tx','TEXT'),('tn','NUMERIC')]:
        setup+=f'CREATE TABLE {table}(id INTEGER PRIMARY KEY,g,v {affinity},s);'
        for i,v in enumerate(values+rng.choices(values,k=8),1):setup+=f"INSERT INTO {table} VALUES({i},{i%3},{v},'s{i}');"
    setup+='CREATE TABLE e(id INTEGER PRIMARY KEY,g,v,s);'
    setup+="CREATE TABLE o(id INTEGER PRIMARY KEY,g,v,s);INSERT INTO o VALUES(1,0,9223372036854775807,'a'),(2,0,1,'b'),(3,0,-1,'c');"
    functions=['count(v{})','sum(v{})','avg(v{})','total(v{})','min(v{})','max(v{})',
        'min(DISTINCT v{})','max(DISTINCT v COLLATE NOCASE{})','group_concat(v{})',
        'group_concat(v,s{})','string_agg(v,s{})','group_concat(DISTINCT v{})',
        'group_concat(DISTINCT v COLLATE NOCASE{})','group_concat(DISTINCT v COLLATE RTRIM{})',
        'sum(DISTINCT v{})','abs(v{})','min(v,id{})']
    orders=['id','id DESC','v','v DESC','v COLLATE NOCASE','v COLLATE RTRIM DESC NULLS LAST',
        'v NULLS LAST,id DESC','1','0','999','-1','id%3 DESC,id',
        'v+0','g,id DESC','abs(-9223372036854775808)','missing','sum(id)',
        'id COLLATE missing',"v='a' COLLATE missing",'no_function(id)']
    queries=[]
    for table in ['t','tx','tn','e','o']:
        for function in functions:
            for ordering in ['id DESC','v','v COLLATE NOCASE']:
                aggregate=function.format(' ORDER BY '+ordering)
                queries.append(f'SELECT id,typeof({aggregate}),hex({aggregate}) FROM {table};')
                queries.append(f'SELECT g,id,hex({aggregate}) FROM {table} GROUP BY g ORDER BY g;')
    for _ in range(count):
        table=rng.choice(['t','tx','tn','e','o']);function=rng.choice(functions);ordering=rng.choice(orders)
        aggregate=function.format(' ORDER BY '+ordering)
        filter_=rng.choice(['',' FILTER(WHERE id>2)',' FILTER(WHERE 0)',' FILTER(WHERE v IS NULL)'])
        aggregate+=filter_
        result=rng.choice([f'hex({aggregate}) AS x',f'id,hex({aggregate}) AS x',
            f'min(v),id,hex({aggregate}) AS x',f'hex({aggregate}) AS x,id,max(v)',
            f'hex({aggregate}) AS x,abs(-9223372036854775808)'])
        where=rng.choice(['',' WHERE 0',' WHERE id>1'])
        group=rng.choice(['',' GROUP BY g',' GROUP BY v COLLATE NOCASE'])
        having=rng.choice(['',' HAVING x IS NOT NULL',' HAVING 0'])
        tail=rng.choice(['',' ORDER BY x',' LIMIT 0',' LIMIT 1',' LIMIT 1 OFFSET 1'])
        queries.append(f'SELECT {result} FROM {table}{where}{group}{having}{tail};')
    queries += [
        'SELECT count(ORDER BY missing) FROM t;', 'SELECT count(ORDER BY no_function(1)) FROM t;',
        'SELECT count(DISTINCT ORDER BY missing) FROM t;', 'SELECT sum(ORDER BY id) FROM t;',
        'SELECT count(ORDER BY id),count(ALL ORDER BY missing) FROM t;',
        'SELECT count(* ORDER BY id) FROM t;', 'SELECT count(v ORDER BY abs(-9223372036854775808)) FROM t;',
        'SELECT min(v ORDER BY abs(-9223372036854775808)) FROM t;',
        'SELECT min(v ORDER BY id COLLATE missing) FROM t;',
        "SELECT min(v ORDER BY v='a' COLLATE missing) FROM t;",
        'SELECT min(v ORDER BY missing) FROM t LIMIT 0;',
        'SELECT min(v ORDER BY no_function(id)) FROM t LIMIT 0;',
        'SELECT sum(v ORDER BY id DESC),sum(v ORDER BY id ASC) FROM o LIMIT 0;',
        'SELECT sum(v ORDER BY id DESC) FROM o;',
        'SELECT sum(v ORDER BY id) FILTER(WHERE id>1) FROM o;',
        'SELECT sum(v ORDER BY abs(-9223372036854775808)) FILTER(WHERE 0) FROM t;',
        'SELECT group_concat(DISTINCT v ORDER BY v),group_concat(DISTINCT v ORDER BY id) FROM t;',
        'SELECT group_concat(DISTINCT v COLLATE NOCASE ORDER BY v COLLATE NOCASE) FROM t;',
        'SELECT group_concat(DISTINCT v COLLATE NOCASE ORDER BY v COLLATE binary) FROM t;',
        'SELECT id,min(v ORDER BY id),max(v),min(v ORDER BY id DESC) FROM t;',
        'SELECT count(*) FROM t ORDER BY group_concat(v ORDER BY id DESC);',
        'SELECT group_concat(v ORDER BY id DESC) AS x FROM t HAVING x IS NOT NULL;',
        "SELECT __sqlean_aggregate_order(group_concat(v),id) FROM t;",
        "SELECT '__sqlean_aggregate_order'(group_concat(v),id) FROM t;",
        'SELECT group_concat(v ORDER BY __sqlean_order_desc(id)) FROM t;',
        'SELECT group_concat(v ORDER BY 1) FROM t UNION SELECT group_concat(v ORDER BY 1) FROM tx ORDER BY 1;',
    ]
    for expression in ["v='a' COLLATE missing",'min(v COLLATE missing,v)',"v MATCH 'x'",'json(v)','sqrt(v)',
            'abs()','json(v,v)','min(v)','max(v)','min(v,id)','count(*)','no_function(id)',
            'likelihood(v,0)','likelihood(v,0.5)','0x10000000000000000','-0x8000000000000000',
            'likelihood(v,0x00000000000000000)','likelihood(v,0x00000000000000001)']:
        queries.append(f'SELECT min(v ORDER BY {expression}) FROM t;')
        queries.append(f'SELECT max(v ORDER BY {expression}) FROM e LIMIT 0;')
    for left in ['id','id DESC','v COLLATE NOCASE']:
        for right in ['id','id ASC NULLS FIRST','id ASC NULLS LAST','id DESC','id DESC NULLS LAST','v COLLATE NOCASE']:
            queries.append(f'SELECT id,min(v ORDER BY {left}),max(v),min(v ORDER BY {right}) FROM t;')
            queries.append(f'SELECT g,id,min(v ORDER BY {left}),max(v),min(v ORDER BY {right}) FROM t GROUP BY g ORDER BY g;')
    for ordering in ['v NULLS FIRST','v NULLS LAST','v DESC NULLS FIRST','v DESC NULLS LAST',
            'v COLLATE NOCASE NULLS LAST,id DESC']:
        queries.append(f'SELECT group_concat(id ORDER BY {ordering}) FROM t;')
    for size in [1001,2000,2001]:
        keys=','.join(['1']*size)
        queries.append(f'SELECT min(v ORDER BY {keys}) FROM e LIMIT 0;')
    return setup,queries

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353890)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-aggregate-internal-order-') as tmp:
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
