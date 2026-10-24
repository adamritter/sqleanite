#!/usr/bin/env python3
"""Compare ordinary aggregate FILTER clauses in the production Core paths.

Reads compare exact CLI bytes or matching positive errors, preserving main/WAL
bytes. Hex projections observe full string bytes. Error wording/codes are not
compared. Grouped and ungrouped retained MIN/MAX rows are tested separately.
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
    values=['NULL','1','1.0','2','-3',"'4'","'A'","'a'","'a '","X'31'"]
    setup=''
    for table,affinity in [('t',''),('tx','TEXT'),('tn','NUMERIC')]:
        setup+=f'CREATE TABLE {table}(id INTEGER PRIMARY KEY,g,v {affinity},s);'
        for i,v in enumerate(values+rng.choices(values,k=8),1):setup+=f"INSERT INTO {table} VALUES({i},{i%3},{v},'s{i}');"
    setup+='CREATE TABLE e(id INTEGER PRIMARY KEY,g,v,s);'
    setup+="CREATE TABLE n(id INTEGER PRIMARY KEY,g,v,s);INSERT INTO n VALUES(1,0,NULL,'first'),(2,0,NULL,'last');"
    setup+="CREATE TABLE o(id INTEGER PRIMARY KEY,g,v,s);INSERT INTO o VALUES(1,0,9223372036854775807,'a'),(2,0,1,'b');"
    functions=['count(*)','count(v)','count(DISTINCT v)','sum(v)','avg(v)','total(v)','min(v)','max(v)',
        'min(DISTINCT v)','max(DISTINCT v COLLATE NOCASE)','group_concat(v,s)',
        'group_concat(DISTINCT v COLLATE NOCASE)','string_agg(v,s)','sum(abs(-9223372036854775808))',
        'group_concat(v,abs(-9223372036854775808))','sum(sum(v))','group_concat(v,s,g)',
        'abs(v)','min(v,id)']
    filters=['1','0','NULL','id>2','v IS NULL','v>1',"v COLLATE NOCASE='a'",'g=0','id%2=0',
        'likely(v)','0 AND missing','0 AND no_function(1)','missing','count(*)>0',
        'abs(-9223372036854775808)',"'a' COLLATE missing",'id>2 AND abs(-9223372036854775808)']
    queries=[]
    for table in ['t','tx','tn','e','n','o']:
        for function in functions:
            for predicate in ['1','0','id>2']:
                expression=f'{function} FILTER (WHERE {predicate})'
                queries.append(f'SELECT id,typeof({expression}),hex({expression}) FROM {table};')
                queries.append(f'SELECT g,id,hex({expression}) FROM {table} GROUP BY g ORDER BY g;')
    for _ in range(count):
        table=rng.choice(['t','tx','tn','e','n','o']);function=rng.choice(functions);predicate=rng.choice(filters)
        expression=f'{function} FILTER (WHERE {predicate})'
        result=rng.choice([f'hex({expression}) AS x',f'id,hex({expression}) AS x',
            f'min(v),id,hex({expression}) AS x',f'hex({expression}) AS x,id,max(v)',
            f'hex({expression}) AS x,id,max(v) FILTER(WHERE id%2=0)',
            f'hex({expression}) AS x,abs(-9223372036854775808)'])
        where=rng.choice(['',' WHERE 0',' WHERE id>1'])
        group=rng.choice(['',' GROUP BY g',' GROUP BY v COLLATE NOCASE'])
        having=rng.choice(['',' HAVING x IS NOT NULL',' HAVING 0',' HAVING count(*) FILTER(WHERE id>2)>0'])
        order=rng.choice(['',' ORDER BY x',' ORDER BY min(v) FILTER(WHERE id>1) DESC'])
        limit=rng.choice(['',' LIMIT 0',' LIMIT 1',' LIMIT 1 OFFSET 1'])
        queries.append(f'SELECT {result} FROM {table}{where}{group}{having}{order}{limit};')
    queries += [
        'SELECT count(*) FILTER(WHERE 0),sum(abs(-9223372036854775808)) FILTER(WHERE 0);',
        'SELECT count(*) FILTER(WHERE 1) WHERE 0;',
        'SELECT id,min(v),max(v) FILTER(WHERE 0) FROM t;',
        'SELECT id,min(v),max(v) FILTER(WHERE 0) FROM t GROUP BY 1+0;',
        'SELECT id,min(v) FILTER(WHERE id>2),min(v) FILTER(WHERE id>3) FROM t;',
        'SELECT id,min(v) FILTER(WHERE id>2),max(v),min(v) FILTER(WHERE id>2) FROM t;',
        'SELECT id,min(DISTINCT v) FILTER(WHERE id>2),max(v) FILTER(WHERE 0) FROM t;',
        "SELECT count(*) FILTER(WHERE 'a' COLLATE missing)=0 FROM t;",
        "SELECT group_concat(v) FILTER(WHERE 'a' COLLATE missing)='A' FROM t;",
        "SELECT min(v COLLATE NOCASE) FILTER(WHERE id>0)='A' FROM t;",
        'SELECT v AS x,count(*) FILTER(WHERE x>1) FROM t;',
        'SELECT count(*) FILTER(WHERE 0 AND missing) FROM t;',
        'SELECT count(*) FILTER(WHERE 0 AND no_function(1)) FROM t LIMIT 0;',
        'SELECT count(*) FROM t ORDER BY sum(abs(-9223372036854775808)) FILTER(WHERE 0);',
        'SELECT abs(-9223372036854775808)+count(*) FILTER(WHERE 0) FROM t LIMIT 1 OFFSET 1;',
        'SELECT count(*) FILTER(WHERE 0 AND 0x10000000000000000) FROM t;',
        'SELECT count(*) FILTER(WHERE likely(NULL AND abs(-9223372036854775808))) FROM t;',
        "SELECT __sqlean_aggregate_filter(count(*),1) FROM t;",
        "SELECT '__sqlean_aggregate_filter'(count(*),1) FROM t;",
        'SELECT sum(v) FILTER(WHERE id>2) FILTER(WHERE 1) FROM t;',
        'SELECT sum(v) FILTER(WHERE id>2) AS x FROM t HAVING x IS NOT NULL;',
        'SELECT count(*) FILTER(WHERE 1) UNION SELECT count(*) FILTER(WHERE 0) ORDER BY 1;',
    ]
    for predicate in ['NULL AND abs(-9223372036854775808)',
            'likely(NULL AND abs(-9223372036854775808))',
            '(NULL AND abs(-9223372036854775808)) COLLATE binary',
            'likely(0 AND abs(-9223372036854775808))']:
        queries += [f'SELECT count(*) FILTER(WHERE {predicate}) FROM t;',
            f'SELECT count(*) FROM t HAVING {predicate};',
            f'SELECT count(*) FROM t GROUP BY g HAVING {predicate};',
            f'SELECT count(*) FROM t WHERE {predicate};']
    return setup,queries

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353880)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-aggregate-filter-') as tmp:
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
