#!/usr/bin/env python3
"""Compare ungrouped HAVING, aliases, affinities and retained MIN/MAX rows.

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
    values = ['NULL','1','1.0','2','-3',"'4'","'x'","'A'","'a'","'a '","'A  '","X'31'"]
    setup = ''
    for table, affinity in [('t',''),('tx','TEXT'),('tn','NUMERIC')]:
        setup += f'CREATE TABLE {table}(id INTEGER PRIMARY KEY,v {affinity},w TEXT);'
        for i,v in enumerate(values+rng.choices(values,k=14),1):
            setup += f"INSERT INTO {table} VALUES({i},{v},'row{i}');"
    setup += "CREATE TABLE e(id INTEGER PRIMARY KEY,v,w TEXT);"
    setup += "CREATE TABLE n(id INTEGER PRIMARY KEY,v,w TEXT);INSERT INTO n VALUES(1,NULL,'first'),(2,NULL,'last');"
    setup += "CREATE TABLE o(id INTEGER PRIMARY KEY,v,w TEXT);INSERT INTO o VALUES(1,9223372036854775807,'first'),(2,1,'last');"
    setup += 'CREATE TABLE s(id INTEGER PRIMARY KEY,"0",x,"true");INSERT INTO s VALUES(1,7,0,9),(2,8,1,10);'
    results = ['count(*) AS x','sum(v) AS x','min(v) AS x','max(v) AS x','min(DISTINCT v) AS x',
        'min(v COLLATE NOCASE) AS x','max(DISTINCT v COLLATE RTRIM) AS x',
        'id,w,count(*) AS x','id,w,min(v) AS x','id,w,max(v) AS x',
        'id,w,min(v),max(v) AS x','id,w,min(v),max(v),min(v) AS x',
        'id,w,min(DISTINCT v),max(DISTINCT v) AS x',
        'id,w,min(v COLLATE NOCASE),max(v COLLATE RTRIM),min(v COLLATE NOCASE) AS x',
        'abs(-9223372036854775808)+count(*) AS x','coalesce(sum(v),0)+count(*) AS x',
        'typeof(v),typeof(min(v)),v,min(v) AS x','* , count(*) AS x']
    havings=['1','0','NULL','count(*)>0','x IS NOT NULL','x>2','x=1',"x='1'",'id=1','id>1',
        'v IS NULL','v=4',"v='4'",'v IN (1,4,NULL)',"v COLLATE NOCASE='a'",'min(v) IS NOT NULL',
        'max(v) IS NOT NULL','min(v)>0 AND id>1','sum(v)>0 OR count(*)=0',
        'count(*)>0 OR abs(-9223372036854775808)',
        'count(*)<0 AND abs(-9223372036854775808)',
        'NOT(count(*)>0 AND NULL)','0 AND no_function(1)','missing',
        '1 COLLATE missing','v=1 COLLATE missing','abs(-9223372036854775808)']
    orders=['',' ORDER BY 1',' ORDER BY x DESC',' ORDER BY min(v)',
        ' ORDER BY max(v),min(v)',' ORDER BY abs(-9223372036854775808)',
        ' ORDER BY sum(abs(-9223372036854775808))']
    windows=['',' LIMIT 0',' LIMIT 1',' LIMIT 1 OFFSET 1']
    queries=[]
    for table in ['t','tx','tn','e','n','o']:
        for result in results:
            for having in ['1','0','v IS NULL','x IS NOT NULL']:
                queries.append(f'SELECT {result} FROM {table} HAVING {having};')
    for _ in range(count):
        table=rng.choice(['t','tx','tn','e','n','o']);result=rng.choice(results)
        having=rng.choice(havings);order=rng.choice(orders);window=rng.choice(windows)
        where=rng.choice(['',' WHERE id>1',' WHERE 0',' WHERE id=2'])
        queries.append(f'SELECT {result} FROM {table}{where} HAVING {having}{order}{window};')
    queries += [
        'SELECT count(*) AS true FROM t HAVING true=26;',
        'SELECT sum(v) AS v FROM t HAVING v IS NULL;',
        'SELECT count(*) AS x FROM s HAVING x=0;',
        'SELECT count(*) AS true FROM s HAVING true=9;',
        'SELECT count(*) FROM s AS "__aggregate_result" HAVING "__aggregate_result"."0"=7;',
        'SELECT count(*) FROM s AS "__aggregate_source" HAVING "__aggregate_source"."0"=7;',
        'SELECT count(*) FROM t HAVING "__aggregate_result"."0"=0;',
        'SELECT min(v),max(v),min(t.v),id FROM t HAVING 1;',
        'SELECT min(v),max(v),min(T.V),id FROM t HAVING 1;',
        'SELECT min(v),max(v),MIN(v),id FROM t HAVING 1;',
        'SELECT count(*) FROM t HAVING count(*)>0 AND abs(-9223372036854775808) LIMIT 1 OFFSET 1;',
        'SELECT count(*) FROM t HAVING count(*)>0 OR abs(-9223372036854775808);',
        'SELECT count(*) FROM t HAVING count(*)<0 AND abs(-9223372036854775808);',
        'SELECT count(*) FROM t HAVING min(v)>0 ORDER BY max(v);',
        'SELECT count(*) FROM t HAVING 0 AND 0x10000000000000000;',
        'SELECT count(*) FROM t HAVING 0 AND no_function(1);',
        'SELECT count(*) FROM t HAVING sum(sum(v));',
        'SELECT 1 FROM t HAVING count(*)>0;',
        'SELECT count(*) HAVING count(*)=1;',
        'SELECT count(*) AS x WHERE 0 HAVING x=0;',
        'SELECT count(*) HAVING rowid IS NULL;',
        'SELECT count(*) HAVING count(*)>0 ORDER BY sum(abs(-9223372036854775808));',
        'SELECT count(*) HAVING 0 ORDER BY abs(-9223372036854775808);',
        'SELECT abs(-9223372036854775808)+count(*) HAVING 0;',
        'SELECT id,min(v),max(v) FROM t;',
        'SELECT *,count(*) FROM e;',
        'SELECT v,count(*) FROM t GROUP BY v HAVING count(*)>1 ORDER BY count(*) DESC;',
    ]
    return setup,queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353800)
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
            assert before==snapshot(),'HAVING read changed input bytes'
            phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors))
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
