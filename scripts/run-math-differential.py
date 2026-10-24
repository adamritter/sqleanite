#!/usr/bin/env python3
"""Compare the pinned SQLite math-function behavior in both live file modes.

Read queries compare exact CLI bytes and positive error status, preserving
main/WAL bytes. A separate bulk write compares storage classes, binary64 bits
and raw bytes using Python SQLite only as an independent file observer, and
requires integrity_check. This is bounded numerical evidence, not a proof of
transcendental equivalence on every platform or every binary64 input.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import random
import sqlite3
import struct
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
UNARY=['ceil','ceiling','floor','trunc','acos','acosh','asin','asinh','atan','atanh',
    'cos','cosh','sin','sinh','tan','tanh','exp','ln','log','log2','log10','sqrt','radians','degrees']
BINARY=['pow','power','mod','atan2','log']


def expressions(seed,count):
    rng=random.Random(seed)
    values=['NULL','0','-0.0','0.0','1','1.0','-1','0.5','-0.5','1.5','-1.5','2','10',
        '1e999','-1e999','1e-999','1e-300','-1e-300','5e-324','-5e-324','1e300',
        '9223372036854775807','-9223372036854775808',"'1'","'1.0'","'1e0'","' 12 '",
        "'12x'","'NaN'","'Inf'","''","X'31'","X'312E35'","CAST(X'31320078' AS TEXT)",
        "CAST(X'312E300078' AS TEXT)","CAST(X'343530333539393632373337303439360078' AS TEXT)",
        "'9223372036854775808'","'-9223372036854775808'","'1.0e999'","'-0.0'"]
    cases=['pi()']+[f'{fn}({v})' for fn in UNARY for v in values]
    for fn in BINARY:
        for a in values:
            for b in ['NULL','-0.0','0.5','1','2','-2','1e999',"'3tail'","X'3332'"]:
                cases.append(f'{fn}({a},{b})')
    for _ in range(count):
        if rng.randrange(2):
            fn=rng.choice(UNARY)
            v=repr(rng.uniform(-4,4) if rng.randrange(2) else rng.uniform(-1,1)*10**rng.randrange(-300,301))
            if rng.randrange(4)==0:v="'"+v+"'"
            cases.append(f'{fn}({v})')
        else:
            fn=rng.choice(BINARY)
            a=repr(rng.uniform(-4,4) if rng.randrange(2) else rng.uniform(-1,1)*10**rng.randrange(-300,301))
            b=repr(rng.uniform(-4,4) if rng.randrange(2) else rng.uniform(-1,1)*10**rng.randrange(-300,301))
            cases.append(f'{fn}({a},{b})')
    def finite():
        while True:
            value=struct.unpack('>d',rng.getrandbits(64).to_bytes(8,'big'))[0]
            if math.isfinite(value):return repr(value)
    for _ in range(count):
        cases.append(f'mod({finite()},{finite()})')
        cases.append(f'{rng.choice(["ceil","floor","trunc"])}({finite()})')
    return cases


def corpus(seed,count):
    values=['NULL','0','1','1.0','-2','1.25',"'1'","'bad'","X'31'"]
    setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE TABLE e(id INTEGER PRIMARY KEY,v);'
    for i,v in enumerate(values,1):setup+=f'INSERT INTO t VALUES({i},{v});'
    queries=[f'SELECT typeof({e}),quote({e});' for e in expressions(seed,count)]
    for fn in UNARY:
        queries += [f'SELECT id,typeof({fn}(v)),quote({fn}(v)) FROM t ORDER BY id;',
            f'SELECT sum({fn}(v)) FROM t;',f'SELECT {fn}(missing) FROM e LIMIT 0;',
            f'SELECT {fn}() FROM e LIMIT 0;']
    queries += ['SELECT pi(1);','SELECT log();','SELECT log(1,2,3);','SELECT pow(1);','SELECT mod(1,2,3);',
        'SELECT sqrt(abs(-9223372036854775808)) LIMIT 0;',
        'SELECT coalesce(7,sqrt(abs(-9223372036854775808)));',
        'SELECT sqrt(abs(-9223372036854775808));','SELECT pi() FILTER(WHERE 1);',
        'SELECT sqrt(DISTINCT 4);',"SELECT 'sin'(0);",'SELECT ceil(v) AS x,count(*) FROM t GROUP BY x ORDER BY x;']
    return setup,queries


def observe(path):
    connection=sqlite3.connect('file:'+str(path)+'?mode=ro',uri=True)
    try:
        connection.text_factory=bytes
        integrity=connection.execute('PRAGMA integrity_check').fetchall()
        rows=[]
        for identifier,kind,value in connection.execute('SELECT id,typeof(v),v FROM m ORDER BY id'):
            kind=kind.decode()
            stored=struct.pack('>d',value).hex() if kind=='real' else value.hex() if isinstance(value,bytes) else value
            rows.append([identifier,kind,stored])
        return rows,[r[0].decode() for r in integrity]
    finally:connection.close()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353900)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-math-') as tmp:
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
            assert before==snapshot(),'math read changed input bytes'
            cases=expressions(args.seed,args.random_cases)
            bulk='CREATE TABLE m(id INTEGER PRIMARY KEY,v);BEGIN;'+''.join(f'INSERT INTO m VALUES({i},{e});' for i,e in enumerate(cases,1))+'COMMIT;'
            l,r=run(bulk)
            writes_checked=0
            if l.returncode!=0 or r.returncode!=0:
                failures.append(dict(mode=mode,kind='bulk-write',lean=dict(code=l.returncode,stderr=l.stderr.decode('latin1')),sqlite=dict(code=r.returncode,stderr=r.stderr.decode('latin1'))))
            else:
                lean,lean_integrity=observe(folder/'lean.db');reference,ref_integrity=observe(folder/'sqlite.db')
                if lean_integrity!=['ok'] or ref_integrity!=['ok']:
                    failures.append(dict(mode=mode,kind='integrity',lean=lean_integrity,sqlite=ref_integrity))
                assert len(lean)==len(reference)==len(cases)
                for index,(actual,expected) in enumerate(zip(lean,reference)):
                    if actual!=expected:failures.append(dict(mode=mode,kind='stored-value',expression=cases[index],lean=actual,sqlite=expected))
                writes_checked=len(cases)
            phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors,stored_values=writes_checked))
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip(),observer_sqlite_version=sqlite3.sqlite_version,write_transaction=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
