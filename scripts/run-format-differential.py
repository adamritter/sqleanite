#!/usr/bin/env python3
"""Compare the pinned SQLite format()/printf() behavior in both live file modes.

Read queries compare exact CLI bytes and positive error status, preserving
main/WAL bytes. A separate bulk write compares storage classes, binary64 bits
and raw bytes using Python SQLite only as an independent file observer, and
requires integrity_check. This is bounded numerical evidence, not a proof of
full printf equivalence or coverage of every length boundary.
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
def literal(text):
    return "'"+text.replace("'","''")+"'"


def expressions(seed,count):
    rng=random.Random(seed)
    values=['NULL',"''","'abc'","'a''b\\c'","'árvíz'","X'FF80C280'",
        "CAST(X'410042' AS TEXT)",'0','-1','12.75','1e-30','1e999',
        '9223372036854775807','-9223372036854775808']
    types='diuxXoprfegGsqQwc'
    flags=['','+','-','0','#','!',',']
    cases=['format()','printf()',"format(NULL,1)","format('')","printf('')","format(123,1)",
        "format(X'2564002573',42,'tail')"]
    for typ in types:
        for flag in flags:
            for value in values:
                cases.append(f'format({literal("[%"+flag+"12.4"+typ+"]")},{value})')
    for fmt in ['%','abc%','%n','%n%d','%s','%z','%%','%.0s','%.0c','%Y','x%Ytail','%T','%S','%j','%J',
        '%+ d','% +d','%-05d','%#x','%#o','%p','%2$d','%lllX','%hf','%01d','%2147483648d','%.2147483648f',
        '%*.*f','%*s','%.*s','%*.*c','%.*q','%!*.*Q','%0-10.5d','%#.0f','%#+.0f','%!.17g','%!.20g','%!.26g']:
        for args in ['',',NULL',",'abc'",',-3,2,12.75',',-2147483648,-2147483648,1',",10,2,'árvíz'",",5,3,X'FF8080C080'"]:
            cases.append(f'printf({literal(fmt)}{args})')
    for raw in ["X'80'","X'C08080'","X'C280808080'","X'F09F9880'","X'0027'","X'010A1B5C27'"]:
        for fmt in ['%c','%5.3c','%-5.3c','%!.1s','%!8.2s','%#q','%#Q','%#w','%.1q','%!.1q']:
            cases.append(f'format({literal(fmt)},{raw})')
    for _ in range(count):
        typ=rng.choice('diuxXoprfegGEQqwscz')
        flag=''.join(rng.sample('+- #!0,',rng.randrange(5)))
        width=rng.choice(['',str(rng.randrange(0,55)),'*'])
        precision=rng.choice(['','.'+str(rng.randrange(0,35)),'.*'])
        fmt='pre%'+flag+width+precision+rng.choice(['','l','ll'])+typ+'|%n|%s|%d'
        args=[]
        if width=='*':args.append(str(rng.randrange(-55,55)))
        if precision=='.*':args.append(str(rng.randrange(-35,35)))
        args += [repr(rng.uniform(-4,4) if rng.randrange(2) else rng.uniform(-1,1)*10**rng.randrange(-320,309)) if rng.randrange(2) else rng.choice(values),"'tail'",str(rng.randrange(-1000,1000))]
        cases.append(f'{rng.choice(["format","printf"])}({literal(fmt)},'+','.join(args)+')')
    for value in ['2.5','9.95','9.9995','49.47','-0.00001','1.7976931348623157e308','5e-324','0.1','-0.0','1e-4','1e-5']:
        for fmt in ['%.0f','%#.4f','%.1e','%.2g','%!.17g','%!.20g','%!.26e','%,025.5f']:
            cases.append(f'format({literal(fmt)},{value})')
    for _ in range(count//3):
        # Arbitrary grammar fragments, with bounded decimal width tokens.
        fragments=['#','!','+',' ','-','0',',','*','.', 'l','ll',rng.choice(list('dsf%QnY'))]
        fmt='head%'+''.join(rng.choice(fragments) for _ in range(rng.randrange(1,14)))+'tail%d'
        cases.append(f'format({literal(fmt)},-5,3,1.25,7)')
    return cases


def corpus(seed,count):
    setup="CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE TABLE e(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,12.75);INSERT INTO t VALUES(2,'árvíz');"
    queries=[f'SELECT typeof({e}),hex({e});' for e in expressions(seed,count)]
    queries += ["SELECT format('%s',v),printf('%g',v) FROM t ORDER BY id;",
        "SELECT format('%s',missing) FROM e LIMIT 0;","SELECT format('%s',abs(-9223372036854775808)) LIMIT 0;",
        "SELECT coalesce(7,format('%s',abs(-9223372036854775808)));",
        "SELECT format('%s',abs(-9223372036854775808));","SELECT format('%2000000000s','a');",
        "SELECT format('%.2000000000d',1);","SELECT format('%!.2000000000s','a');",
        "SELECT format('%2000000000c','a');","SELECT format('%*s',-2000000000,'a');",
        "SELECT format('%2000000000f',1);","SELECT format(DISTINCT '%s',1);",
        "SELECT format() FILTER(WHERE 1);","SELECT 'format'('%s',12);",
        "SELECT format('%s',sum(v)) FROM t;"]
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
    p.add_argument('--seed',type=int,default=353910)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-format-') as tmp:
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
            assert before==snapshot(),'format read changed input bytes'
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
