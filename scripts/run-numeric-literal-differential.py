#!/usr/bin/env python3
"""Compare decimal/hex numeric literals, separators, identity and signed boundaries.

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
    values = ['0x0','0X1','0xff','0x7fffffff','0x80000000','0x7fffffffffffffff','0x8000000000000000','0xffffffffffffffff','0x0000000000000000000001','0x00000000000000000000ffffffffffffffff',
              '1_000','1_0.0_5','1_0e+0_1','.1_2','1_2.','0xA_B','0xF_FFF_FFFF_FFFF_FFFF','0x0_0_1','2147483648','02147483648','9223372036854775808','09223372036854775808']
    values += [hex(rng.randrange(2**64)) for _ in range(count)]
    values += ['_'.join(str(rng.randrange(10**9))) for _ in range(count)]
    queries = []
    for value in values:
        for expr in [value,'-'+value,'~'+value,f'{value}+1',f'{value}=CAST({value} AS INTEGER)']:
            queries.append(f'SELECT {expr},typeof({expr});')
    for value in ['1','1_0','0x1','0xFFFFFFFFFFFFFFFF','0x8000000000000000','9_223_372_036_854_775_807']:
        queries += [f'SELECT v FROM t LIMIT {value};',f'SELECT v FROM t LIMIT 1 OFFSET {value};',f'SELECT 1 UNION ALL SELECT 2 ORDER BY {value};']
    for left,right in [('2147483648','02147483648'),('214748364_8','2147483648'),('0x80000000','2147483648'),('0xabcdef01','0xABCDEF01'),('1_0.0','10.0'),('1e1_0','1e10'),('0xF_FFFFFFF','0xFFFFFFFF'),('9223372036854775808','09223372036854775808')]:
        queries += [f'SELECT {left} UNION ALL SELECT 2 ORDER BY {right};',f'SELECT abs({left}) UNION ALL SELECT 2 ORDER BY abs({right});']
    malformed = ['0x','0xg','0x1g','0x10000000000000000','0x1_0000000000000000','0x_1','0x1_','0x1__2','1__0','1_','1_.0','1._0','1e_2','1e+_2','1e2_','1e2__3','1e','1e+','1.2foo','12abc','0x1z','0x1$z']
    queries += [f'SELECT {bad};' for bad in malformed]
    queries += ["SELECT 0 AND 0x10000000000000000;", "SELECT 0x10000000000000000 AND 0;", "SELECT 0x10000000000000000 WHERE 0;", "SELECT 0x10000000000000000 LIMIT 0;", "SELECT 1 LIMIT 0 OFFSET 0x10000000000000000;", "SELECT -(9223372036854775808),typeof(-(9223372036854775808));", "SELECT -(+9223372036854775808),typeof(-(+9223372036854775808));", "SELECT -9223372036854775808 UNION SELECT 2 ORDER BY -(9223372036854775808);", "SELECT -9223372036854775808 UNION SELECT 2 ORDER BY -09223372036854775808;", "SELECT -(+0x8000000000000000);", "SELECT -(0x8000000000000000 COLLATE BINARY);", "SELECT CASE WHEN 0 THEN -0x8000000000000000 ELSE 1 END;", "SELECT -0x8000000000000000 LIMIT 0;", "SELECT 0 AND -0x8000000000000000;", "SELECT CAST('0xffff' AS INTEGER),CAST('1_000' AS INTEGER);", "SELECT '0xffff'+0,'1_000'+0;", "SELECT 0xFFFFFFFFFFFFFFFF UNION SELECT -1 ORDER BY 1;", "SELECT v+0xFFFFFFFFFFFFFFFF FROM t ORDER BY id;"]
    setup = 'CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,1),(2,2),(3,NULL);'
    return setup,queries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353780)
    p.add_argument('--random-cases',type=int,default=100)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); setup,queries=corpus(args.seed,args.random_cases)
    failures=[];phases=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-numeric-literal-') as tmp:
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
            writes = [
                "INSERT INTO t VALUES(4,0xFFFFFFFFFFFFFFFF),(5,1_000.0);",
                "UPDATE t SET v=v+0x8000000000000000 WHERE id=4;",
                "INSERT INTO t VALUES(6,-0x8000000000000000);",
                "DELETE FROM t WHERE v=0x0000000000000001;",
            ]
            for sql in writes:
                l,r=run(sql)
                same = l.returncode == r.returncode == 0 or l.returncode > 0 and r.returncode > 0
                if not same:
                    failures.append(dict(mode=mode,sql=sql,lean=dict(code=l.returncode,stderr=l.stderr.decode('latin1')),sqlite=dict(code=r.returncode,stderr=r.stderr.decode('latin1'))))
                l,r=run('SELECT id,typeof(v),quote(v) FROM t ORDER BY id;')
                assert l.returncode==r.returncode==0 and l.stdout==r.stdout,(sql,l.stderr,r.stderr,l.stdout,r.stdout)
                integrity=subprocess.run([args.sqlite,'-batch',str(folder/'lean.db'),'PRAGMA integrity_check;'],capture_output=True,timeout=120)
                assert integrity.returncode==0 and integrity.stdout==b'ok\n',(sql,integrity.stdout,integrity.stderr)
            phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors,writes=len(writes)))
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,random_cases=args.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
