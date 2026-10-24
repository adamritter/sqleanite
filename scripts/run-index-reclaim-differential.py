#!/usr/bin/env python3
"""Check indexed shrink/refill files with SQLite as the independent reader.

Both rollback-journal and WAL production writers run fresh seeded fixtures.
Every phase requires integrity_check=ok and identical SQLite-decoded rows;
no orphan-page exception is allowed.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import subprocess
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353470)
    p.add_argument('--fixtures',type=int,default=6)
    p.add_argument('--cycles',type=int,default=3)
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed)
    checks=[];failures=[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-reclaim-') as tmp:
        root=pathlib.Path(tmp)
        for fixture in range(args.fixtures):
            n=[200,127,501,1000,65,300][fixture%6]+rng.randrange(0,23)
            payloads=[f"key-{rng.randrange(0,40):02d}-"+('x'*rng.randrange(0,60)) for _ in range(n)]
            for mode in ['--verified-file','--verified-wal-file']:
                d=root/f'{fixture}-{mode}';d.mkdir()
                lean,reference=d/'lean.db',d/'sqlite.db'
                def write(sql):
                    q=d/'query.sql';q.write_text(sql)
                    a=subprocess.run([str(args.lean),mode,str(lean),str(q)],text=True,capture_output=True,timeout=180)
                    b=subprocess.run([args.sqlite,'-batch','-bail',str(reference)],input=sql,text=True,capture_output=True,timeout=180)
                    assert a.returncode==b.returncode==0,(fixture,mode,sql[:160],a.stderr,b.stderr)
                def read(db,sql):
                    return subprocess.check_output([args.sqlite,'-readonly','-batch','-bail',str(db),sql],text=True,timeout=180)
                def check(phase):
                    integrity=read(lean,'PRAGMA integrity_check;').strip()
                    oracle_integrity=read(reference,'PRAGMA integrity_check;').strip()
                    assert oracle_integrity=='ok'
                    query="SELECT type,name,tbl_name FROM sqlite_schema ORDER BY type,name; SELECT id,typeof(v),hex(v),tag FROM t ORDER BY id; SELECT * FROM sentinel ORDER BY id; SELECT id FROM t WHERE v='key-00-' ORDER BY id;"
                    a,b=read(lean,query),read(reference,query)
                    item=dict(fixture=fixture,mode=mode,phase=phase,rows=n,integrity=integrity,contents_match=a==b,
                        page_count=int(read(lean,'PRAGMA page_count;')),free_pages=int(read(lean,'PRAGMA freelist_count;')))
                    checks.append(item)
                    if integrity!='ok' or a!=b: failures.append(item)
                setup=['CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,tag TEXT);',
                       'CREATE TABLE sentinel(id INTEGER PRIMARY KEY,v TEXT);','BEGIN;']
                setup += [f"INSERT INTO t VALUES({i+1},'{v}','tag-{i%7}');" for i,v in enumerate(payloads)]
                setup += [f"INSERT INTO sentinel VALUES({i},'unchanged-{i}');" for i in range(50)]
                setup += ['COMMIT;','CREATE INDEX tv ON t(v);']
                write('\n'.join(setup));check('initial')
                for cycle in range(args.cycles):
                    cut=0 if cycle==0 else rng.randrange(n//4,n)
                    write(f'DELETE FROM t WHERE id>{cut};');check(f'delete-{cycle}')
                    refill=['BEGIN;']+[f"INSERT INTO t VALUES({i+1},'{payloads[i]}','tag-{i%7}');" for i in range(cut,n)]+['COMMIT;']
                    write('\n'.join(refill));check(f'refill-{cycle}')
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,fixtures=args.fixtures,cycles=args.cycles,checks=checks,failures=failures,
        implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),
        comparison='SQLite independently reads rollback/WAL images, schema, typed values, index lookup, unchanged neighbour table and integrity after every phase.')
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__':
    raise SystemExit(main())
