#!/usr/bin/env python3
"""Read frozen SQLite-created WAL snapshots through the production Lean CLI.

Copies main+WAL while the oracle connection remains open, so this really tests
uncheckpointed, partial-page WALs. Mutations cover both checksum byte orders,
page sizes, valid transaction prefixes, damaged frames and incomplete tails.
No live cross-engine WAL writer/SHM compatibility is claimed by these cases.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import select
import struct
import subprocess
import tempfile
import time

ROOT=pathlib.Path(__file__).resolve().parents[1]


def checksum(data, seed, endian):
    assert len(data)%8==0
    s1,s2=seed
    words=struct.unpack(endian+'I'*(len(data)//4),data)
    for a,b in zip(words[::2],words[1::2]):
        s1=(s1+a+s2)&0xffffffff
        s2=(s2+b+s1)&0xffffffff
    return s1,s2


def rewrite(wal, endian='>', version=None, uncommitted=False):
    out=bytearray(wal)
    struct.pack_into('>I',out,0,0x377f0683 if endian=='>' else 0x377f0682)
    if version is not None: struct.pack_into('>I',out,4,version)
    size=struct.unpack_from('>I',out,8)[0]
    sums=checksum(out[:24],(0,0),endian)
    struct.pack_into('>II',out,24,*sums)
    for offset in range(32,len(out),size+24):
        if uncommitted: struct.pack_into('>I',out,offset+4,0)
        sums=checksum(out[offset:offset+8]+out[offset+24:offset+24+size],sums,endian)
        struct.pack_into('>II',out,offset+16,*sums)
    return bytes(out)


def variants(wal):
    size=struct.unpack_from('>I',wal,8)[0];stride=size+24
    commits=[i+stride for i in range(32,len(wal),stride) if struct.unpack_from('>I',wal,i+4)[0]]
    assert len(commits)>=2
    first=commits[0]
    items=[('all-committed',wal),('empty',b''),('short-header',wal[:21]),('header-only',wal[:32]),
           ('partial-first-frame',wal[:32+stride//2]),('first-commit',wal[:first]),
           ('partial-after-commit',wal[:first+stride//2]),('incomplete-final-frame',wal[:-1]),
           ('trailing-garbage',wal+b'cut-off'),('all-uncommitted',rewrite(wal,'<' if wal[3]==0x82 else '>',uncommitted=True)),
           ('future-version',rewrite(wal,'<' if wal[3]==0x82 else '>',version=3007001))]
    for name,position in [('bad-header-checksum',24),('bad-first-checksum',48),
                          ('bad-later-checksum',first+16),('bad-later-salt',first+8)]:
        damaged=bytearray(wal);damaged[position]^=0x80;items.append((name,bytes(damaged)))
    damaged=bytearray(wal);damaged[first:first+4]=b'\0'*4;items.append(('zero-later-page',bytes(damaged)))
    return items


def snapshot(args,d,page_size,rng):
    db=d/'source.db'
    setup=[f'PRAGMA page_size={page_size};','PRAGMA journal_mode=WAL;','PRAGMA wal_autocheckpoint=0;',
        'CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);','CREATE TABLE untouched(id INTEGER PRIMARY KEY,v BLOB);','BEGIN;']
    for i in range(1,41):
        setup.append(f"INSERT INTO t VALUES({i},'{rng.randrange(1000000)}-'||hex(zeroblob({rng.randrange(20,100)}))); ")
    for i in range(1,5): setup.append(f'INSERT INTO untouched VALUES({i},zeroblob(9000));')
    setup+=['COMMIT;','PRAGMA wal_checkpoint(TRUNCATE);',
        "BEGIN; UPDATE t SET v='first-commit' WHERE id=2; DELETE FROM t WHERE id=3; COMMIT;",
        "BEGIN; UPDATE t SET v='second-commit' WHERE id=5; INSERT INTO t VALUES(41,'new'); COMMIT;"]
    proc=subprocess.Popen([args.sqlite,'-batch','-bail',str(db)],stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    try:
        proc.stdin.write(('\n'.join(setup)+'\n.print WAL_READY\n').encode());proc.stdin.flush()
        received=b'';deadline=time.monotonic()+15
        while b'WAL_READY\n' not in received:
            assert time.monotonic()<deadline and proc.poll() is None,('snapshot producer failed',received)
            if select.select([proc.stdout],[],[],1)[0]: received+=os.read(proc.stdout.fileno(),4096)
        main=db.read_bytes();wal=pathlib.Path(str(db)+'-wal').read_bytes()
        assert len(wal)>32 and len(main)>page_size
        return main,wal
    finally:
        proc.communicate(b'.quit\n',timeout=15)
        assert proc.returncode==0


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite')
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353510)
    p.add_argument('--fixtures',type=int,default=1)
    p.add_argument('--page-sizes',default='512,1024,4096,8192,65536')
    p.add_argument('--output',type=pathlib.Path)
    args=p.parse_args();rng=random.Random(args.seed)
    failures=[];cases=[]
    query='SELECT id,hex(v),typeof(v) FROM t ORDER BY id; SELECT id,length(v),hex(substr(v,1,8)) FROM untouched ORDER BY id;'
    with tempfile.TemporaryDirectory(prefix='sqleanite-wal-recovery-') as tmp:
        root=pathlib.Path(tmp)
        for page_size in map(int,args.page_sizes.split(',')):
            for fixture in range(args.fixtures):
                d=root/f'{page_size}-{fixture}';d.mkdir()
                main_bytes,original=snapshot(args,d,page_size,rng)
                for endian in ['<','>']:
                    wal=rewrite(original,endian)
                    for label,data in variants(wal):
                        case=d/(endian+label);case.mkdir();sql=case/'query.sql';sql.write_text(query)
                        for name in ['lean.db','sqlite.db']:
                            (case/name).write_bytes(main_bytes);(case/(name+'-wal')).write_bytes(data)
                        a=subprocess.run([str(args.lean),'--verified-wal-file',str(case/'lean.db'),str(sql)],text=True,capture_output=True,timeout=120)
                        b=subprocess.run([args.sqlite,'-batch','-bail','-readonly',str(case/'sqlite.db'),query],text=True,capture_output=True,timeout=120)
                        same=(a.returncode==0 and b.returncode==0 and a.stdout==b.stdout) or (a.returncode!=0 and b.returncode!=0)
                        case_info=dict(page_size=page_size,fixture=fixture,checksum_order=endian,variant=label,
                            main_bytes=len(main_bytes),wal_bytes=len(data),matches=same,matching_error=same and b.returncode!=0,
                            lean_output_sha256=hashlib.sha256(a.stdout.encode()).hexdigest(),
                            sqlite_output_sha256=hashlib.sha256(b.stdout.encode()).hexdigest())
                        if not same:
                            failures.append(dict(**case_info,lean_code=a.returncode,sqlite_code=b.returncode,
                                lean_error=a.stderr,sqlite_error=b.stderr,lean_output_prefix=a.stdout[:200],sqlite_output_prefix=b.stdout[:200]))
                        assert (case/'lean.db').read_bytes()==main_bytes and (case/'lean.db-wal').read_bytes()==data
                        cases.append(case_info)
    digest=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        digest.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,fixtures_per_page_size=args.fixtures,cases=len(cases),matching_cases=sum(x['matches'] for x in cases),
        matching_errors=sum(x['matching_error'] for x in cases),failures=failures,details=cases,
        implementation_sha256=digest.hexdigest(),executable_sha256=hashlib.sha256(args.lean.read_bytes()).hexdigest(),
        harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    if args.output: args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return bool(failures)


if __name__=='__main__': raise SystemExit(main())
