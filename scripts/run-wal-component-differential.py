#!/usr/bin/env python3
"""Component-only WAL append/index comparison, not the live writer protocol.
Pinned SQLite creates the input and observes each Lean-produced appended log.
Native little-endian SHM bytes are compared exactly. Opposite WAL checksum
order and interrupted tails are explicit synthetic format fixtures.
"""
import argparse
import hashlib
import json
import os
import pathlib
import random
import shutil
import struct
import subprocess
import sys
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def checksum(data, seed=(0,0), big=False):
    words=struct.unpack(('>' if big else '<')+'I'*(len(data)//4),data)
    a,b=seed
    for x,y in zip(words[::2],words[1::2]):
        a=(a+x+b)&0xffffffff
        b=(b+y+a)&0xffffffff
    return a,b


def change_order(wal, big):
    result=bytearray(wal)
    result[:4]=struct.pack('>I',0x377f0683 if big else 0x377f0682)
    seed=checksum(result[:24],big=big)
    result[24:32]=struct.pack('>II',*seed)
    size=struct.unpack('>I',result[8:12])[0]
    for offset in range(32,len(result),size+24):
        seed=checksum(result[offset:offset+8]+result[offset+24:offset+24+size],seed,big)
        result[offset+16:offset+24]=struct.pack('>II',*seed)
    return bytes(result)


def uncommitted_frame(wal):
    size=struct.unpack('>I',wal[8:12])[0]
    big=bool(wal[3]&1)
    offset=len(wal)-size-24
    seed=struct.unpack('>II',wal[offset+16:offset+24])
    prefix=wal[offset:offset+4]+bytes(4)
    page=wal[offset+24:]
    crc=checksum(prefix+page,seed,big)
    return prefix+wal[16:24]+struct.pack('>II',*crc)+page


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=353710)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--tests',type=pathlib.Path,default=ROOT/'.lake/build/bin/sqleanite_tests')
    p.add_argument('--output',type=pathlib.Path,required=True)
    args=p.parse_args()
    assert sys.byteorder=='little','The SHM fixture driver currently targets a little-endian host.'
    rng=random.Random(args.seed)
    results,failures=[],[]
    with tempfile.TemporaryDirectory(prefix='sqleanite-wal-components-') as temp:
        for page_size in [512,1024,2048,4096,8192,16384,32768,65536]:
            folder=pathlib.Path(temp)/str(page_size);folder.mkdir()
            db=folder/'source.db'
            rows=rng.randrange(4850,5250) if page_size==4096 else rng.randrange(40,100)
            payload=4000 if page_size==4096 else rng.randrange(1500,5000)
            process=subprocess.Popen([args.sqlite,'-batch','-bail',str(db)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,bufsize=1)
            try:
                process.stdin.write(f"PRAGMA page_size={page_size}; PRAGMA journal_mode=WAL; PRAGMA wal_autocheckpoint=0; CREATE TABLE t(id INTEGER PRIMARY KEY,v); WITH RECURSIVE c(i) AS(VALUES(1) UNION ALL SELECT i+1 FROM c WHERE i<{rows}) INSERT INTO t SELECT i,zeroblob({payload}) FROM c; SELECT 'READY';\n")
                process.stdin.flush()
                while True:
                    line=process.stdout.readline()
                    if line.strip()=='READY':break
                    if not line:raise RuntimeError(process.stderr.read())
                original_main=db.read_bytes()
                original_wal=pathlib.Path(str(db)+'-wal').read_bytes()
                original_shm=pathlib.Path(str(db)+'-shm').read_bytes()
            finally:
                process.stdin.close();process.wait(timeout=30)
            wal_path=folder/'original.wal';wal_path.write_bytes(original_wal)
            shm_path=folder/'original.shm';shm_path.write_bytes(original_shm)
            tested=subprocess.run([str(args.tests),'--wal-index-fixture',str(wal_path),str(shm_path)],capture_output=True,text=True,timeout=180)
            if tested.returncode:
                failures.append(dict(page_size=page_size,phase='index',code=tested.returncode,stdout=tested.stdout,stderr=tested.stderr))
            reference=folder/'reference.db';shutil.copyfile(db,reference)
            payload_hex=bytes(rng.randrange(256) for _ in range(31)).hex()
            update=f"UPDATE t SET v=X'{payload_hex}' WHERE id%3=0; DELETE FROM t WHERE id%11=0; INSERT INTO t VALUES({rows+1},X'FF00AB');"
            changed=subprocess.run([args.sqlite,'-batch','-bail',str(reference)],input=update,capture_output=True,text=True,timeout=120)
            assert changed.returncode==0,changed.stderr
            observation='SELECT id,typeof(v),hex(v) FROM t ORDER BY id; PRAGMA integrity_check;'
            expected=subprocess.run([args.sqlite,'-batch','-bail','-readonly',str(reference),observation],capture_output=True,timeout=120)
            assert expected.returncode==0,expected.stderr
            for tail in ['clean','partial','uncommitted']:
                big=rng.choice([False,True])
                prefix=change_order(original_wal,big)
                source=prefix
                if tail=='partial':source+=bytes(rng.randrange(256) for _ in range(17))
                if tail=='uncommitted':source+=uncommitted_frame(prefix)
                wal_path.write_bytes(source)
                actual=folder/f'actual-{tail}.db';actual.write_bytes(original_main)
                destination=pathlib.Path(str(actual)+'-wal')
                append=subprocess.run([str(args.tests),'--wal-append-fixture',str(wal_path),str(reference),str(destination)],capture_output=True,text=True,timeout=180)
                if append.returncode:
                    failures.append(dict(page_size=page_size,phase='append',tail=tail,code=append.returncode,stderr=append.stderr))
                    continue
                encoded=destination.read_bytes()
                if encoded[:len(prefix)]!=prefix:
                    failures.append(dict(page_size=page_size,phase='committed-prefix-changed',tail=tail))
                observed=subprocess.run([args.sqlite,'-batch','-bail','-readonly',str(actual),observation],capture_output=True,timeout=120)
                equal=observed.returncode==0 and observed.stdout==expected.stdout
                if not equal:
                    failures.append(dict(page_size=page_size,phase='independent-SQLite-read',tail=tail,code=observed.returncode,stderr=observed.stderr.decode(),expected_sha256=sha(expected.stdout),observed_sha256=sha(observed.stdout)))
                results.append(dict(page_size=page_size,rows=rows,payload_bytes=payload,tail=tail,big_endian_checksum=big,index_returncode=tested.returncode,index_result=tested.stdout.strip(),append_result=append.stdout.strip(),input_wal_sha256=sha(source),input_shm_sha256=sha(original_shm),committed_prefix_sha256=sha(prefix),appended_wal_sha256=sha(encoded),exact_SQL_output_sha256=sha(observed.stdout),matches_reference=equal))
    source=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:
        source.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=args.seed,scope=__doc__.strip(),results=results,failures=failures,
                implementation_sha256=source.hexdigest(),test_executable_sha256=sha(args.tests.read_bytes()),
                harness_sha256=sha(pathlib.Path(__file__).read_bytes()),host_byteorder=sys.byteorder,
                sqlite_version=subprocess.check_output([args.sqlite,'--version'],text=True).strip())
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(component_cases=len(results),failures=len(failures),report=str(args.output))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
