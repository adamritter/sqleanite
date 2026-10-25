#!/usr/bin/env python3
"""Compare reads of SQLite pages with nonzero reserved tails.

The pinned CLI creates records, indexes and overflow chains using the selected
usable page size. Explicitly marked private tail bytes must survive reads.
Closed-writer WAL overlays are included. This suite makes no write-support or
concurrent-locking claim for reserved-byte databases.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353940)
    p.add_argument('--random-cases',type=int,default=0)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();rng=random.Random(a.seed);cases=[];fixtures=[];guards=[]
    configs=[(512,0,False),(512,1,False),(512,16,False),(512,32,False),
        (1024,255,False),(4096,1,False),(4096,16,False),(4096,255,False),(65536,255,False),
        (512,32,True),(4096,16,True),(65536,255,True)]
    for _ in range(a.random_cases):
        page=rng.choice([512,1024,2048,4096,8192,65536]);configs.append((page,rng.randrange(1,min(255,page-480)+1),bool(rng.randrange(2))))
    with tempfile.TemporaryDirectory(prefix='sqleanite-reserved-') as tmp:
        for number,(page,reserve,overlay) in enumerate(configs):
            folder=Path(tmp)/str(number);folder.mkdir();ref=folder/'sqlite.db'
            rows=[]
            for i in range(1,19):
                length=rng.choice([0,8,100,page//2,page+23,page*2+31])
                payload=bytes([97+i%26])*length
                rows.append(f"INSERT INTO t VALUES({i},CAST(X'{payload.hex()}' AS TEXT),{rng.randrange(-10000,10000)});")
            setup=f'PRAGMA page_size={page};\n.filectrl reserve_bytes {reserve}\nCREATE TABLE t(id INTEGER PRIMARY KEY,v,n);CREATE INDEX t_n ON t(n);CREATE INDEX t_v ON t(v);BEGIN;'+''.join(rows)+'COMMIT;'
            r=subprocess.run([a.sqlite,'-batch','-bail',str(ref)],input=setup.encode(),capture_output=True,timeout=120)
            assert r.returncode==0,r.stderr
            raw=bytearray(ref.read_bytes());assert raw[20]==reserve
            if reserve:
                for offset in range(page,len(raw)+1,page):raw[offset-reserve:offset]=bytes(rng.randrange(256) for _ in range(reserve))
                ref.write_bytes(raw)
            if overlay:
                sql="PRAGMA journal_mode=WAL;\n.dbconfig no_ckpt_on_close on\nPRAGMA wal_autocheckpoint=0;UPDATE t SET n=n+1 WHERE id%2=0;INSERT INTO t VALUES(99,'new',123);"
                r=subprocess.run([a.sqlite,'-batch','-bail',str(ref)],input=sql.encode(),capture_output=True,timeout=120);assert r.returncode==0,r.stderr
                assert Path(str(ref)+'-wal').exists()
            check=subprocess.run([a.sqlite,'-readonly','-batch','-bail',str(ref)],input=b"PRAGMA integrity_check;SELECT name,pagetype,count(*) FROM dbstat GROUP BY name,pagetype;",capture_output=True,timeout=120)
            assert check.returncode==0 and check.stdout.startswith(b'ok\n'),check.stderr
            fixtures.append(dict(page_size=page,reserved=reserve,usable=page-reserve,wal_overlay=overlay,topology=check.stdout.decode().splitlines()[1:]))
            for mode in (['--verified-wal-file'] if overlay else ['--verified-file','--verified-wal-file']):
                dest=folder/mode;dest.mkdir();lean=dest/'lean.db';shutil.copyfile(ref,lean)
                for suffix in ['-wal','-shm']:
                    if Path(str(ref)+suffix).exists():shutil.copyfile(str(ref)+suffix,str(lean)+suffix)
                paths=[lean,Path(str(lean)+'-wal')]
                before={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in paths if f.exists()}
                queries=['SELECT id,length(v),hex(substr(v,1,3)),n FROM t ORDER BY id;',
                    'SELECT count(*),sum(n),min(n),max(n),sum(length(v)) FROM t;',
                    'SELECT id,n FROM t WHERE id=7;','SELECT id,n FROM t WHERE n<0 ORDER BY n,id;',
                    'SELECT id,length(v) FROM t WHERE length(v)>2000 ORDER BY id;',
                    "SELECT typeof(v),hex(v) FROM t WHERE id=2;",
                    'SELECT id FROM t ORDER BY v,id LIMIT 5;']
                for sql in queries:
                    q=dest/'read.sql';q.write_text(sql)
                    l=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(lean),str(q)],capture_output=True,timeout=120)
                    r=subprocess.run([a.sqlite,'-readonly','-batch','-bail',str(ref)],input=sql.encode(),capture_output=True,timeout=120)
                    def out(p):return dict(code=p.returncode,stdout=p.stdout.decode('latin1'),stderr=p.stderr.decode('latin1'))
                    cases.append(dict(fixture=number,mode=mode,sql=sql,matched=l.returncode==r.returncode==0 and l.stdout==r.stdout,lean=out(l),sqlite=out(r)))
                after={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in paths if f.exists()}
                assert before==after,'reserved page read modified input bytes'
                if reserve:
                    q.write_text('UPDATE t SET n=n+1 WHERE id=1;')
                    l=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(lean),str(q)],capture_output=True,timeout=120)
                    after={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in paths if f.exists()}
                    guards.append(dict(fixture=number,mode=mode,operation='UPDATE',passed=l.returncode!=0 and b'unsupported reserved-byte database writes' in l.stderr and before==after,lean=out(l),bytes_unchanged=before==after))
                    if overlay:
                        l=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),'--verified-wal-checkpoint',str(lean)],capture_output=True,timeout=120)
                        after={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in paths if f.exists()}
                        guards.append(dict(fixture=number,mode=mode,operation='checkpoint',passed=l.returncode!=0 and b'unsupported reserved-byte database writes' in l.stderr and before==after,lean=out(l),bytes_unchanged=before==after))
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=a.seed,random_cases=a.random_cases,fixtures=fixtures,cases=cases,unsupported_write_guards=guards,guard_failures=sum(not g['passed'] for g in guards),failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'],guards=len(guards),guard_failures=report['guard_failures'])))
    return bool(report['failures'] or report['guard_failures'])
if __name__=='__main__':raise SystemExit(main())
