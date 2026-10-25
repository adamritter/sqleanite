#!/usr/bin/env python3
"""Check SQLite header-size validity against the physical file size.

Create files with pinned SQLite, independently modify the size/counter fields,
and compare read behavior and subsequent writes in the two public file modes.
Successful persisted results are checked by the pinned CLI with integrity_check.
Read snapshots must preserve both main and WAL bytes. Not a concurrency test.
"""
import argparse,hashlib,json,os,random,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353930)
    p.add_argument('--random-cases',type=int,default=0)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();rng=random.Random(a.seed);cases=[]
    mutations=[('ordinary',None,False,0),('zero-size',0,False,0),('mismatched-zero',0,True,0),
        ('stale-small',1,True,0),('stale-large',1000,True,0),('trusted-too-large',1000,False,0),
        ('ignored-full-tail',None,False,1),('ignored-short-tail',None,False,-17),
        ('partial-empty-last-page',None,False,0)]
    mutations += [('random-stale',rng.randrange(0,2**32),True,0) for _ in range(a.random_cases)]
    with tempfile.TemporaryDirectory(prefix='sqleanite-header-size-') as tmp:
        tmp=Path(tmp)
        for page in [512,4096,65536]:
            seed=tmp/f'seed-{page}.db'
            setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE INDEX t_v ON t(v);'+''.join(f'INSERT INTO t VALUES({i},{rng.randrange(-1000000000,1000000000)});' for i in range(1,rng.randrange(15,60)))
            subprocess.run([a.sqlite,'-batch','-bail',str(seed)],input=setup.encode(),check=True,capture_output=True)
            original=seed.read_bytes()
            empty=tmp/f'empty-{page}.db'
            subprocess.run([a.sqlite,'-batch','-bail',str(empty)],input=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE INDEX t_v ON t(v);'.encode(),check=True,capture_output=True)
            partial=empty.read_bytes();partial=partial[:len(partial)-page+8]
            for kind,declared,mismatch,tail in mutations:
                data=bytearray(partial if kind=="partial-empty-last-page" else original)
                if declared is not None:data[28:32]=declared.to_bytes(4,'big')
                if mismatch:data[24:28]=((int.from_bytes(data[92:96],'big')+rng.randrange(1,2**32))%2**32).to_bytes(4,'big')
                if tail>0:data.extend(bytes(page*tail))
                elif tail<0:data.extend(bytes(-tail))
                for mode in ['--verified-file','--verified-wal-file']:
                    folder=tmp/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db'
                    lean.write_bytes(data);ref.write_bytes(data)
                    query='SELECT id,typeof(v),quote(v) FROM t ORDER BY id;SELECT count(*),sum(v) FROM t;'
                    q=folder/'query.sql';q.write_text(query)
                    l=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(lean),str(q)],capture_output=True,timeout=120)
                    r=subprocess.run([a.sqlite,'-readonly','-batch','-bail',str(ref)],input=query.encode(),capture_output=True,timeout=120)
                    def out(p):return dict(code=p.returncode,stdout=p.stdout.decode('latin1'),stderr=p.stderr.decode('latin1'))
                    same=(l.returncode==r.returncode==0 and l.stdout==r.stdout) or (l.returncode>0 and r.returncode>0)
                    assert lean.read_bytes()==data and not Path(str(lean)+'-wal').exists(),'read modified a database'
                    item=dict(page_size=page,input_bytes=len(data),mode=mode,mutation=kind,declared_size=declared,counter_mismatch=mismatch,tail_bytes=page*tail if tail>0 else -tail,read_matched=same,lean_read=out(l),sqlite_read=out(r))
                    if r.returncode==0:
                        update='UPDATE t SET v=v+10 WHERE id=1;INSERT INTO t VALUES(1000,12);'
                        q.write_text(update)
                        lw=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(lean),str(q)],capture_output=True,timeout=120)
                        rw=subprocess.run([a.sqlite,'-batch','-bail',str(ref)],input=update.encode(),capture_output=True,timeout=120)
                        check='PRAGMA integrity_check;'+query
                        li=subprocess.run([a.sqlite,'-batch','-bail',str(lean)],input=check.encode(),capture_output=True,timeout=120)
                        ri=subprocess.run([a.sqlite,'-batch','-bail',str(ref)],input=check.encode(),capture_output=True,timeout=120)
                        item.update(write_matched=lw.returncode==rw.returncode==li.returncode==ri.returncode==0 and li.stdout==ri.stdout and li.stdout.startswith(b'ok\n'),lean_write=out(lw),sqlite_write=out(rw),lean_after=out(li),sqlite_after=out(ri))
                    cases.append(item)
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    failures=[i for i,c in enumerate(cases) if not c['read_matched'] or not c.get('write_matched',True)]
    report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,failed_case_indices=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=len(failures))))
    return bool(failures)
if __name__=='__main__':raise SystemExit(main())
