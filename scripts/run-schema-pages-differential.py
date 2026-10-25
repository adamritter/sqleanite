#!/usr/bin/env python3
"""Read pinned SQLite schemas that span interior, leaf and overflow pages.

Compare exact results in both public file readers, including committed WAL
schema overlays. Preserve input main/WAL bytes. These are read compatibility
checks; they do not establish large-schema write support or concurrent locking.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
    p.add_argument('--seed',type=int,default=353920)
    p.add_argument('--random-cases',type=int,default=0)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();rng=random.Random(a.seed);outcomes=[];fixtures=[]
    configs=[(512,1,3,False),(512,25,10,False),(512,220,30,False),
        (1024,80,15,False),(4096,120,40,False),(65536,450,80,False),
        (512,2,1500,False),(4096,2,8500,False),(65536,2,70000,False),
        (512,80,20,True),(4096,80,40,True),(4096,2,8500,True)]
    configs += [(rng.choice([512,1024,2048,4096,8192]),rng.randrange(10,110),rng.randrange(8,100),bool(rng.randrange(2))) for _ in range(a.random_cases)]
    with tempfile.TemporaryDirectory(prefix='sqleanite-schema-') as tmp:
        for number,(page,count,padding,overlay) in enumerate(configs):
            folder=Path(tmp)/str(number);folder.mkdir();ref=folder/'sqlite.db'
            names=['t'+str(i)+'_'+''.join(rng.choice('abcdefghjkmnpqrstuvwx') for _ in range(padding)) for i in range(count)]
            prefix=f'PRAGMA page_size={page};CREATE TABLE anchor(id INTEGER PRIMARY KEY,v);INSERT INTO anchor VALUES(1,17);'
            schema='BEGIN;'+''.join(f'CREATE TABLE "{name}"(id INTEGER PRIMARY KEY,v);INSERT INTO "{name}" VALUES(1,{i+23});'+(f'CREATE INDEX "i_{name}" ON "{name}"(v);' if i%3==0 else '') for i,name in enumerate(names))+'COMMIT;'
            def reference(sql):return subprocess.run([a.sqlite,'-batch','-bail',str(ref)],input=sql.encode(),capture_output=True,timeout=120)
            initial=reference(prefix);assert initial.returncode==0,initial.stderr
            if overlay:schema='PRAGMA journal_mode=WAL;\n.dbconfig no_ckpt_on_close on\nPRAGMA wal_autocheckpoint=0;'+schema
            generated=reference(schema);assert generated.returncode==0,generated.stderr
            if overlay:assert Path(str(ref)+'-wal').exists(),'producing SQLite closed without retaining WAL'
            # The producing connection is closed before making or opening copies.
            meta=subprocess.run([a.sqlite,'-readonly','-batch','-bail',str(ref)],input=b"SELECT pagetype,count(*) FROM dbstat WHERE name='sqlite_schema' GROUP BY pagetype;PRAGMA integrity_check;",capture_output=True,timeout=120)
            assert meta.returncode==0 and meta.stdout.endswith(b'ok\n'),meta.stderr
            wal=Path(str(ref)+'-wal')
            if overlay:assert wal.exists() and wal.stat().st_size>32,'read-only observer removed WAL'
            fixtures.append(dict(page_size=page,tables=count+1,name_padding=padding,wal_overlay=overlay,wal_frames=(wal.stat().st_size-32)//(page+24) if wal.exists() else 0,schema_pages=meta.stdout.decode().splitlines()[:-1]))
            for mode in (['--verified-wal-file'] if overlay else ['--verified-file','--verified-wal-file']):
                dest=folder/mode;dest.mkdir();lean=dest/'lean.db'
                shutil.copyfile(ref,lean)
                for suffix in ['-wal','-shm']:
                    if Path(str(ref)+suffix).exists():shutil.copyfile(str(ref)+suffix,str(lean)+suffix)
                paths=[lean,Path(str(lean)+'-wal')]
                before={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in paths if f.exists()}
                queries=['SELECT id,v FROM anchor;']
                for i in sorted({0,count//2,count-1}):
                    name=names[i]
                    queries += [f'SELECT id,typeof(v),quote(v) FROM "{name}";',
                        f'SELECT sum(v),count(*),group_concat(v) FROM "{name}";',
                        f'SELECT v FROM "{name}" WHERE v={i+23};']
                for sql in queries:
                    q=dest/'read.sql';q.write_text(sql)
                    left=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(lean),str(q)],capture_output=True,timeout=120)
                    right=subprocess.run([a.sqlite,'-readonly','-batch','-bail',str(ref)],input=sql.encode(),capture_output=True,timeout=120)
                    same=left.returncode==right.returncode==0 and left.stdout==right.stdout
                    def result(p):return dict(code=p.returncode,stdout=p.stdout.decode('latin1'),stderr=p.stderr.decode('latin1'))
                    outcomes.append(dict(fixture=number,mode=mode,sql=sql,matched=same,lean=result(left),sqlite=result(right)))
                after={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in paths if f.exists()}
                assert before==after,'schema read modified input database/WAL'
                if number==2:
                    original=ref.read_bytes()
                    assert original[100]==5
                    pointer=int.from_bytes(original[112:114],'big')
                    first_child=int.from_bytes(original[pointer:pointer+4],'big')
                    changes=[('child-cycle',pointer,1,4),('zero-child',pointer,0,4),
                        ('outside-file',pointer,len(original)//page+1,4),
                        ('repeated-child',108,first_child,4),('header-cell-pointer',112,101,2)]
                    for kind,offset,replacement,width in changes:
                        corrupted=bytearray(original);corrupted[offset:offset+width]=replacement.to_bytes(width,'big')
                        bad=dest/(kind+'.db');bad.write_bytes(corrupted)
                        oracle=dest/(kind+'-sqlite.db');oracle.write_bytes(corrupted)
                        sql='SELECT id,v FROM anchor;';q=dest/'bad.sql';q.write_text(sql)
                        left=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(bad),str(q)],capture_output=True,timeout=120)
                        right=subprocess.run([a.sqlite,'-readonly','-batch','-bail',str(oracle)],input=sql.encode(),capture_output=True,timeout=120)
                        same=left.returncode>0 and right.returncode>0
                        outcomes.append(dict(fixture=number,mode=mode,kind=kind,sql=sql,matched=same,lean=result(left),sqlite=result(right)))
                        assert bad.read_bytes()==oracle.read_bytes()==corrupted,'rejected schema modified input'
    d=hashlib.sha256()
    for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
    report=dict(seed=a.seed,random_cases=a.random_cases,fixtures=fixtures,cases=outcomes,failures=sum(not c['matched'] for c in outcomes),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(outcomes),failures=report['failures'])))
    return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
