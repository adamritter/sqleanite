#!/usr/bin/env python3
"""Live SQLite 3.53.4 / Lean WAL interoperability and lock regressions.

Both databases and observer connections remain real files/processes. The
reference executable is used only by this test, never by the Lean runtime.
"""
import argparse, concurrent.futures, fcntl, hashlib, json, os, pathlib, random, select, signal, struct, subprocess, tempfile, time

ROOT=pathlib.Path(__file__).resolve().parents[1]

class SQLite:
    def __init__(self, executable, db, readonly=False):
        argv=[executable,'-batch']+(['-readonly'] if readonly else [])+[str(db)]
        self.p=subprocess.Popen(argv,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        self.buffer=b''
        self.counter=0
    def query(self, sql, timeout=45):
        self.counter+=1
        marker=f'__sqleanite_end_{self.counter}__'.encode()
        self.p.stdin.write(sql.encode()+b'\n.print '+marker+b'\n')
        lines=[];deadline=time.monotonic()+timeout
        while True:
            if b'\n' in self.buffer:
                line,self.buffer=self.buffer.split(b'\n',1)
                if line==marker: return b'\n'.join(lines).decode()+ ('\n' if lines else '')
                lines.append(line);continue
            wait=max(0,deadline-time.monotonic())
            assert wait and select.select([self.p.stdout],[],[],wait)[0], 'SQLite observer timeout'
            chunk=os.read(self.p.stdout.fileno(),65536)
            assert chunk,'SQLite observer exited'
            self.buffer+=chunk
    def close(self):
        if self.p.poll() is None:
            self.p.stdin.close();self.p.wait(timeout=20)
        err=self.p.stderr.read().decode()
        assert self.p.returncode==0 and not err, (self.p.returncode,err)

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',default=str(ROOT/'.lake/build/bin/sqleanite'))
    p.add_argument('--sqlite',default=os.environ['SQLITE3_BIN'])
    p.add_argument('--seed',type=int,default=356001)
    p.add_argument('--fixtures',type=int,default=6)
    p.add_argument('--large-index',action='store_true')
    p.add_argument('--output',type=pathlib.Path,required=True)
    a=p.parse_args();rng=random.Random(a.seed);cases=[];failures=[]
    def check(name,actual,expected):
        result=dict(name=name,actual=actual,expected=expected,matches=actual==expected)
        cases.append(result)
        if not result['matches']: failures.append(result)
    with tempfile.TemporaryDirectory(prefix='sqleanite-live-wal-') as tmp:
        directory=pathlib.Path(tmp)
        def lean(db,sql='',checkpoint=False):
            argv=[a.lean,'--verified-wal-checkpoint' if checkpoint else '--verified-wal-file',str(db)]
            r=subprocess.run(argv,input=sql,text=True,capture_output=True,timeout=180)
            return dict(code=r.returncode,stdout=r.stdout,stderr=r.stderr)
        def success(db,sql):
            r=lean(db,sql);assert r['code']==0,r
            return r['stdout']
        def read(db):
            r=subprocess.run([a.sqlite,'-readonly',str(db),'SELECT count(*),sum(length(p)) FROM t; PRAGMA integrity_check;'],text=True,capture_output=True,timeout=60)
            assert r.returncode==0,r.stderr
            return r.stdout
        for fixture in range(a.fixtures):
            db=directory/f'case{fixture}.db';n=rng.randint(30,85);width=rng.randint(600,1800)
            origin='lean' if fixture%2==0 else 'sqlite'
            sql='CREATE TABLE t(id INTEGER PRIMARY KEY,p BLOB); BEGIN;'+''.join(f"INSERT INTO t VALUES({i},'x');" for i in range(1,n+1))+'COMMIT;'
            owner=None
            if origin=='lean':success(db,sql)
            else:
                owner=SQLite(a.sqlite,db)
                owner.query('PRAGMA journal_mode=WAL; PRAGMA wal_autocheckpoint=0;'+sql)
            observer=SQLite(a.sqlite,db,readonly=True)
            active=fixture%3!=0
            prefix=f'{fixture}-{origin}-'+('active' if active else 'idle')
            query='SELECT count(*),sum(length(p)) FROM t;'
            try:
                before=observer.query(('BEGIN;' if active else '')+query)
                check(prefix+'-before',before,f'{n}|{n}\n')
                wal=pathlib.Path(str(db)+'-wal');shm=pathlib.Path(str(db)+'-shm')
                header=shm.read_bytes();max_frame=struct.unpack_from('=I',header,16)[0]
                page_size=struct.unpack_from('>I',wal.read_bytes(),8)[0]
                end=32+max_frame*(page_size+24)
                old=wal.read_bytes()[:end];inodes=(wal.stat().st_ino,shm.stat().st_ino)
                success(db,f'UPDATE t SET p=zeroblob({width});')
                check(prefix+'-committed-prefix',wal.read_bytes()[:end]==old,True)
                check(prefix+'-inodes',(wal.stat().st_ino,shm.stat().st_ino),inodes)
                latest=f'{n}|{n*width}\n'
                check(prefix+'-snapshot',observer.query(query),before if active else latest)
                check(prefix+'-new-reader',read(db),latest+'ok\n')
                check(prefix+'-lean-read',success(db,query),latest)
                if active:
                    frozen=(db.read_bytes(),wal.read_bytes())
                    attempted=lean(db,checkpoint=True)
                    check(prefix+'-checkpoint-busy',attempted['code']!=0 and 'database is locked' in attempted['stderr'],True)
                    check(prefix+'-busy-is-readonly',(db.read_bytes(),wal.read_bytes())==frozen,True)
                    check(prefix+'-snapshot-after-busy',observer.query(query),before)
                    check(prefix+'-end-snapshot',observer.query('COMMIT;'+query),latest)
                cp=lean(db,checkpoint=True)
                check(prefix+'-checkpoint',cp['code'],0)
                check(prefix+'-idle-after-checkpoint',observer.query(query+'PRAGMA integrity_check;'),latest+'ok\n')
                # SQLite may restart this very WAL after a full backfill.
                if owner is None:owner=SQLite(a.sqlite,db)
                owner.query(f"INSERT INTO t VALUES({n+1},'sql');")
                mixed=f'{n+1}|{n*width+3}\n'
                check(prefix+'-sqlite-after-checkpoint',success(db,query),mixed)
                success(db,f"INSERT INTO t VALUES({n+2},'lean');")
                check(prefix+'-lean-after-restart',observer.query(query+'PRAGMA integrity_check;'),f'{n+2}|{n*width+7}\nok\n')
                # A real SQLite write transaction owns POSIX WAL_WRITE_LOCK.
                owner.query('BEGIN IMMEDIATE; UPDATE t SET p=zeroblob(23) WHERE id=1;')
                frozen=(db.read_bytes(),wal.read_bytes())
                blocked=lean(db,"INSERT INTO t VALUES(999999,'blocked');")
                check(prefix+'-writer-busy',blocked['code']!=0 and 'database is locked' in blocked['stderr'],True)
                check(prefix+'-writer-busy-preserves-files',(db.read_bytes(),wal.read_bytes())==frozen,True)
                check(prefix+'-read-with-uncommitted-writer',success(db,query),f'{n+2}|{n*width+7}\n')
                owner.query('ROLLBACK;')
                check(prefix+'-rollback-visible',success(db,query),f'{n+2}|{n*width+7}\n')
                # Fresh connection must still read correctly after Lean exits.
                check(prefix+'-integrity',read(db),f'{n+2}|{n*width+7}\nok\n')
                success(db,'CREATE TABLE u(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO u VALUES(7,\'schema\');')
                check(prefix+'-new-schema',observer.query('SELECT id,v FROM u;'),'7|schema\n')
                success(db,'UPDATE t SET p=zeroblob(3500);')
                check(prefix+'-relocated-root',observer.query('SELECT id,v FROM u;PRAGMA integrity_check;'),'7|schema\nok\n')
                success(db,'ALTER TABLE u RENAME COLUMN v TO payload;')
                check(prefix+'-renamed-column',observer.query('SELECT id,payload FROM u;'),'7|schema\n')
                success(db,'DROP TABLE u;')
                check(prefix+'-dropped-schema',observer.query("SELECT count(*) FROM sqlite_schema WHERE name='u';"),'0\n')
            finally:
                observer.close()
                if owner:owner.close()
        # Freeze a real Lean writer after it has acquired the SQLite write byte.
        # This verifies both directions of the native lock conflict and checks
        # that unrelated pread/pwrite closes do not silently release the lock.
        db=directory/'paused-writer.db';owner=SQLite(a.sqlite,db)
        writer=None;descriptor=None
        try:
            owner.query("PRAGMA journal_mode=WAL;PRAGMA wal_autocheckpoint=0;CREATE TABLE t(id INTEGER PRIMARY KEY,p BLOB);WITH RECURSIVE n(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM n WHERE x<1500) INSERT INTO t SELECT x,'x' FROM n;")
            descriptor=os.open(str(db)+'-shm',os.O_RDONLY)
            writer=subprocess.Popen([a.lean,'--verified-wal-file',str(db)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            writer.stdin.write(b'UPDATE t SET p=zeroblob(1800);');writer.stdin.close()
            locked=False;deadline=time.monotonic()+15
            while time.monotonic()<deadline and writer.poll() is None:
                request=struct.pack('hhqqii',fcntl.F_RDLCK,os.SEEK_SET,120,1,0,0)
                held=struct.unpack('hhqqii',fcntl.fcntl(descriptor,fcntl.F_GETLK,request))[0]
                if held==fcntl.F_WRLCK:
                    os.kill(writer.pid,signal.SIGSTOP);locked=True;break
                time.sleep(0.001)
            check('paused-lean-writer-lock-observed',locked,True)
            if locked:
                check('read-during-lean-writer',success(db,'SELECT count(*),sum(length(p)) FROM t;'),'1500|1500\n')
                check('sqlite-read-during-lean-writer',owner.query('SELECT count(*),sum(length(p)) FROM t;'),'1500|1500\n')
                competing=subprocess.run([a.sqlite,str(db),"INSERT INTO t VALUES(999999,'blocked');"],capture_output=True,text=True,timeout=10)
                check('sqlite-writer-blocked-by-lean',competing.returncode!=0 and 'database is locked' in competing.stderr,True)
                os.kill(writer.pid,signal.SIGCONT)
            writer.wait(timeout=120)
            check('paused-lean-writer-completed',dict(code=writer.returncode,stderr=writer.stderr.read().decode()),dict(code=0,stderr=''))
            check('paused-lean-writer-final',owner.query('SELECT count(*),sum(length(p)) FROM t;PRAGMA integrity_check;'),'1500|2700000\nok\n')
        finally:
            if writer and writer.poll() is None:
                os.kill(writer.pid,signal.SIGCONT);writer.kill();writer.wait()
            if descriptor is not None:os.close(descriptor)
            owner.close()
        # Race Lean-only opens too: no permanent SQLite connection keeps DMS
        # alive for this test. Each read may observe any committed prefix.
        db=directory/'lean-only.db';success(db,'CREATE TABLE t(id INTEGER PRIMARY KEY,p);')
        jobs=[('writer',i) for i in range(1,9)]+[('reader',i) for i in range(24)]
        rng.shuffle(jobs)
        def worker(job):
            kind,i=job
            return job,lean(db,f'INSERT INTO t VALUES({i},{i});' if kind=='writer' else 'SELECT count(*) FROM t;')
        with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
            for (kind,i),result in pool.map(worker,jobs):
                check(f'lean-only-{kind}-{i}',result['code'],0)
                if kind=='reader' and result['code']==0:
                    check(f'lean-only-prefix-{i}',0<=int(result['stdout'].strip())<=8,True)
        check('lean-only-final',success(db,'SELECT count(*),sum(p) FROM t;'),'8|36\n')
        if a.large_index:
            db=directory/'regions.db';owner=SQLite(a.sqlite,db)
            try:
                owner.query("PRAGMA journal_mode=WAL;PRAGMA wal_autocheckpoint=0;CREATE TABLE t(id INTEGER PRIMARY KEY,p BLOB);INSERT INTO t VALUES(1,'x');")
                owner.query(''.join(f"UPDATE t SET p='{i}';" for i in range(4100)),timeout=120)
                shm=pathlib.Path(str(db)+'-shm')
                initial=struct.unpack_from('=I',shm.read_bytes(),16)[0]
                check('multiple-index-regions-before',initial>4062,True)
                success(db,"INSERT INTO t VALUES(2,'lean');")
                check('multiple-index-regions-read',owner.query('SELECT id,p FROM t ORDER BY id;PRAGMA integrity_check;'),'1|4099\n2|lean\nok\n')
            finally:owner.close()
    report=dict(purpose=__doc__.strip(),seed=a.seed,fixtures=a.fixtures,cases=cases,failures=failures,
        sqlite_identity=subprocess.check_output([a.sqlite,':memory:','SELECT sqlite_version(),sqlite_source_id();'],text=True).strip(),
        executable_sha256=digest(pathlib.Path(a.lean)),native_sha256=digest(ROOT/'native/sqleanite_vfs.c'),harness_sha256=digest(pathlib.Path(__file__)))
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(cases=len(cases),failures=len(failures),output=str(a.output))))
    return bool(failures)

if __name__=='__main__':raise SystemExit(main())
