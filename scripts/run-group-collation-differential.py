#!/usr/bin/env python3
"""Compare collated column grouping, aggregate values and representative rows.
Uses fresh seeded tables in both production modes, exact CLI bytes, and verifies
that all read queries preserve database and WAL bytes. Every mismatch is kept.
"""
import argparse,hashlib,json,os,pathlib,random,subprocess,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=353740);p.add_argument('--random-cases',type=int,default=100);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'));p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 vals=["NULL","1","1.0","'1'","'a'","'A'","'a '","'A  '","'B'","'b'","'Á'","'á'","X'41'","CAST(X'410078' AS TEXT)","CAST(X'610059' AS TEXT)","CAST(X'FF41' AS TEXT)","CAST(X'FF61' AS TEXT)"]
 setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v,w,n); CREATE TABLE empty(id INTEGER PRIMARY KEY,v,w,n);'
 for i,v in enumerate(vals+[rng.choice(vals) for _ in range(35)],1):setup+=f'INSERT INTO t VALUES({i},{v},{rng.choice(vals[:10])},{rng.choice(["NULL","-3","0","1","1.0","2","5"])});'
 setup+="CREATE TABLE big(id INTEGER PRIMARY KEY,v,n);INSERT INTO big VALUES(1,'a',9223372036854775807),(2,'A',1),(3,'b',0),(4,'c',9223372036854775807),(5,'C',1);"
 queries=[]
 for collation in ['BINARY','NOCASE','RTRIM']:
  for projection in ['v,count(*)','v,count(n),sum(n),avg(n),total(n)','v,min(n),max(n)','v,max(n),min(n),max(n)','v,sum(n)','v COLLATE NOCASE,count(*)','v COLLATE missing,count(*)']:
   for where in ['', ' WHERE id<20', " WHERE v COLLATE NOCASE='a'",' WHERE 0']:
    queries.append(f'SELECT {projection} FROM t{where} GROUP BY v COLLATE {collation};')
  for projection in ['v,w,count(*)','w,v,min(n),max(n),count(n)','v,w,sum(n)']:
   for other in ['BINARY','NOCASE','RTRIM']:
    queries.append(f'SELECT {projection} FROM t GROUP BY v COLLATE {collation},w COLLATE {other};')
  queries += [f'SELECT v,count(*) FROM t AS x GROUP BY x.v COLLATE {collation};',f'SELECT v,count(*) FROM empty GROUP BY v COLLATE {collation};']
 for _ in range(a.random_cases):
  c,d=rng.choices(['BINARY','NOCASE','RTRIM'],k=2);limit=rng.randrange(0,55)
  projection=rng.choice(['v,count(*)','v,count(n),sum(n)','v,min(n),max(n),min(n)','v,max(n),min(n)','v,avg(n),total(n)'])
  queries.append(f'SELECT {projection} FROM t WHERE id>{limit} GROUP BY v COLLATE {c} COLLATE {d};')
  queries.append(f'SELECT {projection} FROM t WHERE id>{limit} GROUP BY v COLLATE {c} LIMIT {rng.randrange(0,9)} OFFSET {rng.randrange(0,5)};')
 for sql in ['SELECT v,count(*) FROM t GROUP BY v COLLATE missing;','SELECT v,count(*) FROM empty GROUP BY v COLLATE missing;','SELECT v,count(*) FROM t GROUP BY v COLLATE missing COLLATE NOCASE;','SELECT v,count(*) FROM t GROUP BY v COLLATE NOCASE LIMIT 0;','SELECT v,count(*) FROM t GROUP BY v COLLATE NOCASE ORDER BY v;','SELECT v,count(*) FROM t GROUP BY v COLLATE NOCASE HAVING count(*)>1;','SELECT v,count(*) FROM t GROUP BY v COLLATE NOCASE WHERE 0;']:
  queries.append(sql)
 queries += ["SELECT v,sum(n) FROM big GROUP BY v COLLATE NOCASE LIMIT 0;", "SELECT v,sum(n) FROM big GROUP BY v COLLATE NOCASE LIMIT 1 OFFSET 1;", "SELECT v,sum(n) FROM big WHERE id>2 GROUP BY v COLLATE NOCASE LIMIT 1;", "SELECT v,sum(n) FROM big WHERE id>2 GROUP BY v COLLATE NOCASE LIMIT 1 OFFSET 1;", "SELECT v,count(*) FROM t GROUP BY v COLLATE missing LIMIT 0;"]
 failures=[];phases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-group-collation-') as tmp:
  for mode in ['--verified-file','--verified-wal-file']:
   folder=pathlib.Path(tmp)/mode;folder.mkdir()
   def run(sql):
    q=folder/'query.sql';q.write_text(sql)
    l=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(folder/'lean.db'),str(q)],capture_output=True,timeout=120)
    r=subprocess.run([a.sqlite,'-batch','-bail',str(folder/'sqlite.db')],input=sql.encode(),capture_output=True,timeout=120)
    return l,r
   l,r=run(setup);assert l.returncode==r.returncode==0,(l.stderr,r.stderr)
   def snapshot():return {f.name:f.read_bytes() for f in folder.iterdir() if f.name in ['lean.db','lean.db-wal','sqlite.db','sqlite.db-wal']}
   before=snapshot();errors=0
   for sql in queries:
    l,r=run(sql);same=(l.returncode==r.returncode==0 and l.stdout==r.stdout) or(l.returncode>0 and r.returncode>0)
    if not same:
     def out(x):return dict(code=x.returncode,stdout=x.stdout.decode('latin1'),stderr=x.stderr.decode('latin1'))
     failures.append(dict(mode=mode,sql=sql,lean=out(l),sqlite=out(r)))
    elif l.returncode:errors+=1
   assert before==snapshot(),'GROUP BY modified input bytes'
   phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,random_cases=a.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
 return bool(failures)
if __name__=='__main__':raise SystemExit(main())
