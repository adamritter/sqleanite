#!/usr/bin/env python3
"""Compare compound result collations and representatives with pinned SQLite.
Exact CLI bytes/rejection status, both live file modes, immutable read inputs.
All mismatches are retained, including unsupported outer ORDER BY/LIMIT.
"""
import argparse,hashlib,json,os,pathlib,random,subprocess,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=353750);p.add_argument('--random-cases',type=int,default=150);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'));p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 values=["NULL","1","1.0","'1'","'A'","'a'","'a '","'A  '","X'41'","CAST(X'410062' AS TEXT)","CAST(X'610042' AS TEXT)","CAST(X'FF41' AS TEXT)","CAST(X'FF61' AS TEXT)"]
 setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v);'+''.join(f'INSERT INTO t VALUES({i},{v});' for i,v in enumerate(values+[rng.choice(values) for _ in range(12)],1))
 c=['',' COLLATE BINARY',' COLLATE NOCASE',' COLLATE RTRIM'];ops=['UNION','UNION ALL','INTERSECT','EXCEPT'];queries=[]
 for left,right in [("'A'","'a'"),("'a'","'a '"),("1","1.0"),("NULL","NULL")]:
  for lc in c:
   for rc in c:
    for op in ops:queries.append(f'SELECT {left}{lc} {op} SELECT {right}{rc};')
 for lc in c:
  for rc in c:
   for op in ops:
    queries += [f'SELECT v{lc} FROM t {op} SELECT v{rc} FROM t WHERE id%2=0;',f'SELECT v{lc},id%2 FROM t {op} SELECT v{rc},id%3 FROM t;',f'SELECT \'a\'{lc} {op} SELECT v{rc} FROM t;',f'SELECT v{lc} FROM t {op} SELECT \'a\'{rc};']
 for expr in ['v','+v',"v||''",'CAST(v AS TEXT)','lower(v)','"v"',"coalesce(v,'')","ifnull(v,'')","min(v,'z')",'CASE WHEN 1 THEN v END']:
  for op in ops:
   queries.append(f'SELECT {expr} FROM t {op} SELECT \'a\' COLLATE NOCASE;')
 for _ in range(a.random_cases):
  choices=rng.choices(values,k=3);collations=rng.choices(c,k=3);op1,op2=rng.choices(ops,k=2)
  queries.append(f'SELECT {choices[0]}{collations[0]} {op1} SELECT {choices[1]}{collations[1]} {op2} SELECT {choices[2]}{collations[2]};')
 queries += ["SELECT 'A' COLLATE NOCASE UNION SELECT 'a' ORDER BY 1;", "SELECT 'A' COLLATE NOCASE UNION SELECT 'a' LIMIT 1;", "SELECT 1 COLLATE missing UNION ALL SELECT 2;", "SELECT 1 COLLATE missing UNION SELECT 2;", "SELECT v FROM t UNION SELECT 'a' COLLATE missing;", "SELECT 'a' UNION SELECT 'A' COLLATE missing;", "SELECT v COLLATE NOCASE FROM t UNION SELECT 1,2;", "SELECT v COLLATE NOCASE FROM t WHERE 0 UNION SELECT 'A';", "SELECT min(v COLLATE NOCASE) FROM t UNION SELECT 'a';", "SELECT * FROM t UNION SELECT 99,'a' COLLATE NOCASE;"]
 queries += ["SELECT a.v FROM t AS a JOIN t AS b ON a.id=b.id UNION SELECT 'a' COLLATE NOCASE;", "SELECT a.* FROM t AS a JOIN t AS b ON a.id=b.id UNION SELECT 99,'a' COLLATE NOCASE;", "SELECT 'A' UNION ALL SELECT 'a' UNION SELECT NULL COLLATE NOCASE;", "SELECT 'A' COLLATE NOCASE UNION ALL SELECT 'a' EXCEPT SELECT 'a';", "SELECT 1 COLLATE missing UNION ALL SELECT 2 COLLATE NOCASE UNION ALL SELECT 3;", "SELECT 1 COLLATE BINARY UNION SELECT 2 COLLATE missing;"]
 failures=[];phases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-compound-collation-') as tmp:
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
    l,r=run(sql);same=(l.returncode==r.returncode==0 and l.stdout==r.stdout) or (l.returncode>0 and r.returncode>0)
    if not same:
     def out(x):return dict(code=x.returncode,stdout=x.stdout.decode('latin1'),stderr=x.stderr.decode('latin1'))
     failures.append(dict(mode=mode,sql=sql,lean=out(l),sqlite=out(r)))
    elif l.returncode:errors+=1
   assert before==snapshot(),'compound read changed input bytes'
   phases.append(dict(mode=mode,queries=len(queries),matching_errors=errors))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,random_cases=a.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(queries=sum(p['queries'] for p in phases),failures=len(failures))))
 return bool(failures)
if __name__=='__main__':raise SystemExit(main())
