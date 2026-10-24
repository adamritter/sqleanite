#!/usr/bin/env python3
"""Compare explicit expression collations with pinned SQLite through both live
file modes. Exact CLI bytes or ordinary error status are compared; every
mismatch is retained. Read-only queries must preserve main/WAL bytes.
"""
import argparse,hashlib,json,os,pathlib,random,subprocess,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[1]

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--seed',type=int,default=353730);p.add_argument('--random-cases',type=int,default=200)
 p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','/usr/bin/sqlite3'))
 p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 values=["NULL","1","1.0","'1'","'A'","'a'","'a '","'A  '","'á'","'Á'","X'41'","CAST(X'410062' AS TEXT)","CAST(X'610042' AS TEXT)","CAST(X'FF41' AS TEXT)","CAST(X'FF61' AS TEXT)"]
 pairs=[("'A'","'a'"),("'a'","'a '"),("'Á'","'á'"),("NULL","NULL"),("1","1.0"),("1","'1'"),("X'41'","'a'"),("CAST(X'410062' AS TEXT)","CAST(X'610042' AS TEXT)"),("CAST(X'FF41' AS TEXT)","CAST(X'FF61' AS TEXT)")]
 queries=[]
 def add(group,sql):queries.append((group,sql))
 for x,y in pairs:
  for c in ['BINARY','NOCASE','RTRIM']:
   for op in ['=','<>','<','<=','>','>=','IS','IS NOT']:
    for l,r in [(f'{x} COLLATE {c}',y),(x,f'{y} COLLATE {c}'),(f'{x} COLLATE {c}',f'{y} COLLATE BINARY')]:
     add('comparison',f'SELECT ({l}) {op} ({r});')
   for expression in [f'{x} COLLATE {c} IN ({y})',f'{x} IN ({y} COLLATE {c})',f'{x} COLLATE {c} IN ({y},NULL,\'z\')',f'{x} IN ({y} COLLATE {c},NULL,\'z\')',f'CASE {x} COLLATE {c} WHEN {y} THEN 7 ELSE 9 END',f'min({x} COLLATE {c},{y})',f'max({x},{y} COLLATE {c})',f'nullif({x} COLLATE {c},{y})']:
    add('membership-case-function',f'SELECT {expression};')
 for _ in range(a.random_cases):
  x,y=rng.choices(values,k=2);c=rng.choice(['BINARY','NOCASE','RTRIM']);d=rng.choice(['BINARY','NOCASE','RTRIM'])
  expr=rng.choice([f'({x} COLLATE {c} COLLATE {d}) = {y}',f'({x}||\'\' COLLATE {c}) = {y}',f'coalesce({x} COLLATE {c},{y}) = {y}',f'CASE {x} WHEN {y} COLLATE {c} THEN 1 ELSE 0 END',f'min(DISTINCT {x},{y} COLLATE {c},\'b\')'])
  add('random-expression',f'SELECT {expr};')
 for c in ['BINARY','NOCASE','RTRIM']:
  for col in ['v','txt','num','id']:
   for literal in ["'a'","'1'","1","NULL","X'41'"]:
    for expr in [f'{col} COLLATE {c} = {literal}',f'{col} IN ({literal} COLLATE {c},\'a\')',f'{col} IN ({literal} COLLATE {c},\'a\',\'b\')',f'nullif({col} COLLATE {c},{literal})']:
     add('row-expression',f'SELECT id,{expr} FROM t ORDER BY id;')
    add('where',f'SELECT id FROM t WHERE {col} COLLATE {c} = {literal} ORDER BY id;')
  add('distinct',f'SELECT DISTINCT v COLLATE {c} FROM t;')
  add('distinct-order',f'SELECT DISTINCT v COLLATE {c} FROM t ORDER BY v COLLATE {c};')
  add('aggregate',f'SELECT min(v COLLATE {c}),max(v COLLATE {c}),count(DISTINCT v COLLATE {c}) FROM t;')
  add('compound',f"SELECT 'A' COLLATE {c} UNION SELECT 'a';")
  add('group',f'SELECT v,count(*) FROM t GROUP BY v COLLATE {c};')
 for sql in ["SELECT min(v COLLATE NOCASE)='A',max(v COLLATE NOCASE)='b' FROM t WHERE id IN (6,7);", "SELECT nullif(min(v COLLATE NOCASE),'A'),coalesce(min(v COLLATE NOCASE),'z')='A' FROM t WHERE id IN (6,7);", "SELECT min(v COLLATE NOCASE) IN ('A'),max(v COLLATE RTRIM) IN ('a') FROM t;", "SELECT sum(id COLLATE missing),count(v COLLATE missing) FROM t;", "SELECT DISTINCT sum(id) COLLATE missing FROM t;", "SELECT DISTINCT sum(1) COLLATE missing;", "SELECT min(v COLLATE missing) FROM t LIMIT 0;", "SELECT id,v IN (txt COLLATE NOCASE),v IN (txt COLLATE missing) FROM t ORDER BY id;", "SELECT id FROM t WHERE v='a' COLLATE NOCASE ORDER BY id;", "SELECT id FROM t WHERE txt=1 COLLATE NOCASE ORDER BY id;", "SELECT 'a' COLLATE missing IS TRUE;", "SELECT CASE WHEN 1 THEN 7 ELSE 2 COLLATE NOCASE END;"]:
  add('aggregate-and-binding-edges',sql)
 unknown=["1 COLLATE missing","(1 COLLATE missing) + 2","'a' COLLATE missing = 'a'","'a' COLLATE missing COLLATE BINARY = 'a'","min('a' COLLATE missing,'b')","1 IN (1 COLLATE missing)","1 IN (1 COLLATE missing,2)","1 IN (1 COLLATE missing,2,3)","1 COLLATE missing IN ()","0 AND (1 COLLATE missing=1)","CASE WHEN 1 THEN 2 ELSE 1 COLLATE missing END","CASE WHEN 1 THEN 2 ELSE 1 COLLATE missing=1 END"]
 for e in unknown:
  for suffix in ['', ' LIMIT 0', ' FROM empty']:
   add('unknown-collation',f'SELECT {e}{suffix};')
 setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v,txt TEXT,num NUMERIC); CREATE TABLE empty(id INTEGER PRIMARY KEY);'+''.join(f'INSERT INTO t VALUES({i},{v},{v},{v});' for i,v in enumerate(values+[rng.choice(values) for _ in range(8)],1))
 failures=[];phases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-scalar-collation-') as tmp:
  for mode in ['--verified-file','--verified-wal-file']:
   folder=pathlib.Path(tmp)/mode;folder.mkdir()
   def run(sql,d=folder):
    d.mkdir(exist_ok=True);q=d/'query.sql';q.write_text(sql)
    l=subprocess.run([str(ROOT/'.lake/build/bin/sqleanite'),mode,str(d/'lean.db'),str(q)],capture_output=True,timeout=120)
    r=subprocess.run([a.sqlite,'-batch','-bail',str(d/'sqlite.db')],input=sql.encode(),capture_output=True,timeout=120)
    return l,r
   l,r=run(setup);assert l.returncode==r.returncode==0,(l.stderr,r.stderr)
   def snapshot():return {f.name:f.read_bytes() for f in folder.iterdir() if f.name in ['lean.db','sqlite.db','lean.db-wal','sqlite.db-wal']}
   before=snapshot();errors=0;counts={}
   def compare(group,sql,l,r):
    same=(l.returncode==r.returncode==0 and l.stdout==r.stdout) or (l.returncode>0 and r.returncode>0)
    if not same:
     def out(x):return dict(code=x.returncode,stdout=x.stdout.decode('latin1'),stderr=x.stderr.decode('latin1'))
     failures.append(dict(mode=mode,group=group,sql=sql,lean=out(l),sqlite=out(r)))
    return same
   for group,sql in queries:
    l,r=run(sql);same=compare(group,sql,l,r);errors+=bool(same and l.returncode);counts[group]=counts.get(group,0)+1
   assert before==snapshot(),'read queries modified database bytes'
   writes=["INSERT INTO t VALUES(99,'A' COLLATE NOCASE='a',nullif('a' COLLATE NOCASE,'A'),min('a' COLLATE RTRIM,'a '));","UPDATE t SET v=(v COLLATE NOCASE='a') WHERE txt COLLATE RTRIM='a';","DELETE FROM t WHERE v COLLATE NOCASE IN ('a','A ','b');"]
   for i,write in enumerate(writes):
    sql=setup+write+'SELECT id,v,txt,num FROM t ORDER BY id;';l,r=run(sql,folder/f'write-{i}');compare('write',sql,l,r)
   phases.append(dict(mode=mode,queries=len(queries),groups=counts,matching_errors=errors,writes=len(writes)))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,random_cases=a.random_cases,phases=phases,failures=failures,implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256((ROOT/'.lake/build/bin/sqleanite').read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(outcomes=sum(p['queries']+p['writes'] for p in phases),failures=len(failures))))
 return bool(failures)
if __name__=='__main__':raise SystemExit(main())
