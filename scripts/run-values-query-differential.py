#!/usr/bin/env python3
"""Standalone/compound VALUES and INSERT from VALUES compounds.

Successful reads compare exact bytes; errors compare positive exit status.
All successful or failed writes are independently observed with pinned SQLite.
Read-only calls must retain the main/WAL byte images. No global coverage claim.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=353980);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=['VALUES(1);','VALUES(1),(2),(3);',"VALUES(1,'a'),(NULL,'b'),(2.0,X'00FF');",
  'VALUES();','VALUES(1),(2,3);','VALUES(1,2),(3);','VALUES(1) ORDER BY 1;',
  'VALUES(1) LIMIT 0;','VALUES(1) LIMIT -1;','VALUES(1) OFFSET 1;',
  'VALUES(missing);','VALUES(sum(1));','VALUES(abs(-9223372036854775808));',
  'VALUES(1),(abs(-9223372036854775808));','VALUES(abs(-9223372036854775808)),(missing);',
  'VALUES(NULL),(0),(1),(1.0),(TRUE),(FALSE);',
  'VALUES(1) UNION ALL SELECT 2 ORDER BY column1 DESC;',
  'VALUES(1),(2) UNION ALL SELECT 3 LIMIT 2 OFFSET 1;',
  'SELECT 1 UNION ALL VALUES(2),(3);','SELECT 1 UNION ALL VALUES(2),(3) LIMIT 1;',
  'VALUES(1),(2) UNION VALUES(2),(3);','VALUES(1),(2) INTERSECT SELECT 2;',
  'VALUES(1),(1),(2) EXCEPT VALUES(1);',
  'VALUES(1),(2) UNION SELECT 3 ORDER BY 1 DESC LIMIT 2;',
  'VALUES(1),(2) UNION SELECT 3 ORDER BY column1 DESC;',
  "VALUES('a'),('b' COLLATE nocase) UNION SELECT 'A';",
  "VALUES('a' COLLATE nocase),('b') UNION SELECT 'A';",
  "VALUES('a' COLLATE nocase),('A' COLLATE missing) UNION SELECT 'a';",
  "VALUES('a' COLLATE missing),('b') UNION SELECT 'A';",
  'VALUES(1),(2) UNION ALL SELECT id FROM src ORDER BY column1 DESC;',
  'VALUES(1),(2) UNION ALL SELECT id FROM src ORDER BY column1 DESC LIMIT 3 OFFSET 2;',
  'VALUES(1),(2) UNION ALL SELECT 3 ORDER BY 2;',
  'VALUES(1),(2) UNION ALL SELECT 3 ORDER BY 1+0;',
  'VALUES(1),(2) UNION ALL SELECT 3 LIMIT 0 OFFSET NULL;',
  'VALUES(1),(2) UNION ALL SELECT 3 LIMIT 2 OFFSET 1;',
  'SELECT 1,2 UNION ALL VALUES(3,4),(5,6);']
 queries += ['VALUES(sum(1),count(*));','VALUES(sum(1)),(2);','VALUES(1),(sum(2));',
  'VALUES(sum(1)) UNION ALL VALUES(sum(2));','VALUES(sum(1)) UNION ALL SELECT 3 ORDER BY 1 DESC;',
  'VALUES(sum(abs(-9223372036854775808))) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;',
  'VALUES(abs(-9223372036854775808)) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;',
  'VALUES(abs(-9223372036854775808)),(2) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;',
  'VALUES(1),(abs(-9223372036854775808)) UNION ALL SELECT 3 LIMIT 1;',
  'VALUES(1),(abs(-9223372036854775808)) UNION ALL SELECT 3 ORDER BY 1 LIMIT 1;',
  'VALUES(1,1),(2,abs(-9223372036854775808)) UNION ALL SELECT 3,3 ORDER BY 1 LIMIT 1;',
  'VALUES(abs(-9223372036854775808)),(2) UNION ALL SELECT 3 LIMIT 0;',
  'VALUES(1,1),(2,abs(-9223372036854775808)) UNION ALL SELECT 3,3 ORDER BY 1 LIMIT 0;',
  'VALUES'+','.join('('+str(i)+')' for i in range(1001))+';',
  'VALUES('+','.join('1' for _ in range(2000))+');',
  'VALUES('+','.join('1' for _ in range(2001))+');']
 # Parse-time lowering: affinity-bearing prefixes, coroutine column names,
 # right-arm subqueries, and OFFSET expression evaluation are independently visible.
 for prefix in ["'a'","CAST('a' AS TEXT)","+CAST('a' AS TEXT)","likely(CAST('a' AS TEXT))"]:
  for suffix in ["('b' COLLATE nocase)","('b'),('c' COLLATE nocase)","(CAST('b' AS TEXT)),('c' COLLATE nocase)"]:
   for q in [f"VALUES({prefix}),{suffix} UNION SELECT 'A';",f"SELECT 'A' UNION VALUES({prefix}),{suffix};",f"VALUES({prefix}),{suffix} UNION ALL SELECT 'A' ORDER BY column1;",f"VALUES({prefix}),{suffix} UNION ALL SELECT 'A' ORDER BY {prefix};"]:queries.append(q)
 queries += ["VALUES(1+2),(4) UNION ALL SELECT 5 ORDER BY 1+2;",
  "VALUES(CAST(1 AS TEXT)),(2+1),(4) UNION ALL SELECT 5 ORDER BY 2+1;",
  "VALUES(CAST('a' AS TEXT)),('b' COLLATE nocase) UNION ALL SELECT 'A' ORDER BY 'b' COLLATE nocase;",
  "VALUES(CAST(abs(-9223372036854775808) AS TEXT)),(2) UNION ALL SELECT 3 LIMIT 1 OFFSET 1;",
  "VALUES(CAST(1 AS TEXT)),(abs(-9223372036854775808)),(3) UNION ALL SELECT 4 LIMIT 1 OFFSET 2;",
  "VALUES(CAST(1 AS TEXT)),(CAST(abs(-9223372036854775808) AS TEXT)),(3) UNION ALL SELECT 4 LIMIT 1 OFFSET 2;",
  "SELECT 9 UNION ALL VALUES(CAST(abs(-9223372036854775808) AS TEXT)),(2) UNION ALL SELECT 3 LIMIT 1 OFFSET 2;"]
 vals=['NULL','-1','0','1','1.0','-0.0','1e999',"'a'","'A' COLLATE nocase","X'00FF'","CAST(X'610062' AS TEXT)","CAST(X'80FF' AS TEXT)","unistr('a\\u00e9')","printf('%g',1.25)"]
 vals += ["CAST('a' AS TEXT)","CAST('A' AS TEXT) COLLATE nocase","+CAST('a' AS TEXT)","'b ' COLLATE rtrim","0 COLLATE nocase"]
 for _ in range(a.random_cases):
  width=rng.randrange(1,5);rows=['('+','.join(rng.choice(vals) for _ in range(width))+')' for _ in range(rng.randrange(1,12))];q='VALUES'+','.join(rows)
  if rng.randrange(2):
   q+=' '+rng.choice(['UNION ALL','UNION','INTERSECT','EXCEPT'])+' SELECT '+','.join(rng.choice(vals) for _ in range(width))
   if rng.randrange(2):q+=f' ORDER BY {rng.randrange(1,width+1)} '+rng.choice(['ASC','DESC'])+f' LIMIT {rng.randrange(0,10)} OFFSET {rng.randrange(0,5)}'
  queries.append(q+';')
 writes=["INSERT INTO out(v,w) VALUES(1,'a'),(2,'b') UNION ALL SELECT 3,'c';",
  "INSERT INTO out(v,w) VALUES(1,'a'),(2,'b') UNION SELECT 2,'b';",
  "INSERT INTO out(v,w) SELECT 1,'a' UNION ALL VALUES(2,'b'),(3,'c');",
  'INSERT INTO out(v) VALUES(1),(2) EXCEPT SELECT 1;',
  'INSERT INTO out(v) VALUES(1),(2) UNION ALL SELECT 3 ORDER BY column1 DESC LIMIT 2;',
  'INSERT INTO out(v) VALUES(CAST(X\'80FF\' AS TEXT)),(NULL) UNION ALL SELECT 1.5;',
  'INSERT INTO out(v,w) VALUES(1),(2) UNION ALL SELECT 3;',
  'INSERT INTO out(v,w) VALUES(1,2),(3) UNION ALL SELECT 4,5;']
 with tempfile.TemporaryDirectory(prefix='sqleanite-values-') as tmp:
  base=Path(tmp)/'base.db';setup='CREATE TABLE src(id INTEGER PRIMARY KEY,v);INSERT INTO src VALUES(1,7),(2,8),(3,9);CREATE TABLE out(id INTEGER PRIMARY KEY,v,w);';r=run([a.sqlite,'-batch','-bail',str(base)],setup);assert r['code']==0,r
  for mode in ['--verified-file','--verified-wal-file']:
   for operation,sql in [('read',q) for q in queries]+[('write',q) for q in writes]:
    folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
    l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail',str(ref)],sql);same=(l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']);item=dict(mode=mode,operation=operation,sql=sql,lean=l,sqlite=r,matched=same)
    if operation=='read':item['bytes_unchanged']=before==hashes(lean);item['matched'] &= item['bytes_unchanged']
    else:
     observation='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(w),hex(w) FROM out ORDER BY id;';lo=run([a.sqlite,'-batch','-bail',str(lean)],observation);ro=run([a.sqlite,'-batch','-bail',str(ref)],observation);item.update(observed_lean=lo,observed_sqlite=ro);item['matched'] &= lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
    cases.append(item)
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
