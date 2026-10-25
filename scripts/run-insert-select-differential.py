#!/usr/bin/env python3
"""INSERT SELECT: source snapshots, target affinity, conflicts and atomicity.

Compare exact SQL results and complete row storage types/bytes in all fixture
tables, including after errors. Pinned SQLite independently checks each file.
Both CLIs receive one statement per line so -bail stops at the first error.
The 3.53.4 shell can continue after a step error within a single input line.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def statement_lines(sql):
 # Retain every SQL byte and add a line boundary only after unquoted semicolons.
 result=[];quote=None;i=0
 while i<len(sql):
  c=sql[i];result.append(c)
  if quote:
   if c==quote:
    if quote!=']' and i+1<len(sql) and sql[i+1]==quote:result.append(sql[i+1]);i+=1
    else:quote=None
  elif c in "'\"`[":quote=']' if c=='[' else c
  elif c==';':result.append('\n')
  i+=1
 return ''.join(result)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=353970);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];fixtures=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=statement_lines(sql).encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 observation='PRAGMA integrity_check;'+''.join(f'SELECT rowid,typeof(v),hex(v),typeof(b),hex(b) FROM {table} ORDER BY rowid;' for table in ['src','dst','auto'])+'SELECT rowid,typeof(v),hex(v) FROM u ORDER BY rowid;'
 def observe(path):return run([a.sqlite,'-batch','-bail',str(path)],observation)
 scripts=['INSERT INTO dst SELECT id+100,v,b FROM src ORDER BY id;',
  'INSERT INTO dst(v,b) SELECT v,b FROM src ORDER BY id DESC;',
  'INSERT INTO auto SELECT v,b FROM src ORDER BY id DESC;',
  'INSERT INTO auto(rowid,v,b) SELECT id+100,v,b FROM src;',
  'INSERT INTO dst(b,v) SELECT b,v FROM src WHERE id>2 ORDER BY id LIMIT 3 OFFSET 1;',
  'INSERT INTO dst(v) SELECT sum(id) FROM src;',
  'INSERT INTO dst(v) SELECT v FROM src WHERE 0;',
  'INSERT INTO dst SELECT * FROM src WHERE 0;',
  'INSERT INTO dst SELECT id,v FROM src WHERE 0;',
  'INSERT INTO dst(v) SELECT v,b FROM src LIMIT 0;',
  'INSERT INTO dst(missing) SELECT v FROM src WHERE 0;',
  'INSERT INTO dst(v) SELECT missing FROM src LIMIT 0;',
  'INSERT INTO dst(v) SELECT no_function(id) FROM src WHERE 0;',
  'INSERT INTO dst(v) SELECT abs(-9223372036854775808) FROM src WHERE 0;',
  'INSERT INTO dst(v) SELECT abs(-9223372036854775808) FROM src;',
  'INSERT INTO dst(v) SELECT CASE WHEN id=3 THEN abs(-9223372036854775808) ELSE id END FROM src ORDER BY id;',
  'INSERT INTO dst SELECT 1,2,3;',
  'INSERT INTO dst(v) SELECT 1 UNION ALL SELECT 2 UNION ALL SELECT NULL;',
  "INSERT INTO dst(v) SELECT '1' UNION SELECT 1 UNION SELECT 1.0;",
  'INSERT INTO dst(v) SELECT count(*) FROM src GROUP BY id%3 HAVING count(*)>1 ORDER BY 1;',
  'INSERT INTO dst(v) SELECT DISTINCT v FROM src ORDER BY v;',
  'INSERT INTO dst(v) SELECT v FROM src ORDER BY id LIMIT 0 OFFSET NULL;',
  'INSERT INTO dst(v,v) SELECT id,id+1 FROM src;',
  'INSERT INTO dst(v,v) SELECT id,abs(-9223372036854775808) FROM src;',
  'INSERT INTO src(v,b) SELECT v,b FROM src ORDER BY id DESC;',
  'INSERT INTO src SELECT id+100,v,b FROM src ORDER BY id;',
  'INSERT OR REPLACE INTO src SELECT id,v,b FROM src ORDER BY id DESC;',
  'REPLACE INTO src(id,v,b) SELECT 1,v,b FROM src ORDER BY id;',
  'INSERT OR ABORT INTO dst SELECT id,v,b FROM src;',
  'INSERT INTO u(v) SELECT id%3 FROM src;',
  'INSERT OR REPLACE INTO u(v) SELECT id%3 FROM src ORDER BY id;',
  'BEGIN;INSERT INTO dst(v,b) SELECT v,b FROM src;ROLLBACK;',
  'BEGIN;INSERT INTO dst(v,b) SELECT v,b FROM src;COMMIT;',
  'INSERT INTO dst(v) SELECT 7;INSERT INTO dst(v) SELECT abs(-9223372036854775808);',
  'BEGIN;INSERT INTO dst(v) SELECT 7;INSERT INTO dst(v) SELECT abs(-9223372036854775808);COMMIT;']
 scripts += ['INSERT INTO dst SELECT * FROM src;',
  'INSERT INTO dst SELECT s.id+100,s.v,s.b FROM src AS s WHERE s.id%2=1;',
  'INSERT INTO dst(v,b) SELECT max(v),sum(id) FROM src GROUP BY id%3;',
  "INSERT INTO dst(v) SELECT printf('%g',v) FROM src ORDER BY id;",
  'INSERT INTO dst(id) SELECT v FROM src ORDER BY id;',
  'INSERT INTO auto(v) SELECT s.v FROM src AS s JOIN dst AS d ON s.id=d.id;',
  'INSERT INTO dst(v) SELECT abs(-9223372036854775808) LIMIT 0;']
 for _ in range(a.random_cases):
  value=rng.choice(['v','id','id*0.5','CAST(v AS TEXT)',"printf('%s',v)",'CASE WHEN id%2=0 THEN NULL ELSE v END','hex(b)','unistr_quote(v)'])
  condition=rng.choice(['id>2','id%2=0','v IS NULL','v IS NOT NULL','length(v)>1','id IN (1,3,7)'])
  direction=rng.choice(['ASC','DESC']);limit=rng.randrange(0,10);offset=rng.randrange(0,5)
  scripts.append(f'INSERT INTO dst(v,b) SELECT {value},b FROM src WHERE {condition} ORDER BY id {direction} LIMIT {limit} OFFSET {offset};')
 values=['NULL','0','1','-1','1.5','-0.0','1e999','9223372036854775807',"'12'","'3.25'","'word'","''","X'00FF12'","CAST(X'610062' AS TEXT)","CAST(X'80FF' AS TEXT)"]
 with tempfile.TemporaryDirectory(prefix='sqleanite-insert-select-') as tmp:
  for sample in range(a.fixtures):
   for page,affinity in [(512,''),(4096,'TEXT'),(4096,'NUMERIC'),(65536,'REAL')]:
    folder=Path(tmp)/f'{sample}-{page}-{affinity}';folder.mkdir();base=folder/'base.db';count=rng.randrange(6,16)
    setup=f'PRAGMA page_size={page};CREATE TABLE src(id INTEGER PRIMARY KEY,v,b);CREATE TABLE dst(id INTEGER PRIMARY KEY,v {affinity},b BLOB);CREATE INDEX dst_v ON dst(v);CREATE TABLE auto(v {affinity},b);CREATE TABLE u(id INTEGER PRIMARY KEY,v);CREATE UNIQUE INDEX uv ON u(v);BEGIN;'
    for i in range(1,count+1):setup+=f"INSERT INTO src VALUES({i},{rng.choice(values)},X'{bytes(rng.randrange(256) for _ in range(rng.randrange(0,9))).hex()}');"
    r=run([a.sqlite,'-batch','-bail',str(base)],setup+'COMMIT;');assert r['code']==0,r;fixtures.append(dict(sample=sample,page_size=page,affinity=affinity,rows=count))
    for mode in ['--verified-file','--verified-wal-file']:
     for sql in scripts:
      dest=folder/str(len(cases));dest.mkdir();lean=dest/'lean.db';ref=dest/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref)
      l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail',str(ref)],sql);lo=observe(lean);ro=observe(ref)
      same=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
      cases.append(dict(sample=sample,page_size=page,affinity=affinity,mode=mode,sql=sql,sql_input=statement_lines(sql),lean=l,sqlite=r,matched=same,observed_lean=lo,observed_sqlite=ro))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=fixtures,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
