#!/usr/bin/env python3
"""INSERT OR IGNORE public-file differential against pinned SQLite.

Compare successful output bytes, positive errors, and independently observed
stored rows, storage classes, and integrity after every script. Failed single
statements must retain main/WAL bytes. Large successful captures are stored
as byte counts, SHA-256 and previews after full-byte comparison. Failures keep
full captures. This is not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354000);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=["INSERT OR IGNORE INTO t VALUES(1,'new',9,NULL);",
  "INSERT OR IGNORE INTO t VALUES(9,'new',1,NULL);",
  "INSERT OR IGNORE INTO t VALUES(9,NULL,9,NULL);",
  "INSERT OR IGNORE INTO t(id,v,u) VALUES('bad',NULL,9);",
  "INSERT OR IGNORE INTO t(id,v,u) VALUES(1.5,'x',9);",
  "INSERT OR IGNORE INTO t(v,u) VALUES('new',NULL),('next',NULL);",
  "INSERT OR IGNORE INTO t(id,v,u) VALUES(1,'skip',7),(9,'keep',9),(10,'skip',9),(11,'keep',11);",
  "INSERT OR IGNORE INTO t(v,u) VALUES(NULL,9),('new',10);",
  "INSERT OR IGNORE INTO t DEFAULT VALUES;",
  "INSERT OR IGNORE INTO t(id,v,u) VALUES(1,abs(-9223372036854775808),9);",
  "INSERT OR IGNORE INTO t(id,v,u) VALUES(1,'skip',9),(9,abs(-9223372036854775808),10);",
  "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',abs(-9223372036854775808),9);",
  "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',no_function(),9);",
  "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',missing,9);",
  "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',abs(),9);",
  "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',0 AND no_function(),9);",
  "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',0 AND missing,9);",
  "INSERT OR IGNORE INTO t(v,v,u) VALUES('ok',sum(1),9);",
  "INSERT INTO t(v,v,u) VALUES('ok',no_function(),9);",
  "INSERT INTO t(v,v,u) VALUES('ok',abs(-9223372036854775808),9);",
  "INSERT INTO t(v,v,u) VALUES('ok',0 AND missing,9);",
  "INSERT OR IGNORE INTO t(id,v,u) VALUES(9223372036854775807,'max',9);",
  "INSERT OR IGNORE INTO t(id,v,u) VALUES(-9223372036854775808,'min',9);",
  "INSERT OR IGNORE INTO t(id,v,u) VALUES(9223372036854775808,'overflow',9);",
  "INSERT OR IGNORE INTO t(v,u) SELECT v,u FROM src;",
  "INSERT OR IGNORE INTO t SELECT * FROM t;",
  "INSERT OR IGNORE INTO t(v,u) SELECT v,u FROM t ORDER BY id DESC;",
  "INSERT OR IGNORE INTO t(v,u) SELECT 'a',9 UNION ALL SELECT 'b',9 UNION ALL SELECT 'c',10;",
  "INSERT OR IGNORE INTO t(v,u) VALUES('a',9),('b',9) UNION ALL SELECT 'c',10;",
  "INSERT OR IGNORE INTO t(v,u) SELECT v FROM src WHERE 0;",
  "INSERT OR IGNORE INTO t(missing) SELECT v FROM src WHERE 0;",
  "INSERT OR IGNORE INTO t(v,u) VALUES('x');",
  "INSERT OR IGNORE INTO t VALUES(9,'x',9,NULL,0);",
  "INSERT OR IGNORE INTO keyed VALUES('a',3),('c',5),('a',6),(NULL,7);",
  "INSERT OR IGNORE INTO t(v,u) VALUES(CAST(X'80FF' AS TEXT),9);",
  "INSERT OR IGNORE INTO t(id,v,u) VALUES(9,'a',1.0),(10,'b','2'),(11,'c',X'31');",
  "BEGIN;\nINSERT OR IGNORE INTO t(v,u) VALUES('new',9),('skip',9);\nROLLBACK;",
  "BEGIN;\nINSERT OR IGNORE INTO t(v,u) VALUES('new',9),('skip',9);\nCOMMIT;",
  "BEGIN;\nINSERT INTO t(v,u) VALUES('new',9);\nINSERT OR IGNORE INTO t(v,u) VALUES(abs(-9223372036854775808),1);\nCOMMIT;"]
 idvalues=['NULL','-1','0','1','2','3','4','9','10',"'bad'",'1.25']
 vals=['NULL',"'a'","'b'","CAST(X'80FF' AS TEXT)","'a'||char(0)||'b'","X'00FF'",'1.5']
 uniques=['NULL','0','1','1.0',"'1'",'2','3','9',"X'31'"]
 for _ in range(a.random_cases):
  rows=[f"({rng.choice(idvalues)},{rng.choice(vals)},{rng.choice(uniques)},NULL)" for _ in range(rng.randrange(1,9))]
  queries.append('INSERT OR IGNORE INTO t VALUES'+','.join(rows)+';')
 with tempfile.TemporaryDirectory(prefix='sqleanite-ignore-insert-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3];base=Path(tmp)/f'base{fixture}.db'
   setup=f"PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER,w);CREATE UNIQUE INDEX tu ON t(u);CREATE INDEX tv ON t(v);INSERT INTO t VALUES(1,'a',1,NULL),(2,'b',2,3.5);CREATE TABLE keyed(k TEXT PRIMARY KEY NOT NULL,v);INSERT INTO keyed VALUES('a',1),('b',2);CREATE TABLE src(v,u);"
   setup += "INSERT INTO src VALUES"+','.join('('+rng.choice(vals)+','+rng.choice(uniques)+')' for _ in range(10+fixture*7))+';'
   r=run([a.sqlite,'-batch','-bail',str(base)],setup);assert r['code']==0,r
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail',str(ref)],sql)
     same=(l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']);item=dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=same)
     observation='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(u),hex(u),typeof(w),hex(w) FROM t ORDER BY id;SELECT rowid,typeof(k),hex(k),typeof(v),hex(v) FROM keyed ORDER BY rowid;SELECT rowid,typeof(v),hex(v),typeof(u),hex(u) FROM src ORDER BY rowid;';lo=run([a.sqlite,'-batch','-bail',str(lean)],observation);ro=run([a.sqlite,'-batch','-bail',str(ref)],observation);item.update(observed_lean=lo,observed_sqlite=ro);item['matched'] &= lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     if r['code'] and '\n' not in sql:item['failed_statement_bytes_unchanged']=before==hashes(lean);item['matched'] &= item['failed_statement_bytes_unchanged']
     if item['matched']:
      for key in ['lean','sqlite','observed_lean','observed_sqlite']:
       value=item[key];raw=value['stdout'].encode('latin1')
       if len(raw)>4096:
        value.update(stdout_bytes=len(raw),stdout_sha256=hashlib.sha256(raw).hexdigest(),stdout_prefix=raw[:128].decode('latin1'),stdout_suffix=raw[-128:].decode('latin1'));del value['stdout']
     cases.append(item)
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
