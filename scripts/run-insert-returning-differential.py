#!/usr/bin/env python3
"""INSERT RETURNING public-file differential against pinned SQLite.

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
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354030);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=["INSERT INTO t VALUES(9,'x',9,NULL) RETURNING *;", "INSERT INTO t(v,u) VALUES('x',9),('y',10) RETURNING rowid,id,typeof(v),hex(v),typeof(u),hex(u);", "INSERT INTO t(v,u) VALUES('x',9) RETURNING id AS v,v;", "INSERT INTO t(v,u) VALUES('x',9) RETURNING id AS n,n;", "INSERT INTO t(v,u) VALUES('x',9) RETURNING t.id,t.v;", "INSERT INTO t(v,u) VALUES('x',9) RETURNING t.*;", "INSERT INTO t(v,u) VALUES('x',9) RETURNING missing;", "INSERT INTO t(v,u) VALUES('x',9) RETURNING no_function();", "INSERT INTO t(v,u) VALUES('x',9) RETURNING count(*);", "INSERT INTO t(v,u) VALUES('x',9) RETURNING max(id);", "INSERT INTO t(v,u) VALUES('x',9) RETURNING max(id,2);", "INSERT INTO t(v,u) VALUES('x',9) RETURNING 0 AND no_function();", "INSERT INTO t(v,u) VALUES('x',9) RETURNING 0 AND missing;", "INSERT INTO t(v,u) VALUES('x',9) RETURNING 0 AND abs();", "INSERT INTO t(v,u) VALUES('x',9) RETURNING 0 AND count(*);", "INSERT INTO t(v,u) VALUES('x',9),('y',10) RETURNING CASE WHEN u=10 THEN abs(-9223372036854775808) ELSE id END;", "INSERT OR IGNORE INTO t VALUES(1,'skip',9,NULL),(9,'keep',9,NULL),(10,'skip',9,NULL),(11,'keep',11,NULL) RETURNING *;", "INSERT OR IGNORE INTO t VALUES(1,'skip',9,NULL) RETURNING abs(-9223372036854775808);", "INSERT OR IGNORE INTO t VALUES(1,'skip',9,NULL) RETURNING missing;", "INSERT OR IGNORE INTO t(v,u) VALUES(NULL,9),('x',9) RETURNING id,v;", "INSERT OR REPLACE INTO t VALUES(1,'new',2,NULL) RETURNING *;", "INSERT OR REPLACE INTO t VALUES(9,'first',9,NULL),(9,'second',10,NULL) RETURNING id,v,u;", "INSERT OR REPLACE INTO t(v,u) VALUES('first',9),('second',9) RETURNING id,v,u;", "REPLACE INTO t VALUES(9,'first',9,NULL),(9,'second',9,NULL) RETURNING *;", 'INSERT INTO t DEFAULT VALUES RETURNING *;', 'INSERT OR IGNORE INTO t DEFAULT VALUES RETURNING *;', 'INSERT INTO implicit DEFAULT VALUES RETURNING *,rowid;', "INSERT INTO implicit(v,v) VALUES('ok',abs(-9223372036854775808)) RETURNING *,rowid;", "INSERT INTO implicit(v,v) VALUES('ok',no_function()) RETURNING *;", "INSERT INTO implicit(v,w) VALUES(CAST(X'80FF' AS TEXT),'a'||char(0)||'b') RETURNING typeof(v),hex(v),typeof(w),hex(w);", "INSERT INTO implicit(v,w) VALUES('x',zeroblob(7000)) RETURNING *,hex(w);", "INSERT INTO keyed VALUES('c',3) RETURNING *,rowid,oid,_rowid_;", "INSERT OR REPLACE INTO keyed VALUES('a',3),('a',4) RETURNING *,rowid;", "INSERT OR IGNORE INTO keyed VALUES('a',3),('c',5),(NULL,7) RETURNING *,rowid;", "INSERT INTO shadow(rowid,v) VALUES(99,'x') RETURNING *,rowid,_rowid_,oid;", "INSERT INTO t(id,v,u) VALUES(9223372036854775807,'max',9) RETURNING id,typeof(id);", "INSERT INTO t(id,v,u) VALUES(-9223372036854775808,'min',9) RETURNING id,typeof(id);", "INSERT INTO t(id,v,u) VALUES(9223372036854775808,'bad',9) RETURNING *;", "INSERT INTO t(id,v,u) VALUES(NULL,'a','9'),('10','b',10.0) RETURNING id,typeof(id),u,typeof(u);", 'INSERT OR IGNORE INTO t(v,u) SELECT v,u FROM src RETURNING id,typeof(v),hex(v),u;', 'INSERT OR REPLACE INTO t(v,u) SELECT v,u FROM src WHERE v IS NOT NULL RETURNING id,v,u;', 'INSERT INTO implicit(v,w) SELECT v,u FROM t ORDER BY id DESC RETURNING *,rowid;', 'INSERT OR IGNORE INTO t SELECT * FROM t RETURNING *;', 'INSERT INTO implicit(v,w) SELECT v,w FROM implicit RETURNING *,rowid;', "INSERT INTO t(v,u) SELECT 'a',9 UNION ALL SELECT 'b',10 RETURNING *;", "INSERT INTO t(v,u) VALUES('a',9),('b',10) UNION ALL SELECT 'c',11 RETURNING *;", 'INSERT INTO t(v,u) SELECT v,u FROM src WHERE 0 RETURNING abs(-9223372036854775808);', 'INSERT INTO t(v,u) SELECT v,u FROM src WHERE 0 RETURNING missing;', 'INSERT INTO t(v,u) SELECT v,u FROM src WHERE 0 RETURNING no_function();', 'INSERT INTO t(v,u) SELECT v FROM src WHERE 0 RETURNING *;', "BEGIN;\nINSERT INTO t(v,u) VALUES('x',9) RETURNING *;\nROLLBACK;", "BEGIN;\nINSERT INTO t(v,u) VALUES('x',9) RETURNING *;\nCOMMIT;", "BEGIN;\nINSERT INTO t(v,u) VALUES('x',9);\nINSERT INTO t(v,u) VALUES('y',10) RETURNING abs(-9223372036854775808);\nCOMMIT;"]
 queries += ['INSERT INTO implicit DEFAULT VALUES RETURNING '+','.join(['1']*n)+';' for n in [2000,2001]]
 queries += ["INSERT INTO implicit(v,w) VALUES"+','.join(f"({i},'v{i}')" for i in range(300))+" RETURNING rowid,v,w;"]
 queries += ["INSERT INTO t AS x(v,u) VALUES('x',9) RETURNING t.id,t.v;",
  "INSERT INTO t AS x(v,u) VALUES('x',9) RETURNING x.id;",
  "INSERT INTO t AS x(v,u) SELECT 'x',9 RETURNING t.id;",
  "INSERT INTO t AS t(v,u) VALUES('x',9) RETURNING t.id;",
  "INSERT INTO t AS rowid(v,u) VALUES('x',9) RETURNING rowid;",
  "INSERT INTO t AS x(v,u) VALUES(x.v,9) RETURNING id;"]
 idvalues=['NULL','-1','0','1','2','3','4','9','10',"'bad'",'1.25']
 vals=['NULL',"'a'","'b'","CAST(X'80FF' AS TEXT)","'a'||char(0)||'b'","X'00FF'",'1.5']
 uniques=['NULL','0','1','1.0',"'1'",'2','3','9',"X'31'"]
 for _ in range(a.random_cases):
  rows=[f"({rng.choice(idvalues)},{rng.choice(vals)},{rng.choice(uniques)},NULL)" for _ in range(rng.randrange(1,9))]
  projection = rng.choice(['*','id,typeof(v),hex(v),u,typeof(u)','id+1,quote(v),hex(w)','t.id,printf("%04d",u),coalesce(w,v)','rowid,oid,_rowid_'])
  policy = rng.choice(['',' OR ABORT',' OR IGNORE',' OR REPLACE'])
  queries.append('INSERT'+policy+' INTO t VALUES'+','.join(rows)+' RETURNING '+projection+';')
 with tempfile.TemporaryDirectory(prefix='sqleanite-insert-returning-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3];base=Path(tmp)/f'base{fixture}.db'
   setup=f"PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER,w);CREATE UNIQUE INDEX tu ON t(u);CREATE INDEX tv ON t(v);INSERT INTO t VALUES(1,'a',1,NULL),(2,'b',2,3.5);CREATE TABLE keyed(k TEXT PRIMARY KEY NOT NULL,v);INSERT INTO keyed VALUES('a',1),('b',2);CREATE TABLE src(v,u);CREATE TABLE implicit(v,w);INSERT INTO implicit VALUES(1,2),(NULL,3);CREATE TABLE shadow(rowid,v);"
   setup += "INSERT INTO src VALUES"+','.join('('+rng.choice(vals)+','+rng.choice(uniques)+')' for _ in range(10+fixture*7))+';'
   r=run([a.sqlite,'-batch','-bail',str(base)],setup);assert r['code']==0,r
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail',str(ref)],sql)
     same=(l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']);item=dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=same)
     observation='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(u),hex(u),typeof(w),hex(w) FROM t ORDER BY id;SELECT rowid,typeof(k),hex(k),typeof(v),hex(v) FROM keyed ORDER BY rowid;SELECT rowid,typeof(v),hex(v),typeof(u),hex(u) FROM src ORDER BY rowid;SELECT rowid,typeof(v),hex(v),typeof(w),hex(w) FROM implicit ORDER BY rowid;SELECT _rowid_,rowid,typeof(v),hex(v) FROM shadow ORDER BY _rowid_;';lo=run([a.sqlite,'-batch','-bail',str(lean)],observation);ro=run([a.sqlite,'-batch','-bail',str(ref)],observation);item.update(observed_lean=lo,observed_sqlite=ro);item['matched'] &= lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
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
