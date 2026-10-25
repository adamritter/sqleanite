#!/usr/bin/env python3
"""INSERT duplicate-target expression evaluation public-file differential against pinned SQLite.

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
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354080);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=[
  "INSERT INTO t(v,v) VALUES('kept',abs(-9223372036854775808));",
  "INSERT INTO t(v,v) VALUES('kept',abs(-9223372036854775808)),('second',1);",
  "INSERT INTO t(v,v) VALUES('first',1),('kept',abs(-9223372036854775808));",
  "INSERT INTO t(id,id,v) VALUES(abs(-9223372036854775808),10,'kept');",
  "INSERT INTO t(id,id,v) VALUES(abs(-9223372036854775808),10,'first'),(11,12,'second');",
  "INSERT INTO t(rowid,id,v) VALUES(NULL,10,'first'),(abs(-9223372036854775808),11,'second');",
  "INSERT INTO t(v,v) SELECT 'kept',abs(-9223372036854775808);",
  "INSERT INTO t(v,v) SELECT 'kept',abs(-9223372036854775808) WHERE 0;",
  "INSERT INTO t(v,v) SELECT 'kept',no_function() WHERE 0;",
  "INSERT INTO t(v,v) VALUES('kept',no_function()),('second',1);",
  "INSERT INTO t(v,v) VALUES('kept',missing),('second',1);",
  "INSERT OR IGNORE INTO t(id,v,v) VALUES(1,'kept',abs(-9223372036854775808)),(10,'second',1);",
  "INSERT OR REPLACE INTO t(id,v,v) VALUES(1,'kept',abs(-9223372036854775808)),(10,'second',1);",
  "INSERT INTO t(v,v) VALUES('first','unused'),('second','unused') RETURNING id,v;",
  "INSERT INTO t(v,v) VALUES('kept',abs(-9223372036854775808)),('second',1) RETURNING id,v;",
  "INSERT OR IGNORE INTO t(id,id,v) VALUES(abs(-9223372036854775808),1,'first'),(1,10,'second') RETURNING id,v;",
  "INSERT INTO keyed(k,k,v) VALUES('first',abs(-9223372036854775808),1);",
  "INSERT INTO keyed(k,k,v) VALUES('first',abs(-9223372036854775808),1),('second','unused',2);",
  "INSERT INTO implicit(rowid,_rowid_,v) VALUES(abs(-9223372036854775808),10,'first');",
  "INSERT INTO implicit(rowid,_rowid_,v) VALUES(abs(-9223372036854775808),10,'first'),(11,12,'second');",
  "INSERT INTO shadow(rowid,_rowid_,v) VALUES(11,12,'first'),(13,14,'second') RETURNING rowid,_rowid_,v;",
  "INSERT INTO t(v,v) VALUES('first',1),('second',CASE WHEN 1 THEN abs(-9223372036854775808) ELSE 0 END);",
  "INSERT INTO t(v,v) VALUES('first',0 AND abs(-9223372036854775808)),('second',0) RETURNING id,v;",
  "BEGIN;\nINSERT INTO t(v,v) VALUES('first','unused'),('second','unused') RETURNING id,v;\nROLLBACK;"]
 queries += ["INSERT INTO t(v,v) VALUES(CAST(X'80FF' AS TEXT),X'00'),(CAST(X'610062' AS TEXT),NULL) RETURNING id,typeof(v),hex(v);",
  "INSERT INTO t(v,v,w) VALUES('first','discarded',zeroblob(7000)),('second','discarded',zeroblob(8500)) RETURNING id,hex(v),length(w);",
  "INSERT OR IGNORE INTO t(id,v,v) VALUES(1,'first',0),(2,'second',abs(-9223372036854775808));",
  "INSERT INTO implicit(v,v) VALUES('first',0),('second',abs(-9223372036854775808));"]
 discarded=['0','NULL',"'unused'",'abs(-9223372036854775808)','no_function()','0 AND abs(-9223372036854775808)','CASE WHEN 0 THEN 0 ELSE abs(-9223372036854775808) END']
 for _ in range(a.random_cases):
  policy=rng.choice(['',' OR ABORT',' OR IGNORE',' OR REPLACE']);count=rng.randrange(1,6)
  if rng.randrange(2):
   cols='id,id,v';rows=[f"({rng.choice(discarded)},{rng.choice([1,2,10,11,12])},'v{i}')" for i in range(count)]
  else:
   cols='id,v,v';rows=[f"({rng.choice([1,2,10,11,12])},'v{i}',{rng.choice(discarded)})" for i in range(count)]
  queries.append('INSERT'+policy+' INTO t('+cols+') VALUES'+','.join(rows)+rng.choice(['',' RETURNING id,v'])+';')
 with tempfile.TemporaryDirectory(prefix='sqleanite-insert-input-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3];base=Path(tmp)/f'base{fixture}.db'
   setup=f"PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER,w);CREATE UNIQUE INDEX tu ON t(u);CREATE TABLE keyed(k TEXT PRIMARY KEY,v);CREATE TABLE implicit(v);CREATE TABLE shadow(rowid INTEGER,v);"
   setup += f"INSERT INTO t VALUES(1,'fixture-{rng.getrandbits(48):012x}',1,NULL),(2,'fixture-{rng.getrandbits(48):012x}',2,NULL);"
   setup += "INSERT INTO keyed VALUES('a',1),('b',2);INSERT INTO implicit VALUES('a'),('b');INSERT INTO shadow VALUES(1,'a'),(2,'b');"
   r=run([a.sqlite,'-batch','-bail',str(base)],setup);assert r['code']==0,r
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail',str(ref)],sql)
     same=(l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']);item=dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=same)
     observation='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(u),hex(u),typeof(w),hex(w) FROM t ORDER BY id;SELECT rowid,typeof(k),hex(k),typeof(v),hex(v) FROM keyed ORDER BY rowid;SELECT rowid,typeof(v),hex(v) FROM implicit ORDER BY rowid;SELECT _rowid_,rowid,typeof(v),hex(v) FROM shadow ORDER BY _rowid_;';lo=run([a.sqlite,'-batch','-bail',str(lean)],observation);ro=run([a.sqlite,'-batch','-bail',str(ref)],observation);item.update(observed_lean=lo,observed_sqlite=ro);item['matched'] &= lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
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
