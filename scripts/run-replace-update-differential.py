#!/usr/bin/env python3
"""UPDATE OR REPLACE and key-update public-file differential against pinned SQLite.

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
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354020);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=["UPDATE OR REPLACE t SET u=100 WHERE v='a' OR v='c';",
  "UPDATE OR REPLACE t SET u=100 WHERE v>'a' OR v<'c';",
  "UPDATE OR REPLACE t SET u=100 WHERE v>='a' AND v<='c';",
  "UPDATE OR REPLACE t SET u=100 WHERE v IN ('a','c');",
  "UPDATE OR REPLACE t SET u=100 WHERE w>0;",
  "UPDATE OR REPLACE t SET u=1;", "UPDATE OR REPLACE t SET u=NULL;",
  "UPDATE OR REPLACE t SET v=NULL;", "UPDATE OR REPLACE t SET u=u+1;",
  "UPDATE OR REPLACE t SET u=u-1;", "UPDATE OR REPLACE t SET id=id+1;",
  "UPDATE OR REPLACE t SET id=id-1;", "UPDATE OR REPLACE t SET id=-id,u=u+10;",
  "UPDATE OR REPLACE t SET id=NULL;", "UPDATE OR REPLACE t SET id='bad',v=NULL;",
  "UPDATE OR REPLACE t SET v=NULL,w=abs(-9223372036854775808);",
  "UPDATE OR REPLACE t SET u=CASE WHEN id<4 THEN 100 ELSE 1 END;",
  "UPDATE OR REPLACE t SET u=9,w=1.5;", "UPDATE OR REPLACE t SET u=u+10,w=u;",
  "UPDATE OR REPLACE t SET u=abs(-9223372036854775808) WHERE id=1;",
  "UPDATE OR REPLACE t SET u=CASE WHEN id=7 THEN abs(-9223372036854775808) ELSE u+10 END;",
  "UPDATE OR REPLACE t SET u=abs(-9223372036854775808),u=9;",
  "UPDATE OR REPLACE t SET u=no_function(),u=9;",
  "UPDATE OR REPLACE t SET u=missing,u=9;",
  "UPDATE OR REPLACE t SET u=u+1,u=u+2;",
  "UPDATE OR REPLACE t AS x SET u=x.u+10 WHERE x.id<4;",
  "UPDATE OR REPLACE t AS x SET u=t.u+10 WHERE x.id<4;",
  "UPDATE OR REPLACE keyed SET k='a';", "UPDATE OR REPLACE keyed SET k=k||'x';",
  "UPDATE OR REPLACE keyed SET k=NULL;", "UPDATE OR REPLACE keyed SET rowid=rowid+10,k=k||'x';",
  "UPDATE keyed SET k=k||'x';", "UPDATE keyed SET k='a';",
  "UPDATE OR REPLACE t SET u=9 WHERE 0;", "UPDATE OR REPLACE t SET u=abs(-9223372036854775808) WHERE 0;",
  "UPDATE OR REPLACE t SET missing=1 WHERE 0;",
  "BEGIN;\nUPDATE OR REPLACE t SET u=1;\nROLLBACK;",
  "BEGIN;\nUPDATE OR REPLACE t SET u=1;\nCOMMIT;",
  "BEGIN;\nINSERT INTO t VALUES(999,'new',999,NULL);\nUPDATE OR REPLACE t SET u=abs(-9223372036854775808);\nCOMMIT;"]
 queries += [
  "UPDATE OR REPLACE t SET u=1,w=CASE WHEN id=7 THEN abs(-9223372036854775808) ELSE w END;",
  "UPDATE OR REPLACE t SET id=id+1,v=v||'x';",
  "UPDATE OR REPLACE t SET id=id+1,v=v||'x' WHERE id<4;",
  "UPDATE OR REPLACE t SET id=id+2,u=100;",
  "UPDATE OR REPLACE t SET u=100 WHERE id<4;",
  "UPDATE OR REPLACE t SET u=100 WHERE v>='a';",
  "UPDATE OR REPLACE t SET u=100 WHERE likely(v>'a');",
  "UPDATE OR REPLACE t SET id=CASE WHEN id=1 THEN 7 ELSE id END,w=CASE WHEN id=7 THEN abs(-9223372036854775808) ELSE w END;",
  "UPDATE OR REPLACE t SET u=CASE WHEN id=1 THEN 7 ELSE u END,v=CASE WHEN id=7 THEN NULL ELSE v END;",
  "UPDATE OR REPLACE keyed SET k='same',v=v+1;",
  "UPDATE OR REPLACE keyed SET rowid=rowid+1,v=v+1;",
  "UPDATE OR REPLACE t SET u=100 WHERE CASE WHEN id=7 THEN abs(-9223372036854775808) ELSE 1 END;",
  "UPDATE OR REPLACE t SET id=9223372036854775807 WHERE id=7;",
  "UPDATE OR REPLACE t SET id=-9223372036854775808 WHERE id=7;",
  "UPDATE OR REPLACE t SET id=id+9223372036854775807 WHERE id=7;"]
 assignments=['u=1' ,'u=NULL','u=u+1','u=u-1','u=id%3','v=NULL',"v='x'","v=CAST(X'80FF' AS TEXT)",'id=id+1','id=id-1','id=-id','id=NULL',"id='bad'",'u=u+10,w=u','w=u+0.5','u=u+2,u=u+3','v=CASE WHEN id%2=0 THEN NULL ELSE v END']
 predicates=['1','0','id<4','id>3','id IN (1,3,7)','id%2=0','u<5','u IN (1,2,3,4)','w IS NULL',"v='a'","v IN ('a','c')","v>='a' AND v<='c'",'u>=1 AND u<=7',"v='a' OR v='c'","v>'a' OR v<'c'"]
 vals=['NULL',"'a'","'b'",'1.5'];uniques=['NULL','0','1','2','9']
 for _ in range(a.random_cases):queries.append('UPDATE OR REPLACE t SET '+rng.choice(assignments)+' WHERE '+rng.choice(predicates)+';')
 with tempfile.TemporaryDirectory(prefix='sqleanite-replace-update-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3];base=Path(tmp)/f'base{fixture}.db'
   setup=f"PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER,w);CREATE UNIQUE INDEX tu ON t(u);CREATE INDEX tv ON t(v);CREATE UNIQUE INDEX tw ON t(w);CREATE TABLE keyed(k TEXT PRIMARY KEY NOT NULL,v);INSERT INTO keyed VALUES('a',1),('b',2);CREATE TABLE src(v,u);"
   order=list(range(1,8));rng.shuffle(order)
   setup += "INSERT INTO t VALUES"+','.join(f"({i},'{rng.choice(['a','b','c'])}',{u},{'NULL' if i%3==0 else str(u+0.5)})" for i,u in enumerate(order,1))+';'
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
