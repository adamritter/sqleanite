#!/usr/bin/env python3
"""Diagnostic inventory of UPDATE access-plan differences against pinned SQLite.

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
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354010);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=["UPDATE OR IGNORE t SET u=100 WHERE v>='a' AND u>0;",
  "UPDATE OR IGNORE t SET u=100 WHERE v>='a' AND w>0;",
  "UPDATE OR IGNORE t SET w=100 WHERE v>='a' AND u>0;",
  "UPDATE OR IGNORE t SET u=100 WHERE v BETWEEN 'a' AND 'z' AND u=2;",
  "UPDATE OR IGNORE t SET u=100 WHERE (v='a4' OR v='a7') AND u>0;",
  "UPDATE OR IGNORE t SET u=100 WHERE v>='a' AND (u>2 OR w>0);",
  "UPDATE OR IGNORE t SET u=100 WHERE v GLOB 'a*';",
  "UPDATE OR IGNORE t SET u=100 WHERE v IS NOT NULL;",
  "UPDATE OR IGNORE t SET w=100 WHERE u IS NOT NULL;",
  "UPDATE OR IGNORE t SET u=100 WHERE w IS NOT NULL;",
  "UPDATE OR IGNORE t SET u=100 WHERE likely(v>'a');",
  "UPDATE OR IGNORE t SET u=100 WHERE unlikely(v>'a');",
  "UPDATE OR IGNORE t SET u=100 WHERE +v>='a';",
  "UPDATE OR IGNORE t SET u=100 WHERE v COLLATE nocase>='a';",
  "UPDATE OR IGNORE t SET u=100 WHERE v='a4' OR v='a7';"]
 vals=['NULL',"'a'","'b'",'1.5'];uniques=['NULL','0','1','2','9']
 with tempfile.TemporaryDirectory(prefix='sqleanite-ignore-update-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3];base=Path(tmp)/f'base{fixture}.db'
   setup=f"PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT NOT NULL,u INTEGER,w);CREATE UNIQUE INDEX tu ON t(u);CREATE INDEX tv ON t(v);CREATE UNIQUE INDEX tw ON t(w);CREATE TABLE keyed(k TEXT PRIMARY KEY NOT NULL,v);INSERT INTO keyed VALUES('a',1),('b',2);CREATE TABLE src(v,u);"
   order=list(range(1,8));rng.shuffle(order)
   setup += "INSERT INTO t VALUES"+','.join(f"({i},'{'a'+str(8-i) if i<5 else 'b'+str(8-i)}',{u},{'NULL' if i%3==0 else str(u+0.5)})" for i,u in enumerate(order,1))+';'
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
