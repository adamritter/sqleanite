#!/usr/bin/env python3
"""Mutated foreign B-tree pointer-order and overflow public-file differential against pinned SQLite.

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
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354065);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=["SELECT rowid,typeof(k),hex(k),typeof(v),hex(v),u FROM keyed ORDER BY rowid;",
  "SELECT rowid,hex(k) FROM keyed WHERE k IS NULL ORDER BY rowid;",
  "SELECT rowid,hex(k) FROM keyed WHERE k>='m' ORDER BY k,rowid LIMIT 7;",
  "SELECT rowid,hex(k) FROM keyed ORDER BY k,rowid DESC LIMIT 20;",
  "UPDATE keyed SET v=zeroblob(6500) WHERE rowid%13=0 RETURNING rowid,hex(k);",
  "DELETE FROM keyed WHERE rowid%9=0 RETURNING rowid,hex(k);",
  "INSERT OR REPLACE INTO keyed VALUES('a',X'CAFE',NULL),(NULL,X'FF',NULL) RETURNING rowid,hex(k),hex(v);"]
 with tempfile.TemporaryDirectory(prefix='sqleanite-pointer-layout-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3];base=Path(tmp)/f'base{fixture}.db'
   not_null = False
   with_nulls = True
   unique_values=rng.sample(range(1,20),4)
   payloads=[f"fixture{fixture}-{rng.getrandbits(48):012x}" for _ in range(4)]
   setup=f"PRAGMA page_size={page};CREATE TABLE keyed(k TEXT PRIMARY KEY{' NOT NULL' if not_null else ''},v,u INTEGER);INSERT INTO keyed VALUES('a','{payloads[0]}',{unique_values[0]}),('b','{payloads[1]}',{unique_values[1]});"
   if with_nulls:setup += f"INSERT INTO keyed VALUES(NULL,'{payloads[2]}',{unique_values[2]}),(NULL,'{payloads[3]}',{unique_values[3]});"
   order=list(range(90+fixture*5));rng.shuffle(order)
   for i in order:
    key=rng.choice(['c','m','z'])+f"{i:05d}-"+rng.choice(['a','t','x'])*rng.choice([12,60,500,1600])
    setup+=f"INSERT INTO keyed VALUES('{key}',zeroblob({rng.choice([0,80,900,7000])}),{100+i});"
   setup += "CREATE UNIQUE INDEX ku ON keyed(u);UPDATE keyed SET k=k||'changed' WHERE rowid%11=0;DELETE FROM keyed WHERE rowid%7=0;"
   setup += "INSERT INTO keyed VALUES(NULL,'last-null',NULL);"

   r=run([a.sqlite,'-batch','-bail',str(base)],setup);assert r['code']==0,r
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail',str(ref)],sql)
     same=(l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']);item=dict(fixture=fixture,page_size=page,not_null=not_null,initial_nulls=with_nulls,initial_unique_values=unique_values,initial_payloads=payloads,mode=mode,sql=sql,lean=l,sqlite=r,matched=same)
     observation='PRAGMA integrity_check;PRAGMA table_info(keyed);PRAGMA index_list(keyed);SELECT rowid,typeof(k),hex(k),typeof(v),hex(v),typeof(u),hex(u) FROM keyed ORDER BY rowid;';lo=run([a.sqlite,'-batch','-bail',str(lean)],observation);ro=run([a.sqlite,'-batch','-bail',str(ref)],observation);item.update(observed_lean=lo,observed_sqlite=ro);item['matched'] &= lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     if r['code'] and '\n' not in sql:item['failed_statement_bytes_unchanged']=before==hashes(lean);item['matched'] &= item['failed_statement_bytes_unchanged']
     followup="INSERT INTO keyed(k,v,u) VALUES(NULL,'post-c',NULL);"
     lc=run([a.sqlite,'-batch','-bail',str(lean)],followup);rc=run([a.sqlite,'-batch','-bail',str(ref)],followup)
     readback="SELECT rowid,typeof(k),hex(k),typeof(v),hex(v),typeof(u),hex(u) FROM keyed ORDER BY rowid;"
     lr=run([binary,mode,str(lean)],readback);rr=run([a.sqlite,'-batch','-bail',str(ref)],readback)
     item.update(c_followup_lean=lc,c_followup_sqlite=rc,reopen_lean=lr,reopen_sqlite=rr)
     item['matched'] &= ((lc['code']!=0 and rc['code']!=0) or lc['code']==rc['code']==0) and lr['code']==rr['code']==0 and lr['stdout']==rr['stdout']
     if item['matched']:
      for key in ['lean','sqlite','observed_lean','observed_sqlite','reopen_lean','reopen_sqlite']:
       value=item[key];raw=value['stdout'].encode('latin1')
       if len(raw)>4096:
        value.update(stdout_bytes=len(raw),stdout_sha256=hashlib.sha256(raw).hexdigest(),stdout_prefix=raw[:128].decode('latin1'),stdout_suffix=raw[-128:].decode('latin1'));del value['stdout']
     cases.append(item)
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
