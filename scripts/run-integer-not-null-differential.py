#!/usr/bin/env python3
"""Explicit INTEGER PRIMARY KEY NOT NULL metadata public-file differential against pinned SQLite.

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
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354090);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=["SELECT rowid,* FROM keyed ORDER BY rowid;",
  "UPDATE keyed SET v=v||'x';",
  "INSERT INTO keyed(k,v,u) VALUES(NULL,'new',NULL) RETURNING rowid,k;",
  "INSERT OR REPLACE INTO keyed(k,v,u) VALUES(1,'replace',NULL) RETURNING rowid,k;",
  "UPDATE keyed SET k=NULL;",
  "DELETE FROM keyed WHERE k=1 RETURNING rowid,k;",
  "BEGIN;\nUPDATE keyed SET v=v||'x';\nROLLBACK;",
  "BEGIN;\nUPDATE keyed SET v=v||'x';\nCOMMIT;"]
 for _ in range(a.random_cases):
  value=rng.choice(['NULL','-10','0','1','2','3','12'])
  if rng.randrange(2):
   queries.append('INSERT'+rng.choice(['',' OR ABORT',' OR IGNORE',' OR REPLACE'])+f" INTO keyed(k,v,u) VALUES({value},'random-{rng.getrandbits(32):08x}',NULL) RETURNING rowid,k;")
  else:
   queries.append('UPDATE'+rng.choice(['',' OR ABORT',' OR IGNORE',' OR REPLACE'])+' keyed SET '+rng.choice(["v=v||'x'",'k='+value])+' WHERE '+rng.choice(['1','0','k=1','k>1'])+' RETURNING rowid,k;')
 with tempfile.TemporaryDirectory(prefix='sqleanite-integer-not-null-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][(fixture//3)%3];base=Path(tmp)/f'base{fixture}.db'
   integer_key = True
   not_null = fixture % 2 == 0
   with_nulls = False
   spelling = rng.choice(['PRIMARY KEY(k)','CONSTRAINT "primary key name" PRIMARY KEY("k" ASC)','PRIMARY KEY(k COLLATE binary ASC) ON CONFLICT ABORT'])
   if integer_key:spelling=rng.choice([spelling,'PRIMARY KEY(k DESC)','PRIMARY KEY(k COLLATE nocase DESC)'])
   key_position=(fixture//3+fixture%3)%3
   columns=['v','u INTEGER'];columns.insert(key_position,f"k {'INTEGER' if integer_key else 'TEXT'}{' NOT NULL' if not_null else ''}")
   if fixture%3==0:
    columns[key_position]+=" PRIMARY KEY"
    ddl="CREATE TABLE keyed("+','.join(columns)+");"
   else:ddl="CREATE TABLE keyed("+','.join(columns)+','+spelling+");"
   unique_values=rng.sample(range(1,20),4)
   payloads=[f"fixture{fixture}-{rng.getrandbits(48):012x}" for _ in range(4)]
   setup=f"PRAGMA page_size={page};"+ddl+f"INSERT INTO keyed(k,v,u) VALUES(1,'{payloads[0]}',{unique_values[0]}),(2,'{payloads[1]}',{unique_values[1]});"
   if with_nulls:setup += f"INSERT INTO keyed(k,v,u) VALUES(NULL,'{payloads[2]}',{unique_values[2]}),(NULL,'{payloads[3]}',{unique_values[3]});"
   setup += "CREATE UNIQUE INDEX ku ON keyed(u);"
   r=run([a.sqlite,'-batch','-bail',str(base)],setup);assert r['code']==0,r
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries+["DROP TABLE keyed;\n"+ddl+"\nINSERT INTO keyed(k,v,u) VALUES(NULL,'new',9);","DROP TABLE keyed;\n"+ddl+"\nINSERT INTO keyed(k,v,u) VALUES(1,'first',9),(2,'second',10);"]:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail',str(ref)],sql)
     same=(l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']);item=dict(fixture=fixture,page_size=page,ddl=ddl,key_position=key_position,initial_unique_values=unique_values,initial_payloads=payloads,integer_key=integer_key,not_null=not_null,initial_nulls=with_nulls,mode=mode,sql=sql,lean=l,sqlite=r,matched=same)
     observation="SELECT name,type,tbl_name FROM sqlite_schema ORDER BY name;"+'PRAGMA integrity_check;PRAGMA table_info(keyed);PRAGMA index_list(keyed);SELECT rowid,typeof(k),hex(k),typeof(v),hex(v),typeof(u),hex(u) FROM keyed ORDER BY rowid;';lo=run([a.sqlite,'-batch','-bail',str(lean)],observation);ro=run([a.sqlite,'-batch','-bail',str(ref)],observation);item.update(observed_lean=lo,observed_sqlite=ro);item['matched'] &= lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and '\nok\n' in lo['stdout']
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
