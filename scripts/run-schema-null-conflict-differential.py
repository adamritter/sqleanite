#!/usr/bin/env python3
"""NOT NULL conflict policies, statement overrides and persisted schema behavior.

Compare complete successful output, error status, typed persisted rows and C
integrity. C then performs NULL writes to test preserved constraint semantics.
This is a scoped SQL/file regression, not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354190);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([a.sqlite,'-batch','-bail',str(path)],sql)
 def ident(name):return '"'+name.replace('"','""')+'"'
 def literal(value):return "'"+value.replace("'","''")+"'"
 def observe(path):
  outputs=[csql(path,'PRAGMA integrity_check;'),csql(path,'SELECT name,type,tbl_name FROM sqlite_schema ORDER BY name;')]
  names=csql(path,"SELECT name FROM sqlite_schema WHERE type='table' ORDER BY name;");outputs.append(names)
  if names['code']==0:
   for name in names['stdout'].encode('latin1').decode('utf8').splitlines():
    columns=csql(path,'SELECT name FROM pragma_table_info('+literal(name)+') ORDER BY cid;');outputs.append(columns)
    if columns['code']:continue
    fields=[part for column in columns['stdout'].encode('latin1').decode('utf8').splitlines() for part in ['typeof('+ident(column)+')','hex('+ident(column)+')']]
    outputs.append(csql(path,'PRAGMA table_info('+ident(name)+');PRAGMA index_list('+ident(name)+');SELECT rowid,'+','.join(fields)+' FROM '+ident(name)+' ORDER BY rowid;'))
  return dict(code=int(any(o['code'] for o in outputs)),stdout=''.join(o['stdout'] for o in outputs),stderr=''.join(o['stderr'] for o in outputs))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=[
  "INSERT INTO users(Id,Label,Val) VALUES(3,NULL,9);",
  "INSERT INTO users(Id,Label,Val) VALUES(3,'c',NULL);",
  "INSERT INTO users(Id,Label,Val) VALUES(3,NULL,NULL);",
  "INSERT INTO users(Id) VALUES(3);",
  "INSERT INTO users DEFAULT VALUES;",
  "INSERT INTO users(Id,Label,Val) VALUES(3,'c',9),(4,NULL,10),(5,'e',11);",
  "INSERT INTO users(Id,Label,Val) VALUES(3,'c',9),(4,NULL,10),(5,'e',11) RETURNING rowid,*;",
  "INSERT OR ABORT INTO users(Id,Label,Val) VALUES(3,NULL,9);",
  "INSERT OR IGNORE INTO users(Id,Label,Val) VALUES(3,NULL,NULL),(4,'d',9);",
  "INSERT OR REPLACE INTO users(Id,Label,Val) VALUES(1,NULL,9);",
  "INSERT INTO users(Id,Label,Val) VALUES(1,NULL,9);",
  "INSERT INTO users(rowid,Id,Label,Val) VALUES('bad',3,NULL,9);",
  "INSERT INTO users(Id,Label,Val) SELECT Id+10,NULL,Val FROM users ORDER BY rowid;",
  "INSERT INTO users(Id,Label,Val) SELECT Id+10,NULL,Val FROM users ORDER BY rowid RETURNING rowid,*;",
  "UPDATE users SET Label=NULL;",
  "UPDATE users SET Val=NULL;",
  "UPDATE users SET Label=NULL,Val=NULL;",
  "UPDATE users SET Id=Id+10,Label=CASE WHEN Id=2 THEN NULL ELSE 'c' END;",
  "UPDATE users SET Label=NULL RETURNING rowid,*;",
  "UPDATE OR ABORT users SET Label=NULL;",
  "UPDATE OR IGNORE users SET Label=NULL,Val=NULL;",
  "UPDATE OR REPLACE users SET Label=NULL;",
  "UPDATE users SET rowid=NULL,Label=NULL;",
  "UPDATE users SET Id=1,Label=NULL WHERE Id=2;",
  "UPDATE users SET Val=Val+1;",
  "BEGIN;\nUPDATE users SET Val=Val+1;\nINSERT INTO users(Id,Label,Val) VALUES(3,NULL,9);\nROLLBACK;",
  "ALTER TABLE users RENAME COLUMN Label TO Renamed;\nALTER TABLE users RENAME COLUMN Renamed TO Label;",
  "CREATE TABLE Extra(k INTEGER PRIMARY KEY,n TEXT NOT NULL ON CONFLICT IGNORE);\nINSERT INTO Extra VALUES(1,NULL),(2,'x');\nSELECT * FROM Extra ORDER BY k;",
  "CREATE TABLE Extra(k INTEGER PRIMARY KEY,n TEXT NOT NULL ON CONFLICT REPLACE);\nINSERT INTO Extra VALUES(1,'x');",
  "CREATE TABLE Extra(k INTEGER PRIMARY KEY,n NOT NULL ON CONFLICT IGNORE NOT NULL);\nINSERT INTO Extra VALUES(1,NULL);",
  "CREATE TABLE Extra(k INTEGER PRIMARY KEY,n NOT NULL ON CONFLICT ABORT NOT NULL ON CONFLICT IGNORE);\nINSERT INTO Extra VALUES(1,NULL);",
 ]
 queries.extend([
  "CREATE TABLE Extra(k INTEGER PRIMARY KEY);\nALTER TABLE Extra ADD n NOT NULL ON CONFLICT IGNORE;\nINSERT INTO Extra VALUES(1,NULL),(2,'x');",
  "ALTER TABLE users ADD n NOT NULL ON CONFLICT IGNORE;",
  "CREATE UNIQUE INDEX UniqueLabel ON users(Label);\nINSERT INTO users VALUES(3,'a',9);",
  "CREATE UNIQUE INDEX UniqueLabel ON users(Label);\nINSERT INTO users VALUES(3,'a',NULL);",
  "UPDATE users SET Label=CASE WHEN Id=2 THEN NULL ELSE 'z' END,Val=Val+10 WHERE Label>='a';",
  "UPDATE users SET Id=Id+1,Label=CASE WHEN Id=2 THEN NULL ELSE Label END;",
  "UPDATE users SET Label=NULL,Val=abs(-9223372036854775808);",
  "INSERT INTO users VALUES(3,NULL,9) RETURNING abs(-9223372036854775808);",
  "UPDATE users SET Label=NULL RETURNING abs(-9223372036854775808);",
  "CREATE TABLE Extra(k TEXT PRIMARY KEY NOT NULL ON CONFLICT IGNORE,n);\nINSERT INTO Extra VALUES(NULL,1),('a',2);",
  "CREATE TABLE Extra(k INTEGER PRIMARY KEY NOT NULL ON CONFLICT REPLACE,n);\nINSERT INTO Extra VALUES(NULL,1);",
  "CREATE TABLE Extra(a NOT NULL ON CONFLICT IGNORE,b NOT NULL ON CONFLICT REPLACE);\nINSERT INTO Extra VALUES(NULL,NULL);",
  "CREATE TABLE Extra(a NOT NULL ON CONFLICT REPLACE,b NOT NULL ON CONFLICT IGNORE);\nINSERT INTO Extra VALUES(NULL,NULL);",
 ])
 for _ in range(a.random_cases):
  value=rng.randrange(-100000,100000);action=rng.choice(['',' OR IGNORE',' OR ABORT',' OR REPLACE'])
  label=rng.choice(['NULL',"'fresh-"+str(rng.getrandbits(32))+"'"]);number=rng.choice(['NULL',str(value)])
  if rng.getrandbits(1):queries.append(f"INSERT{action} INTO users(Id,Label,Val) VALUES({rng.randrange(1,6)},{label},{number}) RETURNING rowid,*;")
  else:queries.append(f"UPDATE{action} users SET Label={label},Val={number} WHERE Id={rng.randrange(1,4)} RETURNING rowid,*;")
 with tempfile.TemporaryDirectory(prefix='sqleanite-schema-null-conflict-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][(fixture//4)%3]
   base=Path(tmp)/f'base{fixture}.db';variant=fixture%8
   key=['INTEGER PRIMARY KEY','INTEGER PRIMARY KEY','INTEGER','TEXT PRIMARY KEY','INTEGER PRIMARY KEY NOT NULL ON CONFLICT IGNORE','INTEGER PRIMARY KEY','TEXT PRIMARY KEY NOT NULL ON CONFLICT IGNORE','INTEGER PRIMARY KEY NOT NULL ON CONFLICT REPLACE'][variant]
   label=['IGNORE','ABORT','REPLACE','IGNORE','IGNORE','IGNORE','IGNORE','REPLACE'][variant];val=['ABORT','IGNORE','IGNORE','ABORT','REPLACE','IGNORE','ABORT','IGNORE'][variant]
   setup=f"PRAGMA page_size={page};CREATE TABLE Users(Id {key},Label TEXT NOT NULL ON CONFLICT {label},Val INTEGER NOT NULL ON CONFLICT {val});CREATE INDEX LabelIndex ON Users(Label);INSERT INTO Users VALUES(1,'a',7),(2,'b',8);"
   if fixture>=8:
    payload=rng.randbytes(4097).hex()
    setup+=f"INSERT INTO Users VALUES(37,'{payload}',99),(-11,CAST(X'80FF00' AS TEXT),-7);"
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=csql(ref,sql);lo=observe(lean);ro=observe(ref)
     matched=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     item=dict(fixture=fixture,page_size=page,schema_sql=setup,mode=mode,sql=sql,lean=l,sqlite=r,observed_lean=lo,observed_sqlite=ro,matched=matched)
     if r['code'] and '\n' not in sql:item['failed_statement_bytes_unchanged']=before==hashes(lean);item['matched'] &= item['failed_statement_bytes_unchanged']
     follow="INSERT INTO users(Id,Label,Val) VALUES(99,NULL,7);"
     lf=csql(lean,follow);rf=csql(ref,follow)
     tables=csql(ref,"SELECT name FROM sqlite_schema WHERE type='table' ORDER BY name;")
     reopen_sql='\n'.join('SELECT rowid,* FROM '+ident(name)+' ORDER BY rowid;' for name in tables['stdout'].encode('latin1').decode('utf8').splitlines())
     lr=run([binary,mode,str(lean)],reopen_sql);rr=csql(ref,reopen_sql)
     after_l=observe(lean);after_r=observe(ref)
     item.update(c_followup_lean=lf,c_followup_sqlite=rf,reopen_sql=reopen_sql,reopened_lean=lr,reopened_sqlite=rr,after_followup_lean=after_l,after_followup_sqlite=after_r)
     item['matched'] &= ((lf['code']!=0 and rf['code']!=0) or (lf['code']==rf['code']==0 and lf['stdout']==rf['stdout'])) and lr['code']==rr['code']==0 and lr['stdout']==rr['stdout'] and after_l['code']==after_r['code']==0 and after_l['stdout']==after_r['stdout'] and after_l['stdout'].startswith('ok\n')
     if item['matched']:
      for value in item.values():
       if isinstance(value,dict) and len(value.get('stdout',''))>4096:
        data=value.pop('stdout').encode('latin1');value.update(stdout_bytes=len(data),stdout_sha256=hashlib.sha256(data).hexdigest())
     cases.append(item)
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
