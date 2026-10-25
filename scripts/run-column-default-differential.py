#!/usr/bin/env python3
"""Column DEFAULT expressions, lazy evaluation, conflict replacement and old records.

Compare complete successful output, error status, typed persisted rows and C
integrity. C then inserts omitted fields to test persisted DEFAULT semantics.
This is a scoped SQL/file regression, not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354210);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
  "INSERT INTO users DEFAULT VALUES;",
  "INSERT INTO users DEFAULT VALUES RETURNING rowid,*;",
  "INSERT INTO users(Id) VALUES(17);",
  "INSERT INTO users(Label) VALUES('manual');",
  "INSERT INTO users(Val) VALUES(8),(9) RETURNING rowid,*;",
  "INSERT INTO users(Id,Label) VALUES(17,NULL);",
  "INSERT OR REPLACE INTO users(Id,Label,Val) VALUES(17,NULL,NULL) RETURNING rowid,*;",
  "INSERT OR IGNORE INTO users(Id,Label,Val) VALUES(17,NULL,NULL) RETURNING rowid,*;",
  "INSERT OR ABORT INTO users(Id,Label,Val) VALUES(17,NULL,NULL);",
  "UPDATE users SET Label=NULL,Val=NULL RETURNING rowid,*;",
  "UPDATE OR REPLACE users SET Label=NULL,Val=NULL RETURNING rowid,*;",
  "UPDATE OR IGNORE users SET Label=NULL,Val=NULL RETURNING rowid,*;",
  "INSERT INTO users(Label) SELECT 'copy-' || Label FROM users ORDER BY rowid RETURNING rowid,*;",
  "PRAGMA table_info(users);",
  "ALTER TABLE users ADD Extra TEXT DEFAULT 'added';\nSELECT rowid,* FROM users ORDER BY rowid;",
  "ALTER TABLE users ADD Extra NOT NULL DEFAULT 7;\nSELECT rowid,* FROM users ORDER BY rowid;",
  "ALTER TABLE users ADD Extra DEFAULT (1+2);",
  "ALTER TABLE users RENAME COLUMN Label TO Renamed;\nALTER TABLE users RENAME COLUMN Renamed TO Label;",
 ]
 for default in ["NULL", "12", "-9223372036854775808", "+ /*middle*/ 1", "'quo''te'", "X'80FF00'", "foo", "TRUE", '"quoted"', "( 1 /*tail*/ )", "(1+2)", "(abs(-5))", "(coalesce(NULL,'value'))", "(CAST(X'80FF00' AS TEXT))"]:
  queries.append(f"CREATE TABLE Extra(k INTEGER PRIMARY KEY DEFAULT 99,a DEFAULT {default});\nINSERT INTO Extra DEFAULT VALUES;\nPRAGMA table_info(Extra);\nSELECT rowid,* FROM Extra;")
 for tail in ["", "\nINSERT INTO Extra DEFAULT VALUES;", "\nINSERT INTO Extra(a) VALUES(7);"]:
  queries.append("CREATE TABLE Extra(a DEFAULT (abs(-9223372036854775808)));"+tail)
 queries += [
  "CREATE TABLE Extra(a);\nALTER TABLE Extra ADD b DEFAULT (1+2);\nINSERT INTO Extra DEFAULT VALUES;\nSELECT * FROM Extra;",
  "CREATE TABLE Extra(a DEFAULT 1 DEFAULT 'last');\nINSERT INTO Extra DEFAULT VALUES;\nPRAGMA table_info(Extra);\nSELECT * FROM Extra;",
  "CREATE TABLE Extra(a DEFAULT (other));",
  'CREATE TABLE Extra(a DEFAULT ("quoted"));',
  "CREATE TABLE Extra(a DEFAULT abs(1));",
  "CREATE TABLE Extra(a DEFAULT ((SELECT 1)));",
  "CREATE TABLE Extra(a DEFAULT ?);",
  "CREATE TABLE Extra(a DEFAULT +TRUE);",
  "CREATE TABLE Extra(a NOT NULL ON CONFLICT REPLACE DEFAULT NULL,b NOT NULL ON CONFLICT IGNORE);\nINSERT INTO Extra VALUES(NULL,NULL);",
  "CREATE TABLE Extra(a NOT NULL ON CONFLICT REPLACE DEFAULT NULL,b NOT NULL ON CONFLICT IGNORE);\nINSERT INTO Extra VALUES(NULL,1);",
 ]
 for default in ["(not_a_function(1))", "(abs())", "(sum(1))", "(count(*))", "(-0x8000000000000000)", "(0 AND other)", "(other IN ())", "(1 OR not_a_function(1))", "(FALSE AND not_a_function(1))", "(CASE WHEN 1 THEN 7 ELSE not_a_function(1) END)"]:
  queries.append(f"CREATE TABLE Extra(a DEFAULT {default});")
  queries.append(f"CREATE TABLE Extra(a DEFAULT {default});\nINSERT INTO Extra DEFAULT VALUES;")
 for default in ["-0.0", "1e999", "0xFFFFFFFFFFFFFFFF", "(CAST('1.5' AS INTEGER))", "(-'foo')", "(-NULL)", "(TRUE)", "(coalesce(NULL, 7))", "(CASE WHEN 1 THEN 'é😀' ELSE 'no' END)", "( 'quote''*/--' /*tail*/ )", "'line1\nline2'", "x"]:
  queries.append(f"CREATE TABLE Extra(a DEFAULT {default});\nINSERT INTO Extra DEFAULT VALUES;\nPRAGMA table_info(Extra);\nSELECT typeof(a),hex(a) FROM Extra;")
  queries.append(f"ALTER TABLE users ADD Extra DEFAULT {default};")
 queries += [
  "CREATE TABLE Extra(a DEFAULT (abs(-9223372036854775808)));\nINSERT INTO Extra SELECT 1 WHERE 0;",
  "CREATE TABLE Extra(a NOT NULL ON CONFLICT REPLACE DEFAULT '4',b INTEGER NOT NULL ON CONFLICT REPLACE DEFAULT '7');\nINSERT OR REPLACE INTO Extra DEFAULT VALUES RETURNING *;\nUPDATE OR REPLACE Extra SET a=NULL,b=NULL RETURNING *;",
 ]
 for default in ["(not_a_function(1))", "(abs(-9223372036854775808))"]:
  for action in ["INSERT INTO Extra(b) SELECT 1 WHERE 0;", "INSERT INTO Extra(b) SELECT 1 WHERE 0 RETURNING *;", "UPDATE OR REPLACE Extra SET a=NULL;", "UPDATE OR REPLACE Extra SET a=7 RETURNING *;", "UPDATE OR REPLACE Extra SET b=7;", "INSERT OR REPLACE INTO Extra(a,b) SELECT 7,1 WHERE 0;", "INSERT OR REPLACE INTO Extra(a,b) VALUES(7,1);", "INSERT INTO Extra(a,b) VALUES(7,1);"]:
   queries.append(f"CREATE TABLE Extra(a NOT NULL ON CONFLICT REPLACE DEFAULT {default},b);\n"+action)
 for _ in range(a.random_cases):
  value=rng.randrange(-100000,100000);action=rng.choice(['',' OR IGNORE',' OR ABORT',' OR REPLACE'])
  label=rng.choice(['NULL',"'fresh-"+str(rng.getrandbits(32))+"'"])
  queries.append(rng.choice([f"INSERT{action} INTO users(Val) VALUES({value}) RETURNING rowid,*;",f"INSERT{action} INTO users(Label) VALUES({label}) RETURNING rowid,*;",f"UPDATE{action} users SET Label={label},Val=NULL WHERE Id={rng.randrange(1,4)} RETURNING rowid,*;"]))
 with tempfile.TemporaryDirectory(prefix='sqleanite-column-default-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][(fixture//4)%3]
   base=Path(tmp)/f'base{fixture}.db';variant=fixture%4
   definitions=["Id INTEGER PRIMARY KEY DEFAULT 99", "Label TEXT DEFAULT 'default-label'", "Val INTEGER DEFAULT '0042'"]
   if variant==0:definitions=["Id INTEGER PRIMARY KEY", "Label TEXT", "Val INTEGER"]
   if variant==2:definitions=["Id INTEGER PRIMARY KEY DEFAULT (1+2)", "Label TEXT NOT NULL ON CONFLICT REPLACE DEFAULT (upper('default'))", "Val INTEGER NOT NULL ON CONFLICT IGNORE DEFAULT (1+2)"]
   if variant==3:definitions=["Id TEXT PRIMARY KEY ON CONFLICT IGNORE DEFAULT 'key'", "Label TEXT NOT NULL ON CONFLICT REPLACE DEFAULT NULL", "Val INTEGER NOT NULL ON CONFLICT IGNORE DEFAULT 7"]
   shift=(fixture//4)%3;definitions=definitions[shift:]+definitions[:shift]
   definition=','.join(definitions)
   setup=f"PRAGMA page_size={page};CREATE TABLE Users({definition});CREATE INDEX LabelIndex ON Users(Label);INSERT INTO Users(Id,Label,Val) VALUES(1,'a',{rng.randrange(1,100)}),(2,'b',{rng.randrange(1,100)});"
   if fixture>=8:
    payload=rng.randbytes(4097).hex()
    setup+=f"INSERT INTO Users(Id,Label,Val) VALUES(37,'{payload}',99),(-13,CAST(X'80FF00' AS TEXT),-7);"
   if fixture>=4:setup+="ALTER TABLE Users ADD OldDefault TEXT DEFAULT 'old-record';"
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=csql(ref,sql);lo=observe(lean);ro=observe(ref)
     matched=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     item=dict(fixture=fixture,page_size=page,schema_sql=setup,mode=mode,sql=sql,lean=l,sqlite=r,observed_lean=lo,observed_sqlite=ro,matched=matched)
     if r['code'] and '\n' not in sql:item['failed_statement_bytes_unchanged']=before==hashes(lean);item['matched'] &= item['failed_statement_bytes_unchanged']
     follow="INSERT INTO users(Val) VALUES(99);"
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
