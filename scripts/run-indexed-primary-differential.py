#!/usr/bin/env python3
"""Non-alias single-column primary keys, NULL namespaces and numeric equality.

Compare complete successful output, error status, typed persisted rows and C
integrity. C then performs duplicate-key writes to test preserved constraint semantics.
This is a scoped SQL/file regression, not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354240);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
 types=['INT','REAL','NUMERIC','BLOB','','""','"text" extra','"INTEGER" extra','INTEGER(2)','VARCHAR(7)','ANY','INTEGER','TEXT']
 queries=[]
 def key_query(typ,table_key,policy,integer):
  key='PRIMARY KEY ON CONFLICT '+policy
  definition='a '+typ+('' if table_key else ' '+key)+",b TEXT NOT NULL ON CONFLICT REPLACE DEFAULT 'fallback'"
  if table_key:definition+=',PRIMARY KEY(a) ON CONFLICT '+policy
  return f"CREATE TABLE Extra({definition});\nINSERT INTO Extra(rowid,a,b) VALUES(2,{integer},'integer'),(1,NULL,'null-one'),(3,NULL,'null-two');\nINSERT OR IGNORE INTO Extra(rowid,a,b) VALUES(4,{integer}.0,'real'),(5,'{integer:03d}','numeric text'),(6,X'31','blob');\nSELECT rowid,typeof(a),hex(a),b FROM Extra ORDER BY rowid;\nSELECT rowid,typeof(a),hex(a),b FROM Extra WHERE a={integer}.0 ORDER BY rowid;\nUPDATE Extra SET b='matched' WHERE a='{integer:03d}' RETURNING rowid,typeof(a),hex(a),b;\nDELETE FROM Extra WHERE a=X'31';\nUPDATE OR REPLACE Extra SET a={integer+1}.0 WHERE rowid=2 RETURNING rowid,typeof(a),hex(a),b;\nINSERT OR REPLACE INTO Extra(a) VALUES({integer}),(NULL) RETURNING rowid,typeof(a),hex(a),b;\nINSERT INTO Extra(a) VALUES({integer});\nPRAGMA table_info(Extra);\nPRAGMA index_list(Extra);\nSELECT rowid,typeof(a),hex(a),b FROM Extra ORDER BY rowid;"
 for typ in types:
  for table_key in [False,True]:
   for policy in ['ABORT','IGNORE','REPLACE']:queries.append(key_query(typ,table_key,policy,1))
 for typ in ['BLOB','','NUMERIC','REAL']:
  queries.append(f"CREATE TABLE Extra(a {typ} PRIMARY KEY,b);\nINSERT INTO Extra VALUES(-9223372036854775808,'minimum'),(9223372036854775807,'maximum'),(0,'zero'),(9007199254740992,'exact'),(9007199254740993,'adjacent'),(1e999,'positive infinity'),(-1e999,'negative infinity');\nINSERT OR IGNORE INTO Extra VALUES(-9223372036854775808.0,'duplicate minimum'),(9223372036854775808.0,'upper real'),(-0.0,'negative zero'),(9007199254740992.0,'duplicate exact'),(9007199254740993.0,'rounded'),(9.007199254740994e15,'next'),(1e999,'duplicate infinity'),(-1e999,'duplicate negative');\nSELECT rowid,typeof(a),hex(a),b FROM Extra ORDER BY rowid;\nUPDATE OR REPLACE Extra SET a=0.0 WHERE b='maximum';\nSELECT rowid,typeof(a),hex(a),b FROM Extra ORDER BY rowid;")
 for typ in ['INT','REAL','BLOB','','""','"text" extra','"INTEGER" extra','TEXT']:
  for null_policy in ['ABORT','IGNORE','REPLACE']:
   for key_policy in ['IGNORE','REPLACE']:
    queries.append(f"CREATE TABLE Extra(a {typ} NOT NULL ON CONFLICT {null_policy} DEFAULT '007' PRIMARY KEY ON CONFLICT {key_policy},b);\nINSERT INTO Extra(b) VALUES('default');\nINSERT OR IGNORE INTO Extra VALUES(NULL,'ignored');\nINSERT INTO Extra VALUES(NULL,'null');\nUPDATE Extra SET a=NULL RETURNING rowid,typeof(a),hex(a),b;\nPRAGMA table_info(Extra);\nSELECT rowid,typeof(a),hex(a),b FROM Extra ORDER BY rowid;")
 for _ in range(a.random_cases):
  typ=rng.choice(types);queries.append(key_query(typ,rng.choice([False,True]),rng.choice(['ABORT','IGNORE','REPLACE']),rng.randrange(-1000000000,1000000000)))
 with tempfile.TemporaryDirectory(prefix='sqleanite-indexed-primary-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][(fixture//4)%3]
   base=Path(tmp)/f'base{fixture}.db';variant=fixture%4
   key='INTEGER' if variant<2 else 'TEXT';policy='IGNORE' if variant%2==0 else 'REPLACE'
   label='IGNORE' if fixture%3==0 else 'ABORT'
   keyNull=' NOT NULL ON CONFLICT IGNORE' if 4<=fixture<8 else ''
   definitions=[f'Id {key}{keyNull}',f'Label TEXT NOT NULL ON CONFLICT {label}','Val INTEGER']
   if fixture%8<4:definitions[0]+=f' PRIMARY KEY ON CONFLICT {policy}'
   shift=(fixture//4)%3;definitions=definitions[shift:]+definitions[:shift]
   if fixture%8>=4:definitions.append(f'PRIMARY KEY(Id) ON CONFLICT {policy}')
   if fixture%4!=0:
    definitions=[value.replace('NOT NULL', 'CONSTRAINT "Null constraint" NOT NULL').replace('PRIMARY KEY', 'CONSTRAINT "Key constraint" PRIMARY KEY') for value in definitions]
   definition=','.join(definitions)
   index='CREATE '+('UNIQUE ' if fixture%3!=0 else '')+'INDEX LabelIndex ON Users(Label);'
   setup=f"PRAGMA page_size={page};CREATE TABLE Users({definition});{index}INSERT INTO Users(Id,Label,Val) VALUES(1,'a',{rng.randrange(1,100)}),(2,'b',{rng.randrange(1,100)});"
   if fixture>=8:
    payload=rng.randbytes(4097).hex();longkey="'key-"+rng.randbytes(1200).hex()+"'" if key=='TEXT' else '37'
    setup+=f"INSERT INTO Users(Id,Label,Val) VALUES({longkey},'{payload}',99),(-13,CAST(X'80FF00' AS TEXT),-7);"
    if key=='TEXT':setup+="INSERT INTO Users(Id,Label,Val) VALUES(NULL,'null-one',1),(NULL,'null-two',2);"
   if fixture%2:
    foreign_type=types[(fixture//2)%len(types)]
    setup+=f"CREATE TABLE Imported(a {foreign_type} PRIMARY KEY,b);INSERT INTO Imported VALUES(NULL,'null-one'),(NULL,'null-two'),(7,'number'),(X'FF','blob');"
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=csql(ref,sql);lo=observe(lean);ro=observe(ref)
     matched=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     item=dict(fixture=fixture,page_size=page,schema_sql=setup,mode=mode,sql=sql,lean=l,sqlite=r,observed_lean=lo,observed_sqlite=ro,matched=matched)
     if r['code'] and '\n' not in sql:item['failed_statement_bytes_unchanged']=before==hashes(lean);item['matched'] &= item['failed_statement_bytes_unchanged']
     follow="INSERT INTO users(Id,Label,Val) VALUES(1,'follow',99);"
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
