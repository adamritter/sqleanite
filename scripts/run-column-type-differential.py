#!/usr/bin/env python3
"""Column type grammar, exact spans, affinities and rowid aliases.

Compare complete successful output, error status, typed persisted rows and C
integrity. C then performs duplicate-key writes to test preserved constraint semantics.
This is a scoped SQL/file regression, not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354230);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);p.add_argument('--nonalias-keys',action='store_true',help='Explicit diagnostic of currently unsupported custom non-alias primary keys');a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
 types=[
  '', 'INTEGER', 'int', 'TEXT', 'BLOB', 'REAL', 'NUMERIC', 'DOUBLE PRECISION', 'UNSIGNED BIG INT',
  'VARCHAR(25)', 'DECIMAL(-10,+2)', 'T(1e99)', 'T(0x10)', "'text' extra", '"quoted type"(8)',
  'TEXT /*trailing*/', 'INT/*inside*/EGER', 'varchar /*gap*/ ( 10 ) /*tail*/',
  'TEXT 123', 'BLOB notnull', '(12)', 'TEXT(1+2)', 'TEXT(1,2,3)', 'TEXT(2) EXTRA',
  'RIGHT', 'INDEXED', 'JOIN', 'NOTHING', 'RETURNING', 'TEXT(1_000)', 'TEXT(0xF_F)',
  "x'AB'", "x 'AB'", "x/*gap*/'AB'", 'TEXT()', 'TEXT(1,)', 'TEXT(+.5)', 'TEXT(-1e+2)',
  'GENERATED', 'GENERATED ALWAYS', 'TEXT GENERATED ALWAYS', 'INTgeneratedalways', 'LONGCUSTOMalways', '"INTEGER" always', '"text" extra',
  '""', "''", '[]', '"" extra', '" "', '"text"(3)', '"integer" extra',
  '"any" extra', 'ıNTEGER', 'ſtring', 'K', 'text always always',
  'INTEGER /*c*/ GENERATED ALWAYS', '"INTEGER" /*c*/ GENERATED ALWAYS',
  'T(1e999)', 'T(123456789012345678901234567890)', 'T(0x10000000000000000)',
  'T(- /*gap*/ 3,+ 2)', 'T(0x)', 'T(--3)', 'T(+ -3)', '`custom type` extra',
  'TEXT(NaN)', '"PRIMARY KEY"', "'123'", 'TEXT(1)(2)', 'a.b', 'TEXT /*tail*/ /*second*/',
 ]
 queries=[]
 for typ in types:
  queries.append(f"CREATE TABLE Extra(a {typ},b INTEGER PRIMARY KEY);\nINSERT INTO Extra(a) VALUES('007'),('not numeric'),(NULL);\nPRAGMA table_info(Extra);\nSELECT typeof(a),hex(a) FROM Extra ORDER BY b;")
  queries.append(f"ALTER TABLE users ADD Extra {typ} DEFAULT '007';")
 for typ in ['INTEGER /*tail*/', 'TEXT /*tail*/', 'INTEGER --tail\n', 'TEXT /*a*/ /*b*/']:
  queries.append(f"CREATE TABLE Extra(a {typ} PRIMARY KEY,b);\nINSERT INTO Extra VALUES(1,'first'),(2,'second');\nPRAGMA table_info(Extra);\nSELECT rowid,* FROM Extra ORDER BY rowid;")
 for _ in range(a.random_cases):
  n=rng.randrange(1,10000);m=rng.randrange(0,100);label='type_'+str(rng.getrandbits(32))
  typ=rng.choice([f'VARCHAR({n})',f'DECIMAL(-{n},+{m})',f'\"{label}\" extra',f'INT /* tail-{n} */',f'T({n}+{m})',f'T({n}_{m})'])
  queries.append(f"CREATE TABLE Extra(a {typ});\nINSERT INTO Extra VALUES('007');\nPRAGMA table_info(Extra);\nSELECT typeof(a),hex(a) FROM Extra;")
 if a.nonalias_keys:
  queries=[]
  for typ in ['INT', 'REAL', 'NUMERIC', 'BLOB', '', '"INTEGER" extra', '"integer" extra', '"text" extra', 'INTEGER /*c*/ GENERATED ALWAYS']:
   queries.append(f"CREATE TABLE Extra(a {typ} PRIMARY KEY,b);\nINSERT INTO Extra VALUES('007','first'),(NULL,'null');\nPRAGMA table_info(Extra);\nPRAGMA index_list(Extra);\nSELECT rowid,typeof(a),hex(a),b FROM Extra ORDER BY rowid;")
 with tempfile.TemporaryDirectory(prefix='sqleanite-column-type-') as tmp:
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
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,nonalias_key_diagnostic=a.nonalias_keys,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
