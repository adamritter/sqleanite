#!/usr/bin/env python3
"""CREATE TABLE AS SELECT schema derivation, stored values and rowid assignment.

Compare complete successful output, positive errors, and independently pinned-C
observations of catalog identities, column/index metadata, typed persisted rows
and integrity. Do not fold observed names. This is not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354180);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
  'CREATE TABLE Copy AS SELECT * FROM users ORDER BY oid;\nSELECT oid,* FROM Copy ORDER BY oid;',
  'CREATE TABLE Copy AS SELECT * FROM users WHERE 0;\nPRAGMA table_info(Copy);',
  'CREATE TABLE Copy AS SELECT Label AS Name,Id AS Ident,Val AS Amount FROM users ORDER BY Id DESC;\nSELECT oid,* FROM Copy ORDER BY oid;',
  "CREATE TABLE Copy AS SELECT 1,2.5,'it''s',NULL,X'80FF';\nSELECT oid,* FROM Copy;",
  "CREATE TABLE Copy AS SELECT CAST(1 AS TEXT) AS a,CAST('2' AS INTEGER) AS b,CAST(3 AS REAL) AS c,CAST(4 AS NUMERIC) AS d,CAST(5 AS BLOB) AS e;\nPRAGMA table_info(Copy);",
  'CREATE TABLE Copy AS SELECT Id+0 AS plus, +Val AS unary, Label COLLATE binary FROM users ORDER BY oid;\nSELECT oid,* FROM Copy ORDER BY oid;',
  'CREATE TABLE Copy AS SELECT true,false,likely(1),1 /*source*/ + 2;\nPRAGMA table_info(Copy);',
  'CREATE TABLE Copy AS SELECT Label,Label,Label FROM users ORDER BY oid;\nPRAGMA table_info(Copy);',
  'CREATE TABLE Copy AS SELECT Id AS A,Val AS a,Label AS "a:1" FROM users ORDER BY oid;\nPRAGMA table_info(Copy);',
  'CREATE TABLE Copy AS SELECT rowid,oid,_rowid_ FROM tags ORDER BY oid;\nPRAGMA table_info(Copy);',
  'CREATE TABLE Copy AS SELECT * FROM users ORDER BY oid LIMIT 1;\nINSERT INTO Copy SELECT * FROM users ORDER BY oid;\nSELECT oid,* FROM Copy ORDER BY oid;',
  'CREATE TABLE "Dotted.Copy" AS SELECT * FROM tags ORDER BY oid;\nSELECT oid,* FROM "Dotted.Copy" ORDER BY oid;',
  'CREATE TABLE "" AS SELECT * FROM users ORDER BY oid;\nSELECT oid,* FROM "" ORDER BY oid;',
  'CREATE TABLE Copy AS SELECT count(*) AS Count,max(Id) AS Maximum FROM users;\nSELECT oid,* FROM Copy;',
  'CREATE TABLE Copy AS SELECT Id FROM users UNION ALL SELECT Owner FROM tags ORDER BY 1;\nPRAGMA table_info(Copy);',
  'CREATE TABLE Copy AS SELECT 1 AS a UNION ALL SELECT CAST(2 AS TEXT);\nSELECT typeof(a),hex(a) FROM Copy ORDER BY rowid;',
  'CREATE TABLE Copy AS SELECT u.Id,t.Owner FROM users u JOIN tags t ON u.Id=t.Owner ORDER BY u.Id,t.Owner;\nSELECT oid,* FROM Copy ORDER BY oid;',
  'CREATE TABLE IF NOT EXISTS users AS SELECT missing FROM absent;',
  'CREATE TABLE users AS SELECT 1;',
  'CREATE TABLE LabelIndex AS SELECT 1;',
  'CREATE TABLE sqlite_forbidden AS SELECT 1;',
  'CREATE TABLE Copy AS SELECT * FROM missing;',
  'BEGIN;\nCREATE TABLE Copy AS SELECT * FROM users ORDER BY oid;\nROLLBACK;',
  'BEGIN;\nCREATE TABLE Copy AS SELECT * FROM users ORDER BY oid;\nCOMMIT;',
  "CREATE TABLE Copy AS SELECT 'a''b', 'x' /* ; */ || 'y';\nPRAGMA table_info(Copy);"]
 queries.append('CREATE TABLE Copy AS VALUES(1,2),(3,4);\nSELECT rowid,* FROM Copy ORDER BY rowid;')
 queries.extend(["CREATE TABLE Copy AS SELECT 1 /*end*/;\nPRAGMA table_info(Copy);", "CREATE TABLE Copy AS SELECT /*start*/((1));\nPRAGMA table_info(Copy);", "CREATE TABLE Copy AS SELECT 1 --end\n;\nPRAGMA table_info(Copy);", "CREATE TABLE Copy AS SELECT 1/*notclosed"])
 def case_name(name):return ''.join(ch.upper() if rng.getrandbits(1) else ch.lower() for ch in name)
 for _ in range(a.random_cases):
  name='Copy'+str(rng.randrange(1000000));alias='field_'+str(rng.randrange(1000000));constant=rng.randrange(-100000,100000)
  queries.append('CREATE TABLE '+ident(name)+' AS SELECT Id,'+str(constant)+' AS '+ident(alias)+',Label FROM users ORDER BY Id '+rng.choice(['ASC','DESC'])+';\nSELECT oid,* FROM '+ident(name)+' ORDER BY oid;')
 with tempfile.TemporaryDirectory(prefix='sqleanite-create-table-as-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][(fixture//3)%3];upper_table=fixture%3!=0;upper_column=fixture%3!=1
   table='Users' if upper_table else 'users';tags='Tags' if upper_table else 'tags';index='LabelIndex' if upper_table else 'labelindex'
   cols=['Id','Label','Val'] if upper_column else ['id','label','val'];tc=['Key','Owner'] if upper_column else ['key','owner'];base=Path(tmp)/f'base{fixture}.db'
   primary='' if fixture%3==0 else ' PRIMARY KEY'
   definitions=[f'{ident(cols[0])} INTEGER{primary}',f'{ident(cols[1])} TEXT',f'{ident(cols[2])} INTEGER'];shift=(fixture//3)%3;definitions=definitions[shift:]+definitions[:shift]
   tag_definitions=[f'{ident(tc[0])} TEXT PRIMARY KEY',f'{ident(tc[1])} INTEGER']
   if fixture%2:tag_definitions.reverse()
   setup=f'PRAGMA page_size={page};CREATE TABLE {ident(table)}('+','.join(definitions)+f');CREATE INDEX {ident(index)} ON {ident(table.swapcase())}({ident(cols[1].swapcase())});CREATE TABLE {ident(tags)}('+','.join(tag_definitions)+');'
   if fixture%3!=2:setup+=f"INSERT INTO {ident(table)}({ident(cols[0])},{ident(cols[1])},{ident(cols[2])}) VALUES(1,'value-{rng.getrandbits(32):08x}',10),(2,'value-{rng.getrandbits(32):08x}',20);INSERT INTO {ident(tags)}({ident(tc[0])},{ident(tc[1])}) VALUES('a',1),('b',2);"
   if fixture>=3 and fixture%3!=2:
    payload=rng.randbytes(4097).hex();key='key-'+rng.randbytes(1200).hex()
    setup+=f"INSERT INTO {ident(table)}({ident(cols[0])},{ident(cols[1])},{ident(cols[2])}) VALUES(-17,CAST(X'80FF00' AS TEXT),-9),(73,'{payload}',99);INSERT INTO {ident(tags)}({ident(tc[0])},{ident(tc[1])}) VALUES(NULL,3),('{key}',73);"
   if fixture>=3:setup+=f'ALTER TABLE {ident(table)} ADD PreExisting;ALTER TABLE {ident(tags)} ADD PreExisting;'
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=csql(ref,sql);lo=observe(lean);ro=observe(ref)
     matched=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     item=dict(fixture=fixture,page_size=page,upper_table=upper_table,upper_column=upper_column,mode=mode,sql=sql,lean=l,sqlite=r,observed_lean=lo,observed_sqlite=ro,matched=matched)
     if r['code'] and '\n' not in sql:item['failed_statement_bytes_unchanged']=before==hashes(lean);item['matched'] &= item['failed_statement_bytes_unchanged']
     follow="ALTER TABLE users ADD COLUMN FromC;"
     lf=csql(lean,follow);rf=csql(ref,follow)
     tables=csql(ref,"SELECT name FROM sqlite_schema WHERE type='table' ORDER BY name;")
     reopen_sql='\n'.join('SELECT rowid,* FROM '+ident(name)+' ORDER BY rowid;' for name in tables['stdout'].encode('latin1').decode('utf8').splitlines())
     lr=run([binary,mode,str(lean)],reopen_sql);rr=csql(ref,reopen_sql)
     after_l=observe(lean);after_r=observe(ref)
     item.update(c_followup_lean=lf,c_followup_sqlite=rf,reopen_sql=reopen_sql,reopened_lean=lr,reopened_sqlite=rr,after_followup_lean=after_l,after_followup_sqlite=after_r)
     item['matched'] &= lf['code']==rf['code']==0 and lf['stdout']==rf['stdout'] and lr['code']==rr['code']==0 and lr['stdout']==rr['stdout'] and after_l['code']==after_r['code']==0 and after_l['stdout']==after_r['stdout'] and after_l['stdout'].startswith('ok\n')
     if item['matched']:
      for value in item.values():
       if isinstance(value,dict) and len(value.get('stdout',''))>4096:
        data=value.pop('stdout').encode('latin1');value.update(stdout_bytes=len(data),stdout_sha256=hashlib.sha256(data).hexdigest())
     cases.append(item)
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
