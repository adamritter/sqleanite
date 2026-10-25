#!/usr/bin/env python3
"""Case-insensitive SQL binding with case-preserving schema metadata.

Compare complete successful output, positive errors, and independently pinned-C
observations of catalog identities, column/index metadata, typed persisted rows
and integrity. Do not fold observed names. This is not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354100);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
  'SELECT * FROM users ORDER BY id;',
  'SELECT U.iD,upper(U.LaBeL),U.VaL FROM UsErS AS U WHERE u.ID>0 ORDER BY U.iD;',
  'SELECT UsErS.* FROM USERS WHERE Id=1;',
  'SELECT u.ID,t.KEY FROM USERS AS u JOIN TAGS AS t ON u.ID=t.OWNER ORDER BY u.ID;',
  'SELECT LABEL,count(*) FROM USERS GROUP BY label ORDER BY Label;',
  "UPDATE UsErS SET LABEL=label||'x' WHERE Id=1 RETURNING users.ID,Label;",
  "INSERT INTO USERS(ID,LABEL,VAL) VALUES(3,'new',30) RETURNING users.id,label;",
  "INSERT OR REPLACE INTO TAGS(KEY,OWNER) VALUES('a',2) RETURNING rowid,key,owner;",
  'DELETE FROM uSeRs WHERE ID=1 RETURNING id,Label;',
  'CREATE INDEX "MixedIndex" ON "UsErS"("LABEL");',
  'DROP INDEX labelINDEX;',
  'CREATE TABLE IF NOT EXISTS USERS(Other);',
  'CREATE INDEX IF NOT EXISTS LABELINDEX ON USERS(missing);',
  'CREATE TABLE USERS(Other);',
  'CREATE INDEX USERS ON USERS(ID);',
  'CREATE TABLE labelINDEX(Other);',
  'CREATE TABLE "More"("ID" INTEGER PRIMARY KEY,"VaLuE" TEXT);\nINSERT INTO more VALUES(1,\'new\');\nSELECT id,value FROM MORE;',
  'CREATE TABLE "MiXeD Table"("KeY" TEXT PRIMARY KEY,"VaLuE" TEXT);\nINSERT INTO "mixed table" VALUES(\'a\',\'value\');\nSELECT key,value FROM "MIXED TABLE";',
  'DROP TABLE tAgS;',
  'CREATE TABLE bad("ID",id);',
  'BEGIN;\nUPDATE USERS SET Label=upper(label);\nROLLBACK;',
  'BEGIN;\nUPDATE USERS SET Label=upper(label);\nCOMMIT;',
  'SELECT sum(VAL),min(ID),max(ID),count(LABEL) FROM UsErS;',
  'SELECT ID FROM users UNION ALL SELECT OWNER FROM TAGS ORDER BY id;',
  'CREATE INDEX "OtherIndex" ON UsErS(LaBeL);\nDROP INDEX OTHERindex;',
  'DROP INDEX SQLITE_AUTOINDEX_TAGS_1;',
  'DROP TABLE IF EXISTS SQLITE_SCHEMA;',
  'CREATE TABLE SQLITE_New(v);',
  'CREATE TABLE "Ä"("Ä","ä");\nCREATE TABLE "ä"(v);\nINSERT INTO "Ä" VALUES(1,2);\nINSERT INTO "ä" VALUES(3);\nSELECT "Ä","ä" FROM "Ä";\nSELECT v FROM "ä";',
  'CREATE TABLE "ShAdOw"("RoWiD" TEXT,Id INTEGER PRIMARY KEY);\nINSERT INTO shadow(rowid,id) VALUES(\'text\',4);\nSELECT ROWID,OID,Id FROM SHADOW;',
  'CREATE TABLE "Quo""Ted"("Va""Lue");\nINSERT INTO "qUO""tED" VALUES(1);\nSELECT "va""LUE" FROM "QUO""TED";']
 def case_name(name):return ''.join(ch.upper() if rng.getrandbits(1) else ch.lower() for ch in name)
 for _ in range(a.random_cases):
  target=case_name('users');key=case_name('id');label=case_name('label')
  queries.append(rng.choice([f"UPDATE {target} SET {label}={label}||'{rng.randrange(1000)}' WHERE {key}={rng.randrange(1,4)} RETURNING {key},{label};",f"SELECT {key},{label} FROM {target} WHERE {key}>{rng.randrange(3)} ORDER BY {key};"]))
 with tempfile.TemporaryDirectory(prefix='sqleanite-schema-case-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][(fixture//3)%3];upper_table=fixture%3!=0;upper_column=fixture%3!=1
   table='Users' if upper_table else 'users';tags='Tags' if upper_table else 'tags';index='LabelIndex' if upper_table else 'labelindex'
   cols=['Id','Label','Val'] if upper_column else ['id','label','val'];tc=['Key','Owner'] if upper_column else ['key','owner'];base=Path(tmp)/f'base{fixture}.db'
   setup=f'PRAGMA page_size={page};CREATE TABLE {ident(table)}({ident(cols[0])} INTEGER PRIMARY KEY,{ident(cols[1])} TEXT,{ident(cols[2])} INTEGER);CREATE INDEX {ident(index)} ON {ident(table.swapcase())}({ident(cols[1].swapcase())});CREATE TABLE {ident(tags)}({ident(tc[0])} TEXT PRIMARY KEY,{ident(tc[1])} INTEGER);'
   setup+=f"INSERT INTO {ident(table)} VALUES(1,'value-{rng.getrandbits(32):08x}',10),(2,'value-{rng.getrandbits(32):08x}',20);INSERT INTO {ident(tags)} VALUES('a',1),('b',2);"
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=csql(ref,sql);lo=observe(lean);ro=observe(ref)
     matched=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     item=dict(fixture=fixture,page_size=page,upper_table=upper_table,upper_column=upper_column,mode=mode,sql=sql,lean=l,sqlite=r,observed_lean=lo,observed_sqlite=ro,matched=matched)
     if r['code'] and '\n' not in sql:item['failed_statement_bytes_unchanged']=before==hashes(lean);item['matched'] &= item['failed_statement_bytes_unchanged']
     follow="INSERT INTO uSeRs(iD,lAbEl,vAl) VALUES(NULL,'c-followup-%08x',99);"%rng.getrandbits(32)
     lf=csql(lean,follow);rf=csql(ref,follow)
     reopen_sql='SELECT rowid,id,typeof(label),hex(label),val FROM USERS ORDER BY ID;'
     lr=run([binary,mode,str(lean)],reopen_sql);rr=csql(ref,reopen_sql)
     after_l=observe(lean);after_r=observe(ref)
     item.update(c_followup_lean=lf,c_followup_sqlite=rf,reopened_lean=lr,reopened_sqlite=rr,after_followup_lean=after_l,after_followup_sqlite=after_r)
     item['matched'] &= lf['code']==rf['code']==0 and lf['stdout']==rf['stdout'] and lr['code']==rr['code']==0 and lr['stdout']==rr['stdout'] and after_l['code']==after_r['code']==0 and after_l['stdout']==after_r['stdout'] and after_l['stdout'].startswith('ok\n')
     cases.append(item)
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
