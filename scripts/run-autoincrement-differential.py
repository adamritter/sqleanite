#!/usr/bin/env python3
"""AUTOINCREMENT sequence state, ignored rows, transactions and C file interchange.

Compare complete successful output, error status, typed persisted rows and C
integrity. C then performs duplicate-key writes to test preserved constraint semantics.
This is a scoped SQL/file regression, not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354250);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
 queries=[]
 variants=[
  'id INTEGER PRIMARY KEY AUTOINCREMENT,v',
  'id INTEGER PRIMARY KEY ON CONFLICT IGNORE AUTOINCREMENT,v',
  'id INTEGER NOT NULL ON CONFLICT IGNORE PRIMARY KEY ON CONFLICT REPLACE AUTOINCREMENT,v',
  'id INTEGER PRIMARY KEY AUTOINCREMENT DEFAULT 99,v',
  'id INTEGER,v,PRIMARY KEY(id AUTOINCREMENT)',
  'id INTEGER,v,PRIMARY KEY(id DESC AUTOINCREMENT) ON CONFLICT IGNORE',
 ]
 for definition in variants:
  queries.append(f"CREATE TABLE Extra({definition});\nINSERT INTO Extra(v) VALUES('first'),('second');\nDELETE FROM Extra WHERE id=2;\nINSERT INTO Extra(v) VALUES('third') RETURNING id,v;\nSELECT * FROM sqlite_sequence ORDER BY rowid;\nSELECT * FROM Extra ORDER BY id;")
  queries.append(f"CREATE TABLE Extra({definition});\nINSERT INTO Extra VALUES(37,'explicit');\nDELETE FROM Extra;\nBEGIN;\nINSERT INTO Extra(v) VALUES('rollback');\nROLLBACK;\nINSERT INTO Extra(v) VALUES('committed');\nSELECT * FROM sqlite_sequence ORDER BY rowid;\nSELECT * FROM Extra ORDER BY id;")
 scenarios=[
  "INSERT INTO Extra(v) SELECT 7 WHERE 0;",
  "INSERT INTO Extra(v) SELECT seq FROM sqlite_sequence WHERE name='Extra';",
  "INSERT INTO Extra VALUES(-7,'negative');INSERT INTO Extra(v) VALUES('automatic');",
  "INSERT OR IGNORE INTO Extra(v) VALUES(NULL);",
  "CREATE UNIQUE INDEX ExtraV ON Extra(v);INSERT INTO Extra(v) VALUES('same');INSERT OR IGNORE INTO Extra(v) VALUES('same'),('same');INSERT INTO Extra(v) VALUES('next');",
  "CREATE UNIQUE INDEX ExtraV ON Extra(v);INSERT INTO Extra(v) VALUES('same');INSERT OR REPLACE INTO Extra(v) VALUES('same');",
  "INSERT INTO Extra(v) VALUES('first');UPDATE Extra SET id=37;",
  "INSERT INTO sqlite_sequence VALUES('Extra','17extra');INSERT INTO Extra(v) VALUES('next');",
  "INSERT INTO sqlite_sequence VALUES('Extra',-9);INSERT INTO Extra VALUES(-7,'negative');INSERT INTO Extra(v) VALUES('next');",
  "INSERT INTO sqlite_sequence VALUES('Extra',7),('Extra',17);INSERT INTO Extra(v) VALUES('next');",
  "INSERT INTO Extra VALUES(99,'high');DELETE FROM Extra;DELETE FROM sqlite_sequence WHERE name='Extra';INSERT INTO Extra(v) VALUES('reset');",
  "INSERT INTO Extra VALUES(9223372036854775807,'maximum');DELETE FROM Extra;INSERT INTO Extra(v) VALUES('full');",
  "INSERT INTO sqlite_sequence VALUES('Extra',NULL);INSERT INTO Extra(v) SELECT 7 WHERE 0;",
  "INSERT INTO sqlite_sequence VALUES('Extra','17extra');INSERT INTO Extra VALUES(5,'lower');",
  "INSERT INTO sqlite_sequence VALUES('Extra',X'3137');INSERT INTO Extra(v) VALUES('next');",
  "INSERT INTO sqlite_sequence VALUES('Extra',1e999);INSERT INTO Extra(v) VALUES('full');",
  "INSERT INTO sqlite_sequence VALUES('extra',99);INSERT INTO Extra(v) VALUES('case-sensitive');",
  "INSERT INTO Extra(v) VALUES('first');ALTER TABLE Extra RENAME TO Renamed;INSERT INTO Renamed(v) VALUES('next');",
  "INSERT INTO Extra(v) VALUES('first');DROP TABLE Extra;",
  "INSERT INTO Extra(v) SELECT seq FROM sqlite_sequence WHERE name='Extra';INSERT INTO Extra(v) SELECT seq FROM sqlite_sequence WHERE name='Extra' RETURNING id,v;",
  "INSERT INTO Extra(v) VALUES('first');ALTER TABLE Extra RENAME COLUMN id TO key;INSERT INTO Extra(v) VALUES('next') RETURNING key,v;",
  "INSERT INTO Extra(v) VALUES('first');ALTER TABLE Extra ADD flag TEXT DEFAULT 'yes';INSERT INTO Extra(v) VALUES('next') RETURNING *;",
  "INSERT INTO Extra(v) VALUES('first');ALTER TABLE Extra DROP COLUMN v;INSERT INTO Extra DEFAULT VALUES;",
  "BEGIN;INSERT INTO Extra(v) VALUES('first');INSERT OR IGNORE INTO Extra(v) VALUES(NULL);ROLLBACK;INSERT INTO Extra(v) VALUES('after');",
  "INSERT INTO Extra(v) SELECT 'selected' UNION ALL SELECT NULL RETURNING id,v;",
  "INSERT OR IGNORE INTO Extra(v) SELECT 'selected' UNION ALL SELECT NULL RETURNING id,v;",
  "INSERT INTO Extra(id,v) VALUES('7.0','converted'),(NULL,'generated') RETURNING id,v;",
  "INSERT INTO Extra(id,v) VALUES(1.5,'invalid');",
  "INSERT OR IGNORE INTO Extra(id,v) VALUES(1.5,'invalid');",
  "INSERT INTO sqlite_sequence VALUES('Extra','17extra');INSERT OR IGNORE INTO Extra(id,v) VALUES(5,NULL);",
  "INSERT INTO sqlite_sequence VALUES('Extra',17.9);INSERT INTO Extra(v) VALUES('real');",
  "INSERT INTO sqlite_sequence VALUES('Extra',-1e999);INSERT INTO Extra(v) VALUES('negative infinity');",
  "CREATE TABLE Ordinary(k);INSERT INTO sqlite_sequence VALUES('Ordinary',7);ALTER TABLE Ordinary RENAME TO OrdinaryNew;DROP TABLE OrdinaryNew;",
  "INSERT INTO Extra(v) VALUES('first');INSERT INTO sqlite_sequence VALUES('Extra',17);ALTER TABLE Extra RENAME TO Renamed;",
  "CREATE INDEX seqname ON sqlite_sequence(name);",
  "CREATE UNIQUE INDEX seqname ON sqlite_sequence(seq);",
  "DROP TABLE sqlite_sequence;",
  "ALTER TABLE sqlite_sequence RENAME TO Sequence;",
  "ALTER TABLE sqlite_sequence ADD extra;",
  "ALTER TABLE sqlite_sequence RENAME COLUMN seq TO counter;",
  "ALTER TABLE sqlite_sequence DROP COLUMN seq;",
 ]
 for scenario in scenarios:
  queries.append("CREATE TABLE Extra(id INTEGER PRIMARY KEY AUTOINCREMENT,v NOT NULL);\n"+scenario.replace(';',';\n')+"\nSELECT rowid,typeof(name),hex(name),typeof(seq),hex(seq) FROM sqlite_sequence ORDER BY rowid;")
 for declaration in ['id INT PRIMARY KEY AUTOINCREMENT,v','id INTEGER AUTOINCREMENT PRIMARY KEY,v','id INTEGER PRIMARY KEY AUTOINCREMENT ON CONFLICT IGNORE,v','id INTEGER PRIMARY KEY AUTOINCREMENT AUTOINCREMENT,v','id INTEGER,v,PRIMARY KEY(id AUTOINCREMENT DESC)','id INTEGER PRIMARY KEY DESC AUTOINCREMENT,v']:
  queries.append('CREATE TABLE Extra('+declaration+');')
 queries.extend([
  "BEGIN;\nCREATE TABLE Extra(id INTEGER PRIMARY KEY AUTOINCREMENT,v);\nINSERT INTO Extra(v) VALUES('inside');\nROLLBACK;\nSELECT * FROM Users ORDER BY rowid;",
  "CREATE TABLE Extra(id INTEGER PRIMARY KEY AUTOINCREMENT,v NOT NULL ON CONFLICT REPLACE DEFAULT 'fallback');\nINSERT INTO Extra(v) VALUES(NULL),('given') RETURNING id,v;\nSELECT * FROM sqlite_sequence ORDER BY rowid;",
  "CREATE TABLE Extra(id INTEGER PRIMARY KEY AUTOINCREMENT,v NOT NULL ON CONFLICT IGNORE);\nINSERT INTO Extra(v) VALUES(NULL),('given'),(NULL) RETURNING id,v;\nSELECT * FROM sqlite_sequence ORDER BY rowid;",
  "CREATE TABLE Extra(id INTEGER PRIMARY KEY AUTOINCREMENT,v);\nINSERT INTO Extra(v) VALUES('first');\nDELETE FROM Extra;\nINSERT INTO Extra(v) VALUES('again');\nSELECT * FROM sqlite_sequence ORDER BY rowid;",
 ])
 for _ in range(a.random_cases):
  value=rng.randrange(2,1000000)
  queries.append(f"CREATE TABLE Extra(id INTEGER PRIMARY KEY AUTOINCREMENT,v);\nINSERT INTO Extra VALUES({value},'high');\nDELETE FROM Extra;\nINSERT INTO Extra(v) VALUES('next'),('again') RETURNING id,v;\nSELECT * FROM sqlite_sequence ORDER BY rowid;")
 with tempfile.TemporaryDirectory(prefix='sqleanite-autoincrement-') as tmp:
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
    setup+="CREATE TABLE Imported(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO Imported VALUES(37,'historical');DELETE FROM Imported;"
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
     extra_followups=[]
     present=tables['stdout'].encode('latin1').decode('utf8').splitlines()
     for target in ['Extra','Renamed','Imported']:
      if target in present:
       follow_sql='INSERT INTO '+ident(target)+' DEFAULT VALUES;'
       left=csql(lean,follow_sql);right=csql(ref,follow_sql)
       extra_followups.append(dict(sql=follow_sql,lean=left,sqlite=right))
       item['matched'] &= ((left['code']!=0 and right['code']!=0) or (left['code']==right['code']==0 and left['stdout']==right['stdout']))
     item['c_auto_followups']=extra_followups
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
