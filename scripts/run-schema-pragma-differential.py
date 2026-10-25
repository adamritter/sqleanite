#!/usr/bin/env python3
"""Schema PRAGMA output bytes, read immutability and C-mutation/Lean reopen.

The reference is the pinned SQLite CLI. Every fixture has a distinct seed-derived
payload and checks both public file modes; result order and names are not
normalized. This measures the listed metadata pragmas, not full SQL equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354160);p.add_argument('--fixtures',type=int,default=9);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([a.sqlite,'-batch','-bail',str(path)],sql)
 def ident(s):return '"'+s.replace('"','""')+'"'
 def literal(s):return "'"+s.replace("'","''")+"'"
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=[]
 for pragma,names in [('table_info',['Users','Tags','Odd.Name','missing','sqlite_schema']),('table_xinfo',['Users','Tags','Odd.Name','missing']),('index_list',['Users','Tags','Odd.Name','missing']),('index_info',['LabelIndex','ValueIndex','sqlite_autoindex_Tags_1','missing']),('index_xinfo',['LabelIndex','ValueIndex','sqlite_autoindex_Tags_1','missing'])]:
  for name in names:queries.append('PRAGMA '+pragma+'('+literal(name)+');')
  queries.extend(['PRAGMA '+pragma+';','PRAGMA '+pragma+'='+literal(names[0])+';'])
 queries.extend(["PRAGMA table_info('');", "PRAGMA table_xinfo(sqlite_master);", "PRAGMA table_info(sqlite_temp_schema);", "PRAGMA index_info('');", "PRAGMA index_xinfo('');", "PRAGMA index_list('');", "PRAGMA table_info('Ä');", "PRAGMA table_info('ä');", "PRAGMA table_info('Quoted\"Name');", "PRAGMA table_info(('Users'));", "PRAGMA table_info=(Users);", "PRAGMA table_info(CAST('Users' AS TEXT));", "PRAGMA table_info(Users COLLATE binary);", "PRAGMA table_info('Users','Tags');", "PRAGMA table_info='Users');", "PRAGMA table_info('Users';"])
 queries.extend('PRAGMA table_info('+word+');' for word in ['select','where','index','table','commit','returning','on','off','default','delete'])
 for _ in range(a.random_cases):
  pragma=rng.choice(['table_info','table_xinfo','index_list','index_info','index_xinfo']);name=rng.choice(['Users','Tags','Odd.Name','LabelIndex','ValueIndex','sqlite_autoindex_Tags_1','missing',''])
  pragma=''.join(c.upper() if rng.getrandbits(1) else c for c in pragma);name=''.join(c.upper() if rng.getrandbits(1) else c.lower() for c in name)
  spelling=rng.choice([ident(name),literal(name)])
  queries.append('PRAGMA '+pragma+rng.choice(['('+spelling+')','='+spelling])+';')
 with tempfile.TemporaryDirectory(prefix='sqleanite-schema-pragma-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3];base=Path(tmp)/f'base{fixture}.db'
   primary='INTEGER PRIMARY KEY'+(' NOT NULL' if fixture%2 else '')
   columns=['Id '+primary,'Label text NOT NULL','Val numeric','EmptyType','Mixed varchar(17)','Floaty real','AnyType any','Inty int','Bytes blob'];shift=(fixture//3)%3;columns=columns[shift:]+columns[:shift]
   setup=f'PRAGMA page_size={page};CREATE TABLE Users('+','.join(columns)+');CREATE INDEX LabelIndex ON Users(Label);CREATE UNIQUE INDEX ValueIndex ON Users(Val);CREATE TABLE Tags(Key TEXT PRIMARY KEY,Owner INTEGER);CREATE TABLE "Odd.Name"("" TEXT,"a""b" BLOB);'
   setup+=f"INSERT INTO Users(Id,Label,Val) VALUES(1,'payload-{rng.getrandbits(64):016x}',7);INSERT INTO Tags VALUES(NULL,1),('tag',1);"
   setup+='CREATE TABLE "Ä"(a);CREATE TABLE "Quoted""Name"(v);'
   setup+=('CREATE TABLE ""(x INTEGER);' if fixture%2==0 else 'CREATE INDEX "" ON "Odd.Name"("");')
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     lean=Path(tmp)/f'lean{len(cases)}.db';ref=Path(tmp)/f'ref{len(cases)}.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=csql(ref,sql);unchanged=before==hashes(lean)
     follow='ALTER TABLE Users ADD NewCol REAL;DROP INDEX LabelIndex;CREATE INDEX Replacement ON Users(NewCol);'
     lf=csql(lean,follow);rf=csql(ref,follow)
     lr=run([binary,mode,str(lean)],sql);rr=csql(ref,sql)
     equivalent=lambda left,right:(left['code']!=0 and right['code']!=0) or (left['code']==right['code']==0 and left['stdout']==right['stdout'])
     matched=equivalent(l,r) and unchanged and lf['code']==rf['code']==0 and equivalent(lr,rr)
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,read_bytes_unchanged=unchanged,c_followup_sql=follow,c_followup_lean=lf,c_followup_sqlite=rf,reopened_lean=lr,reopened_sqlite=rr,matched=matched))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
