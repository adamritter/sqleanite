#!/usr/bin/env python3
"""Public ordinary CREATE TABLE source retention versus pinned SQLite.

Generate admitted rowid tables, source spelling, comments, quoted identifiers,
defaults and mutation/transaction traces before either implementation runs.
Compare original results, complete catalog text, typed values, C integrity,
reopening, and a subsequent C write in both file modes. Templates are reused;
seeds generate new identifiers/values/comments. TEMP/STRICT/WITHOUT ROWID and
schema-altering/index-creation statements are separate outstanding surfaces.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('position',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--count',type=int,default=128);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  q=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=120);return dict(code=q.returncode,stdout=q.stdout.decode('latin1'),stderr=q.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def quote(s):return '"'+s.replace('"','""')+'"'
 def lexquote(s,style):return '['+s+']' if style=='[' else style+s.replace(style,style+style)+style
 def name():return ''.join(rng.choice('abAZ_019 é中";\'') for _ in range(rng.randrange(1,26)))
 types=['','TEXT','INTEGER','REAL','NUMERIC','BLOB','VARCHAR(19)','DOUBLE PRECISION']
 inputs=[]
 for i in range(a.count):
  table='t_'+name();column='v_'+name();style=rng.choice(['"',"'",'`','[']);tn=lexquote(table,style);cn=lexquote(column,rng.choice(['"',"'",'`','[']))
  default=rng.choice(["'a;''b'",'NULL','-23',"X'0080FF'",'2.25']);decl=rng.choice(types);auto=' AUTOINCREMENT' if i%13==0 else '';comment=' /* kept '+str(rng.randrange(10000000))+'; */ '
  body='(id INTEGER PRIMARY KEY'+auto+','+comment+cn+' '+decl+' DEFAULT ('+default+'))'
  create=rng.choice(['',' /* leading */ ','-- head\n'])+rng.choice(['CREATE TABLE ','create /**/ table ','CREATE TABLE IF NOT EXISTS ','CrEaTe /*prefix*/ TaBlE IF NOT EXISTS '])+tn+comment+body+'; -- ignored tail\n'
  t=quote(table);c=quote(column);select='SELECT rowid,typeof('+c+'),hex('+c+') FROM '+t+' ORDER BY rowid;'
  insert='INSERT INTO '+t+'(id) VALUES(1);';value="'"+('text '+str(rng.randrange(10000000)))+"'";update='UPDATE '+t+' SET '+c+'='+value+' WHERE id=1;'
  scenario=i%8
  if scenario==0:sql=create+select
  elif scenario==1:sql=create+insert+'\n'+update+'\n'+select
  elif scenario==2:sql='BEGIN;\n'+create+insert+'\nCOMMIT;\n'+select
  elif scenario==3:sql='BEGIN;\n'+create+insert+'\nROLLBACK;\n'+create+select
  elif scenario==4:sql=create+'CREATE TABLE IF NOT EXISTS '+t+'(different TEXT);\n'+insert+'\n'+select
  elif scenario==5:sql='SELECT count(*) FROM catalog_guard;\nSAVEPOINT s;\n'+create+insert+'\nROLLBACK TO s;\nRELEASE s;\n'+create+select
  elif scenario==6:sql=create+insert+'\nDELETE FROM '+t+';\n'+select
  else:sql=create+insert+'\nCREATE TABLE '+t+'(different TEXT);\n'+select
  observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;'+select
  follow='INSERT INTO '+t+' VALUES(99,'+value+');PRAGMA integrity_check;'+select
  inputs.append(dict(table=table,column=column,create=create,sql=sql,scenario=scenario,select=select,observe=observe,follow=follow,page_size=512<<(i%8)))
 cases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-create-catalog-') as tmp:
  folder=Path(tmp)
  for i,entry in enumerate(inputs):
   base=folder/(str(i)+'-base.db');made=csql(base,'PRAGMA page_size='+str(entry['page_size'])+';CREATE TABLE catalog_guard(id INTEGER PRIMARY KEY);');assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db');shutil.copyfile(base,left);shutil.copyfile(base,right)
    l,c=run([str(binary),mode,str(left)],entry['sql']),csql(right,entry['sql'])
    lo,co=csql(left,entry['observe']),csql(right,entry['observe']);lr,cr=run([str(binary),mode,str(left)],entry['select']),csql(right,entry['select']);lw,cw=csql(left,entry['follow']),csql(right,entry['follow'])
    matched=helpers.same(l,c) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stderr']==co['stderr']=='' and lo['stdout'].startswith('ok\n') and helpers.same(lr,cr) and lw['code']==cw['code']==0 and lw['stdout']==cw['stdout'] and lw['stderr']==cw['stderr']==''
    cases.append(dict(input=i,mode=mode,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,reopen_lean=lr,reopen_sqlite=cr,follow_lean=lw,follow_sqlite=cw,matched=matched))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 report=dict(seed=a.seed,inputs=inputs,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),comparison=__doc__.strip(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
