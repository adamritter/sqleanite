#!/usr/bin/env python3
"""ALTER ADD COLUMN: source rewrite, results/errors, storage and cross-engine use.

Preselected rowid-table definitions and ALTER traces include quoted Unicode
identifiers, table-level primary keys, expression defaults, comments, rollback
and trailing-line-comment failures. No outcome is filtered. Seeds generate
new names/values/comments within reused templates; this is not all SQL syntax.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('position',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--count',type=int,default=128);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  q=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=120);return dict(code=q.returncode,stdout=q.stdout.decode('latin1'),stderr=q.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def quote(s):return '"'+s.replace('"','""')+'"'
 def lexquote(s,style):return '['+s+']' if style=='[' else style+s.replace(style,style+style)+style
 def name():return ''.join(rng.choice('abAZ_019 é中";\'') for _ in range(rng.randrange(1,25)))
 types=['','TEXT','INTEGER','REAL','NUMERIC','BLOB','VARCHAR(19)','DOUBLE PRECISION'];inputs=[]
 for i in range(a.count):
  table='t_'+name();column='added_'+name();t=quote(table);tn=lexquote(table,rng.choice(['"',"'",'`','[']));cn=lexquote(column,rng.choice(['"',"'",'`','[']));c=quote(column)
  oldcomment=' /* original '+str(rng.randrange(10000000))+'; */ '
  body=rng.choice(['(id INTEGER PRIMARY KEY,v TEXT)', '(id INTEGER, v TEXT'+oldcomment+', PRIMARY KEY(id))','(id INTEGER, v TEXT, CONSTRAINT pk PRIMARY KEY(id))',"(id INTEGER PRIMARY KEY, v TEXT DEFAULT ('a;''b')"+oldcomment+')'])
  create='CREATE TABLE '+tn+oldcomment+body+';';initial=rng.randrange(1,99999);populate="INSERT INTO "+t+" VALUES(1,'old "+str(initial)+"');" if i%3 else ''
  decl=rng.choice(types);default=rng.choice(["'value "+str(rng.randrange(100000))+"'",'NULL',str(-rng.randrange(1,9999)),"X'0080FF'",'2.25']);definition=cn+' '+decl+' /* new '+str(rng.randrange(1000000))+' */ DEFAULT ('+default+')'
  ending=rng.choice([';',' /* ending */;',' -- final;\n;',' \t\n;'])
  alter=rng.choice(['ALTER TABLE ','alter /**/ table '])+tn+rng.choice([' ADD ',' ADD COLUMN '])+definition+ending
  scenario=i%5
  if scenario==0:sql=alter+'\nSELECT count(*) FROM '+t+';'
  elif scenario==1:sql='BEGIN;\n'+alter+'\nCOMMIT;\nSELECT count(*) FROM '+t+';'
  elif scenario==2:sql='BEGIN;\n'+alter+'\nROLLBACK;\n'+alter
  elif scenario==3:sql='SELECT count(*) FROM '+t+';\nSAVEPOINT s;\n'+alter+'\nROLLBACK TO s;\nRELEASE s;\n'+alter
  else:sql=alter+'\nUPDATE '+t+" SET v='changed';\n"
  # Universal observations remain valid whether ADD succeeds or errors.
  read='PRAGMA table_info('+t+');SELECT * FROM '+t+' ORDER BY id;'
  observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;'+read
  follow='INSERT INTO '+t+'(id,v) VALUES(99,\'follow\');PRAGMA integrity_check;'+read
  inputs.append(dict(table=table,column=column,create=create,populate=populate,sql=sql,scenario=scenario,read=read,observe=observe,follow=follow,page_size=512<<(i%8)))
 cases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-alter-catalog-') as tmp:
  folder=Path(tmp)
  for i,entry in enumerate(inputs):
   base=folder/(str(i)+'-base.db');made=csql(base,'PRAGMA page_size='+str(entry['page_size'])+';'+entry['create']+entry['populate']);assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db');shutil.copyfile(base,left);shutil.copyfile(base,right)
    l,c=run([str(binary),mode,str(left)],entry['sql']),csql(right,entry['sql'])
    lo,co=csql(left,entry['observe']),csql(right,entry['observe']);lr,cr=run([str(binary),mode,str(left)],entry['read']),csql(right,entry['read']);lw,cw=csql(left,entry['follow']),csql(right,entry['follow'])
    matched=helpers.same(l,c) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stderr']==co['stderr']=='' and lo['stdout'].startswith('ok\n') and helpers.same(lr,cr) and lw['code']==cw['code']==0 and lw['stdout']==cw['stdout'] and lw['stderr']==cw['stderr']==''
    cases.append(dict(input=i,mode=mode,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,reopen_lean=lr,reopen_sqlite=cr,follow_lean=lw,follow_sqlite=cw,matched=matched))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 report=dict(seed=a.seed,inputs=inputs,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),comparison=__doc__.strip(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
