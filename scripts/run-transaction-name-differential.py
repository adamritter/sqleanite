#!/usr/bin/env python3
"""SQLite DEFERRED transactions and ignored TRANSACTION names.

Each complete statement is sent on a separate input line so -bail stops before
the next statement. Same-line C-shell continuation is a distinct retained
negative diagnostic, not removed from its original reports. No lock-mode claim.

Compare all output, including prefixes before an error, error status, typed persisted rows and C
integrity. C then performs duplicate-key writes to test preserved constraint semantics.
This is a scoped SQL/file regression, not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354320);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
 names=['select','commit','check','constraint','transaction','autoincrement','null','on','delete','default','primary',
  'join','indexed','left','right','full','inner','outer','cross','natural','begin','end','rollback','release',
  'savepoint','window','filter','over','with','1',"'select'",'"select"',"''",'""','`label`','[label]',
  'offset','deferred','immediate','exclusive','É',"'semi;colon'"]
 names += ['name_'+str(rng.randrange(10000000)) for _ in range(a.random_cases)]
 queries=[]
 for name in names:
  update='UPDATE Users SET Val=73 WHERE Id=1;'
  read='SELECT Id,Val FROM Users ORDER BY Id;'
  queries += [
   f'BEGIN TRANSACTION {name};{update}COMMIT;'+read,
   f'BEGIN;{update}COMMIT TRANSACTION {name};'+read,
   f'BEGIN;{update}END TRANSACTION {name};'+read,
   f'BEGIN;{update}ROLLBACK TRANSACTION {name};'+read,
   f'BEGIN;SAVEPOINT s;{update}ROLLBACK TRANSACTION {name} TO SAVEPOINT s;RELEASE s;COMMIT;'+read,
   f'BEGIN DEFERRED TRANSACTION {name};'+read+"END TRANSACTION 'different';",
  ]
 queries += [
  'BEGIN DEFERRED;SELECT 7;COMMIT;', 'BEGIN DEFERRED TRANSACTION;SELECT 8;ROLLBACK;',
  'BEGIN DEFERRED DEFERRED;SELECT 9;COMMIT;', 'BEGIN name;SELECT 9;COMMIT;',
  'BEGIN;COMMIT name;', 'BEGIN;END DEFERRED TRANSACTION;',
  'BEGIN TRANSACTION "to";SAVEPOINT s;ROLLBACK TRANSACTION "ignored" TO s;COMMIT TRANSACTION "anything";',
  'BEGIN TRANSACTION "first";SELECT 7;ROLLBACK TRANSACTION "different";',
 ]
 # Preserve quoted semicolons while giving each statement its own CLI input batch.
 # This changes only transport whitespace; both engines receive identical SQL.
 def separate_statements(sql):
  output=[];mode=None;i=0
  while i<len(sql):
   char=sql[i];output.append(char)
   if mode is not None:
    closing=']' if mode=='[' else mode
    if char==closing:
     if mode!='[' and i+1<len(sql) and sql[i+1]==closing:
      output.append(sql[i+1]);i+=1
     else:mode=None
   elif char in ["'",'"','`','[']:mode=char
   elif char==';':output.append('\n')
   i+=1
  return ''.join(output)
 queries=[separate_statements(sql) for sql in queries]
 with tempfile.TemporaryDirectory(prefix='sqleanite-transaction-name-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3]
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
    for sql,readonly in [(sql,readonly) for sql in queries for readonly in [False,True]]:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean);before_ref=hashes(ref)
     if readonly:lean.chmod(0o444);ref.chmod(0o444)
     l=run([binary,mode,str(lean)],sql);r=csql(ref,sql);after_lean_sql=hashes(lean);after_ref_sql=hashes(ref);lo=observe(lean);ro=observe(ref)
     matched=((l['code']!=0 and r['code']!=0) or l['code']==r['code']==0) and l['stdout']==r['stdout'] and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     item=dict(fixture=fixture,readonly=readonly,page_size=page,schema_sql=setup,mode=mode,sql=sql,lean=l,sqlite=r,observed_lean=lo,observed_sqlite=ro,matched=matched)
     if r['code']:
      item.update(failed_batch_image_unchanged_lean=before==after_lean_sql,failed_batch_image_unchanged_sqlite=before_ref==after_ref_sql)
      if before_ref==after_ref_sql:item['matched'] &= before==after_lean_sql
     if readonly:lean.chmod(0o644);ref.chmod(0o644)
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
 report=dict(input_batching='one complete statement per input line; original same-line negatives retained',seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
