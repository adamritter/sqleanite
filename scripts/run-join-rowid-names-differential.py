#!/usr/bin/env python3
"""Compare declared rowid names taking priority across joined sources.

Qualified names retain source-local fallback; unqualified names first match all
declared columns, then consider implicit rowid aliases. Compare output/error
status, CTAS metadata/typed rows, C integrity and follow-up writes, and Lean
reopening in both file modes. Every mismatch is retained.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354430);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
 def queries(alias):
  result=[]
  for source in ['l a,r b','l a LEFT JOIN r b ON a.id=b.id','l a NATURAL LEFT JOIN r b',f'l a JOIN r b USING({alias})']:
   for projection in [alias,'"'+alias+'"',f'{alias},a.id,b.id',f'a.{alias},b.{alias}',f'{alias} AS chosen,a.id,b.id']:
    result.append(f'SELECT {projection} FROM {source} ORDER BY a.id,b.id;')
    result.append(f'CREATE TABLE Extra AS SELECT {projection} FROM {source} ORDER BY a.id,b.id;')
   for clause in [f'WHERE {alias} IS NULL',f'WHERE {alias}=1',f'WHERE {alias}=a.id',f'ORDER BY {alias}',f'ORDER BY "{alias}" DESC','LIMIT 0']:
    result.append(f'SELECT {alias},a.id,b.id FROM {source} {clause};')
   result.append(f'SELECT a.*,b.* FROM {source} ORDER BY {alias};')
  for source in ['l a,r b','l a CROSS JOIN r b',f'l a JOIN r b ON a.id=b.{alias}']:
   for condition in [f'a.id=b.{alias}',f'b.{alias}=a.id',f'a.id=b.{alias} AND b.id>0']:
    for tail in ['', ' ORDER BY a.id', ' ORDER BY a.id DESC', ' ORDER BY b.id DESC,a.k', ' LIMIT 2 OFFSET 1']:
     result.append(f'SELECT {alias},a.id,b.id FROM {source} WHERE {condition}{tail};')
  for other in ['rowid','oid','_rowid_']:
   result.append(f'SELECT {other} FROM l a,r b ORDER BY a.id,b.id;')
  for _ in range(a.random_cases):
   op=rng.choice(['=','<>','<','>','<=','>=']);number=rng.randrange(-2,12)
   result.append(f'SELECT {alias},a.id,b.id FROM l a LEFT JOIN r b ON a.id=b.id WHERE {alias}{op}{number} ORDER BY a.id,b.id;')
  return result
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-rowid-names-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3]
   base=Path(tmp)/f'base{fixture}.db'
   left_type=['INTEGER','TEXT','BLOB','NUMERIC','REAL',''][fixture%6]
   right_type=['TEXT','NUMERIC','INTEGER','BLOB','','REAL'][fixture%6]
   left_name='K' if fixture%2 else 'k';right_name='ID' if fixture%2 else 'id'
   left_key='TEXT' if fixture%2 else 'INTEGER'
   alias=['rowid','oid','_rowid_'][(fixture//4)%3]
   left_extra=fixture%4 in [1,3];right_extra=fixture%4 in [2,3]
   left_decl=f',{alias} TEXT' if left_extra else ''
   right_decl=f',{alias.upper()} NUMERIC' if right_extra else ''
   setup=f"PRAGMA page_size={page};CREATE TABLE l(id {left_key} PRIMARY KEY,{left_name} {left_type},left_only TEXT{left_decl});CREATE TABLE r({right_name} INTEGER PRIMARY KEY,k {right_type},right_only TEXT{right_decl});"
   counts=(rng.randrange(0,7),rng.randrange(0,7))
   for table,count,extra in [('l',counts[0],left_extra),('r',counts[1],right_extra)]:
    for i in range(1,count+1):
     value=rng.choice(['NULL','1','2',"'01'","'2'","'a'","'A'"])
     extra_value=','+rng.choice(['NULL','1','2',"'01'","'2'","'a'"]) if extra else ''
     setup+=f"INSERT INTO {table} VALUES({i},{value},'{table}-{i}'{extra_value});"
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries(alias):
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean);before_ref=hashes(ref)
     l=run([binary,mode,str(lean)],sql);r=csql(ref,sql);after_lean_sql=hashes(lean);after_ref_sql=hashes(ref);lo=observe(lean);ro=observe(ref)
     matched=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     item=dict(fixture=fixture,page_size=page,schema_sql=setup,mode=mode,sql=sql,lean=l,sqlite=r,observed_lean=lo,observed_sqlite=ro,matched=matched)
     item.update(main_wal_unchanged_lean=before==after_lean_sql,main_wal_unchanged_sqlite=before_ref==after_ref_sql)
     if before_ref==after_ref_sql:item['matched'] &= before==after_lean_sql
     if r['code']:
      item.update(failed_batch_image_unchanged_lean=before==after_lean_sql,failed_batch_image_unchanged_sqlite=before_ref==after_ref_sql)
      if before_ref==after_ref_sql:item['matched'] &= before==after_lean_sql
     follow="INSERT INTO l(id,k,left_only) VALUES(1,'1','follow');"
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
