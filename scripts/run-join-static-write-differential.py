#!/usr/bin/env python3
"""Compare persisted statically decided joined conditions and required errors.

Complete successful output/error status, C metadata/typed rows, integrity,
follow-up C writes and Lean reopening in both file modes. Keep every mismatch.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354493);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
 predicates=['0 AND abs(-9223372036854775808)','1 OR abs(-9223372036854775808)',
  'abs(-9223372036854775808) OR 1','abs(a.k) IN ()','abs(a.k) NOT IN ()',
  "0 AND json_extract(a.k,'$')",'1 OR random()',"1 OR min(a.k COLLATE missing,'x')",
  "0 AND min(a.k COLLATE missing,'x')",'0 AND not_a_function(a.k)',
  '0 AND coalesce(missing,1)','1 OR sum(a.k)','0 AND abs(a.k,a.k)',
  '1 OR likelihood(a.k,2.0)','0 AND abs(true)','1 AND 0 AND abs(b.k)']
 queries=[]
 for predicate in predicates:
  for source,where in [('l a JOIN r b ON '+predicate,''),('l a LEFT JOIN r b ON '+predicate,''),
    ('l a CROSS JOIN r b',' WHERE '+predicate),('l a LEFT JOIN r b ON a.id=b.id',' WHERE '+predicate)]:
   select=f'SELECT a.id AS left_id,b.id AS right_id,a.k AS left_value,b.k AS right_value FROM {source}{where} ORDER BY a.id,b.id'
   queries += ['CREATE TABLE Extra AS '+select+';',
    'CREATE TABLE Extra AS '+select+' LIMIT 0;\nINSERT INTO Extra '+select+' LIMIT 2 OFFSET 1;']
 for _ in range(a.random_cases):
  first=rng.choice(predicates);second=rng.choice(predicates);operator=rng.choice(['AND','OR'])
  queries.append(f'CREATE TABLE Extra AS SELECT a.id,b.id,a.k,b.k FROM l a LEFT JOIN r b ON ({first}) {operator} ({second}) ORDER BY a.id,b.id LIMIT {rng.randrange(0,8)} OFFSET {rng.randrange(0,8)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-static-write-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3]
   base=Path(tmp)/f'base{fixture}.db'
   left_type=['INTEGER','TEXT','BLOB','NUMERIC','REAL',''][fixture%6]
   right_type=['TEXT','NUMERIC','INTEGER','BLOB','','REAL'][fixture%6]
   left_name='K' if fixture%2 else 'k';right_name='ID' if fixture%2 else 'id'
   left_key='TEXT' if fixture%2 else 'INTEGER'
   left_bool=',"true"' if fixture%3 else ''
   right_bool=(',"false"' if fixture%3==1 else ',"true"') if fixture%3 else '' 
   setup=f"PRAGMA page_size={page};CREATE TABLE l(id {left_key} PRIMARY KEY,{left_name} {left_type},left_only TEXT{left_bool});CREATE TABLE r({right_name} INTEGER PRIMARY KEY,k {right_type},right_only TEXT{right_bool});CREATE TABLE n(other_id INTEGER PRIMARY KEY,z);INSERT INTO n VALUES(1,'z');"
   counts=[(3,4),(0,4),(3,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(1,8),rng.randrange(1,8))
   for table,count in zip(['l','r'],counts):
    for i in range(1,count+1):
     value=rng.choice(['NULL','0','1','2','-0.0','0.5',"'01'","'2'","'a'","'A'","'a '","'A  '","'1tail'","X'302E35FF'","CAST(X'3100FF' AS TEXT)","CAST(X'FF31' AS TEXT)"])
     extra=','+str((count-i) if table=='l' else i) if fixture%3 else ''
     setup+=f"INSERT INTO {table} VALUES({i},{value},'{table}-{i}'{extra});"
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
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
