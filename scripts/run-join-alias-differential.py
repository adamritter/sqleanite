#!/usr/bin/env python3
"""Compare joined output-alias resolution in WHERE and ON predicates.

Compare complete successful output, error status, independent C catalog/pragma/
typed-row/integrity observations, follow-up C writes and Lean reopening in both
file modes. Main/WAL bytes must stay unchanged whenever C leaves them unchanged.
Source names take priority; duplicate/quoted aliases and non-recursive substitution are checked. Every mismatch is retained.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354560);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
 sources=[f'l a {kind} r b ON a.id=b.id' for kind in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']]
 sources += [f'l a {kind} r b USING(k)' for kind in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']]
 expressions=['a.k','+a.k','a.k COLLATE nocase','likely(a.k)','k']
 conditions=['chosen=1',"chosen='01'",'chosen IS NULL',"chosen IN ('A',2,NULL)","+chosen='1'"]
 for source in sources:
  for expression in expressions:
   for condition in conditions:
    queries.append(f'SELECT {expression} AS chosen,a.id,b.id FROM {source} WHERE {condition} ORDER BY a.id,b.id;')
  for expression in ['a.k','k']:
   queries.append(f'CREATE TABLE Extra AS SELECT {expression} AS chosen FROM {source} WHERE chosen IS NOT NULL ORDER BY a.id,b.id;')
   queries.append(f'CREATE TABLE Extra AS SELECT {expression} AS chosen FROM {source} WHERE chosen=1 LIMIT 0;\nINSERT INTO Extra SELECT {expression} AS chosen FROM {source} WHERE chosen=1 ORDER BY a.id,b.id;')
  for tail in ['LIMIT 0','LIMIT 1 OFFSET 0']:
   queries.append(f"SELECT a.k AS chosen FROM {source} WHERE chosen COLLATE nocase='A' ORDER BY a.id,b.id {tail};")
 for kind in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']:
  for expression in ['a.k','+a.k','b.k','a.k COLLATE nocase','1','NULL']:
   for condition in ['chosen=b.k','chosen IS NULL','chosen','0 AND chosen']:
    queries.append(f'SELECT {expression} AS chosen,a.id,b.id FROM l a {kind} r b ON {condition} ORDER BY a.id,b.id;')
 for source in ['l a CROSS JOIN r b','l a FULL JOIN r b USING(k)']:
  for alias in ['chosen','k','id','true','false','rowid','label.name']:
   for expression in ['a.k','1']:
    quoted=ident(alias)
    queries.append(f'SELECT {expression} AS {quoted},a.id,b.id FROM {source} WHERE {quoted}=1 ORDER BY a.id,b.id;')
  for projection,condition in [
   ('1 AS chosen,0 AS chosen','chosen'),
   ('a.k AS chosen,b.k AS chosen','chosen=a.k'),
   ('a.k AS first,first AS second','second'),
   ('second AS first,first AS second','first'),
   ('a.k AS chosen','a.chosen'),
   ('a.k AS chosen','missing'),
   ('a.k AS chosen','0 AND missing'),
   ('not_a_function(a.k) AS chosen','0'),
   ('a.k COLLATE missing AS chosen','chosen=1'),
   ('a.k AS chosen','chosen=1 COLLATE missing')]:
   queries.append(f'SELECT {projection} FROM {source} WHERE {condition} ORDER BY a.id,b.id;')
 for alias in ['true','false']:
  for expression in ['0','1','b.k',alias]:
   for condition in [alias,f'{alias}=1',f'a.k IS {alias}']:
    queries.append(f'SELECT {expression} AS {alias},a.id,b.id FROM l a JOIN r b ON a.id=b.id WHERE {condition} ORDER BY a.id,b.id;')
  queries.append(f'SELECT a.k COLLATE missing AS {alias} FROM l a JOIN r b ON a.id=b.id WHERE {alias}=1 LIMIT 0;')
 for source in sources:
  for expression in ['a.k COLLATE nocase','k','1']:
   for order in ['chosen','+chosen','chosen COLLATE binary','1']:
    queries.append(f'SELECT {expression} AS chosen,a.id,b.id FROM {source} WHERE chosen IS NOT NULL ORDER BY {order},a.id,b.id;')
 for kind in ['LEFT JOIN','RIGHT JOIN','FULL JOIN']:
  for expression in ['a.k','b.k','NULL','1']:
   for condition in ['chosen AND a.id=b.id','a.id=b.id AND chosen','chosen AND chosen',
     'chosen OR a.id=b.id','+chosen','chosen COLLATE binary','likely(chosen)','(chosen)']:
    queries.append(f'SELECT {expression} AS chosen,a.id,b.id FROM l a {kind} r b ON {condition} ORDER BY a.id,b.id;')
   for condition in ['chosen AND a.id=b.id','a.id=b.id AND chosen']:
    queries.append(f'SELECT {expression} AS chosen,a.id,b.id FROM l a {kind} r b ON {condition} WHERE b.id IS NULL ORDER BY a.id,b.id;')
 for _ in range(a.random_cases):
  source=rng.choice(sources);expression=rng.choice(expressions);condition=rng.choice(conditions)
  queries.append(f'SELECT {expression} AS chosen,a.id,b.id FROM {source} WHERE {condition} ORDER BY a.id,b.id LIMIT {rng.randrange(0,8)} OFFSET {rng.randrange(0,3)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-alias-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3]
   base=Path(tmp)/f'base{fixture}.db'
   affinity_index=fixture if fixture<4 else fixture-2
   left_type=['INTEGER','TEXT','BLOB','NUMERIC','REAL',''][affinity_index%6]
   right_type=['TEXT','NUMERIC','INTEGER','BLOB','','REAL'][affinity_index%6]
   left_name='K' if fixture%2 else 'k';right_name='ID' if fixture%2 else 'id'
   left_key='TEXT' if fixture%2 else 'INTEGER'
   setup=f"PRAGMA page_size={page};CREATE TABLE l(id {left_key} PRIMARY KEY,{left_name} {left_type},left_only TEXT);CREATE TABLE r({right_name} INTEGER PRIMARY KEY,k {right_type},right_only TEXT);CREATE TABLE n(other_id INTEGER PRIMARY KEY,z);INSERT INTO n VALUES(1,'z');"
   counts=[(3,4),(0,4),(3,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(1,8),rng.randrange(1,8))
   if fixture==1:counts=(3,4)
   for table,count in zip(['l','r'],counts):
    for i in range(1,count+1):
     value=rng.choice(['NULL','0.0','1','2',"'01'","'2'","'a'","'A'","'a '","X'31'"])
     setup+=f"INSERT INTO {table} VALUES({i},{value},'{table}-{i}');"
   if fixture==2:setup+="ALTER TABLE l ADD COLUMN \"true\" INTEGER DEFAULT 1;ALTER TABLE r ADD COLUMN \"false\" TEXT DEFAULT '0';"
   if fixture==4:setup+='ALTER TABLE l ADD COLUMN "true" INTEGER DEFAULT 1;ALTER TABLE r ADD COLUMN "true" INTEGER DEFAULT 0;'
   if fixture==5:setup+='ALTER TABLE l ADD COLUMN "false" INTEGER DEFAULT 1;'
   if fixture==6:setup+='ALTER TABLE r ADD COLUMN "true" INTEGER DEFAULT 1;'
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
