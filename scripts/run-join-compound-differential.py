#!/usr/bin/env python3
"""Compare joined compound result slots and ORDER BY source/name binding.

Compare complete successful output, error status, independent C catalog/pragma/
typed-row/integrity observations, follow-up C writes and Lean reopening in both
file modes. Main/WAL bytes must stay unchanged whenever C leaves them unchanged.
Stars, USING/NATURAL, merged outer columns, expression identity, aliases, set operations and writes are checked. Every mismatch is retained.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354570);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
 sources=[]
 for kind in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']:
  sources.extend([(f'l a {kind} r b ON a.id=b.id',6),(f'l a {kind} r b USING(id)',5),
   (f'l a {kind} r b USING(k)',5),(f'l a NATURAL {kind} r b',4)])
 shapes=[]
 for source,width in sources:
  for projection,count in [('*',width),('a.*',3),('b.*',3),('a.*,b.*',6)]:
   shapes.append((source,projection,count))
   for order in ['1',str(count),str(count+1),'id','k','a.k','b.k','left_only','right_only']:
    queries.append(f'SELECT {projection} FROM {source} UNION ALL SELECT '+','.join(str(90+i) for i in range(count))+f' ORDER BY {order};')
  for operation in ['UNION','INTERSECT','EXCEPT']:
   for order in ['k','b.k','id COLLATE nocase']:
    queries.append(f'SELECT * FROM {source} {operation} SELECT * FROM {source} ORDER BY {order};')
  for projection,count in [('*',width),('a.*',3),('b.*',3)]:
   tail=' UNION ALL SELECT '+','.join(str(90+i) for i in range(count))+' ORDER BY k;'
   queries.append(f'CREATE TABLE Extra AS SELECT {projection} FROM {source}'+tail)
   queries.append(f'CREATE TABLE Extra AS SELECT {projection} FROM {source} LIMIT 0;\nINSERT INTO Extra SELECT {projection} FROM {source}'+tail)
  for projection in ['a.k','b.k','k','+a.k','likely(a.k)','a.k COLLATE nocase','a.k AS chosen','a.k AS chosen,b.k AS chosen']:
   count=2 if ',' in projection else 1
   for order in ['k','a.k','b.k','chosen','+a.k','likely(a.k)','coalesce(a.k,b.k)']:
    queries.append(f'SELECT {projection} FROM {source} UNION ALL SELECT '+','.join('NULL' for _ in range(count))+f' ORDER BY {order};')
  for order in ['a.id','b.id','coalesce(a.id,b.id)','id COLLATE missing','missing','0']:
   queries.append(f'SELECT a.* FROM {source} UNION ALL SELECT 1,2,3 ORDER BY {order} LIMIT 0;')
 for source,width in sources:
  for projection,count,order in [('7,*',width+1,'b.k'),('*,a.k AS chosen',width+1,'chosen'),('a.*,b.k AS chosen',4,'chosen')]:
   queries.append(f'SELECT {projection} FROM {source} UNION ALL SELECT '+','.join('NULL' for _ in range(count))+f' ORDER BY {order};')
  tail=','.join('NULL' for _ in range(width))
  queries.append(f'SELECT {tail} UNION ALL SELECT * FROM {source} ORDER BY k;')
  later=','.join('NULL AS later' if i==0 else 'NULL' for i in range(width))
  queries.append(f'SELECT * FROM {source} UNION ALL SELECT {later} ORDER BY later;')
  queries.append(f'SELECT * FROM {source} UNION ALL SELECT {tail},0 ORDER BY k;')
 for kind in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']:
  source=f'l AS "Left Source" {kind} r AS "Right Source" USING("k")'
  for order in ['"k"','"Left Source"."k"','"Right Source"."k"','"Right Source"."ID"']:
   queries.append(f'SELECT * FROM {source} UNION ALL SELECT NULL,NULL,NULL,NULL,NULL ORDER BY {order};')
 for _ in range(a.random_cases):
  source,projection,count=rng.choice(shapes)
  order=rng.choice(['id','k','a.k','b.k','1',str(count)])
  operation=rng.choice(['UNION ALL','UNION','INTERSECT','EXCEPT'])
  queries.append(f'SELECT {projection} FROM {source} {operation} SELECT '+','.join(rng.choice(['NULL','0',"'A'",'2',"X'32'"]) for _ in range(count))+f' ORDER BY {order} LIMIT {rng.randrange(0,8)} OFFSET {rng.randrange(0,3)};')
 with tempfile.TemporaryDirectory(prefix='sqleanite-join-compound-') as tmp:
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
