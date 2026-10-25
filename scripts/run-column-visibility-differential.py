#!/usr/bin/env python3
"""Compare visible SQL column lookup versus internal rowid bookkeeping.

Check reads, ordering, grouping, predicates, assignments, insert targets and
index declarations. Real rowid/oid/_rowid_ access and output aliases remain
positive controls. Complete output/error status, C metadata/typed-row/integrity
observations, C follow-up writes and Lean reopening in both file modes. This
scope does not yet admit that declared name when an extra hidden rowid is needed.
Every mismatch is retained.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354420);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
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
 hidden='__sqleanite_rowid'
 queries=[f'SELECT {hidden} FROM n;',f'SELECT "{hidden}" FROM n;',
  f'SELECT n.{hidden} FROM n;',f'SELECT {hidden} FROM l;',
  f'SELECT a."{hidden}",b.id FROM l a LEFT JOIN r b ON a.id=b.id ORDER BY a.rowid,b.rowid;',
  f'SELECT other_id FROM n ORDER BY {hidden};',
  f'SELECT count(*) FROM n WHERE {hidden}=1;',
  f'SELECT sum({hidden}) FROM n;',
  f'SELECT other_id FROM n GROUP BY {hidden};',
  f"UPDATE n SET z='changed' WHERE {hidden}=1;",
  f'UPDATE n SET {hidden}=9 WHERE rowid=1;',
  f'DELETE FROM n WHERE {hidden}>0;',
  f"INSERT INTO n({hidden},other_id,z) VALUES(99,8,'new');",
  f'CREATE INDEX HiddenIndex ON n({hidden});',
  'CREATE INDEX RowidIndex ON n(rowid);','CREATE INDEX OidIndex ON n(oid);',
  'CREATE INDEX UnderscoreIndex ON n(_rowid_);',
  'CREATE INDEX DeclaredIndex ON l(id);',
  'SELECT rowid,oid,_rowid_,other_id,z FROM n ORDER BY rowid;',
  f'SELECT rowid AS "{hidden}" FROM n ORDER BY "{hidden}";',
  f'SELECT a.rowid AS "{hidden}",b.id FROM n a,l b ORDER BY "{hidden}",b.id;',
  "INSERT INTO n(rowid,other_id,z) VALUES(9,8,'new');",
  'UPDATE n SET rowid=7 WHERE rowid=1;',
  "UPDATE n SET z='changed' WHERE oid=1;",
  'DELETE FROM n WHERE _rowid_=1;',
  f'SELECT 1 FROM n WHERE {hidden}=1 LIMIT 0;',
  f'SELECT other_id FROM n WHERE 0 AND {hidden}=1;',
  f'SELECT other_id FROM n WHERE 1 OR {hidden}=1;',
  f'SELECT CASE WHEN 1 THEN 8 ELSE {hidden} END FROM n;',
  f'SELECT count(*) FROM n HAVING sum({hidden})>0;',
  f'SELECT count(*) FROM n GROUP BY {hidden} HAVING count(*)>0;',
  f'SELECT a.rowid,b.id FROM n a,l b WHERE a.{hidden}=b.id;',
  f'SELECT a.rowid,b.id FROM n a LEFT JOIN l b ON a.{hidden}=b.id;',
  f'SELECT * FROM n a JOIN l b USING({hidden});',
  f'SELECT "__SQLEANITE_ROWID" FROM n LIMIT 0;',
  f'CREATE TABLE Extra AS SELECT {hidden} FROM n;',
  f'INSERT INTO l(id,k,left_only) SELECT {hidden},other_id,z FROM n;',
  f"UPDATE n SET z='changed' RETURNING {hidden};",
  f'DELETE FROM n RETURNING {hidden};',
  f"INSERT INTO n VALUES(99,'new') RETURNING {hidden};",
  f'SELECT {hidden},rowid,id FROM Named ORDER BY id;',
  f"UPDATE Named SET {hidden}='changed' WHERE id=1;",
  f'CREATE INDEX NamedIndex ON Named({hidden});',
  'SELECT rowid,oid,_rowid_,v FROM Shadow ORDER BY rowid;',
  'SELECT rowid,oid,_rowid_,v FROM Shadow WHERE rowid=31 ORDER BY oid;',
  'UPDATE Shadow SET rowid=52 WHERE oid=41;',
  'CREATE INDEX ShadowIndex ON Shadow(rowid);',
  'INSERT INTO Shadow(rowid,oid,_rowid_,v) VALUES(80,90,100,110);',
  f'ALTER TABLE n RENAME COLUMN {hidden} TO renamed;',
  f'ALTER TABLE n DROP COLUMN {hidden};']
 for _ in range(a.random_cases):
  alias=rng.choice(['rowid','oid','_rowid_']);value=rng.randrange(1,12)
  queries.append(f'SELECT {alias},other_id,z FROM n WHERE {alias}<{value} ORDER BY {alias} DESC;')
 with tempfile.TemporaryDirectory(prefix='sqleanite-column-visibility-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3]
   base=Path(tmp)/f'base{fixture}.db'
   left_type=['INTEGER','TEXT','BLOB','NUMERIC','REAL',''][fixture%6]
   right_type=['TEXT','NUMERIC','INTEGER','BLOB','','REAL'][fixture%6]
   left_name='K' if fixture%2 else 'k';right_name='ID' if fixture%2 else 'id'
   left_key='TEXT' if fixture%2 else 'INTEGER'
   setup=f"PRAGMA page_size={page};CREATE TABLE l(id {left_key} PRIMARY KEY,{left_name} {left_type},left_only TEXT);CREATE TABLE r({right_name} INTEGER PRIMARY KEY,k {right_type},right_only TEXT);CREATE TABLE n(other_id,z);CREATE TABLE Named(id INTEGER PRIMARY KEY,{hidden} TEXT);INSERT INTO Named VALUES(1,'declared'),(2,NULL);CREATE TABLE Shadow(rowid,oid,_rowid_,v);INSERT INTO Shadow VALUES(31,41,51,61),(32,42,52,62);"
   ncount=[1,0,4,2][fixture%4] if fixture<4 else rng.randrange(0,9)
   for i in range(1,ncount+1):
    setup+=f"INSERT INTO n VALUES({rng.randrange(-10,20)},'z-{rng.randrange(1000)}');"
   counts=[(3,4),(0,4),(3,0),(0,0)][fixture%4]
   if fixture>=4:counts=(rng.randrange(1,8),rng.randrange(1,8))
   for table,count in zip(['l','r'],counts):
    for i in range(1,count+1):
     value=rng.choice(['NULL','1','2',"'01'","'2'","'a'","'A'"])
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
