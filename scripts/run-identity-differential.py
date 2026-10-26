#!/usr/bin/env python3
"""Pinned SQLite identity functions through query, write and rejection paths.

Both file modes compare full outputs/errors and C-observed schema/typed rows.
Seeded values reuse explicit SQL templates; unsupported outcomes are retained.
The reference version/source identity is asserted, never read by the Lean port.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('helpers',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--count',type=int,default=128);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=30);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 reference=csql(':memory:','SELECT sqlite_version(),sqlite_source_id();')
 assert reference['stdout']=='3.53.4|2026-07-24 19:02:57 bf7c7f30031888f4e796e429ab3978879485813aaca6f641c7b33e4e09459bcc\n',reference
 fixed=[]
 for function in ['sqlite_version','SQLITE_VERSION','sqlite_source_id','SQLITE_SOURCE_ID','"sqlite_version"','`sqlite_source_id`','[sqlite_version]']:
  for arguments in ['', '*','DISTINCT','0','NULL','1,2','DISTINCT 1','missing']:
   call=function+'('+arguments+')'
   for wrapper in ['SELECT '+call+';','SELECT '+call+' FROM t LIMIT 0;','SELECT CASE WHEN 0 THEN '+call+' ELSE 7 END;','SELECT 0 AND '+call+';']:
    fixed.append(wrapper)
 fixed.extend(['SELECT sqlite_version(1)+missing;', 'SELECT missing+sqlite_version(1);', 'SELECT sqlite_version(json_type());', 'SELECT json_type(sqlite_version(1));', 'SELECT sqlite_version(json_type(missing,1,2));', 'SELECT json_type(1,2,3)+missing;', 'SELECT coalesce(sqlite_version(1),missing);', 'SELECT sqlite_version(missing) FROM t LIMIT 0;', 'SELECT missing AS x,sqlite_version(1) FROM t;', 'SELECT sqlite_version(1),missing AS x FROM t;', 'SELECT sqlite_version(1) AS x FROM t ORDER BY missing;', 'SELECT CASE WHEN 0 THEN missing ELSE 7 END;', 'SELECT sqlite_version(1)+sqlite_source_id(2);', 'SELECT sqlite_source_id(2)+sqlite_version(1);', 'SELECT coalesce(sqlite_version(1),sqlite_source_id(2));', 'SELECT missing1+missing2;', 'SELECT sqlite_version(1),missing;', 'SELECT sqlite_version(1) WHERE missing;'])
 fixed.extend(['SELECT count(*),sqlite_version(missing) FROM t;', 'SELECT sqlite_version(missing) FROM t GROUP BY v;', 'INSERT INTO t(v) VALUES(sqlite_version(missing));', 'UPDATE t SET v=sqlite_version(missing);', 'SELECT sum(id ORDER BY sqlite_version(missing)) FROM t;', 'SELECT count(*),sqlite_version(1)+missing FROM t;', 'SELECT sqlite_version(1)+missing FROM t GROUP BY v;', 'INSERT INTO t(v) VALUES(sqlite_version(1)+missing);', 'UPDATE t SET v=sqlite_version(1)+missing;', 'SELECT sum(id ORDER BY sqlite_version(1)+missing) FROM t;', 'SELECT count(*),sqlite_version(json_type()) FROM t;', 'SELECT sqlite_version(json_type()) FROM t GROUP BY v;', 'INSERT INTO t(v) VALUES(sqlite_version(json_type()));', 'UPDATE t SET v=sqlite_version(json_type());', 'SELECT sum(id ORDER BY sqlite_version(json_type())) FROM t;', 'SELECT count(*),sqlite_source_id(missing) FROM t;', 'SELECT sqlite_source_id(missing) FROM t GROUP BY v;', 'INSERT INTO t(v) VALUES(sqlite_source_id(missing));', 'UPDATE t SET v=sqlite_source_id(missing);', 'SELECT sum(id ORDER BY sqlite_source_id(missing)) FROM t;', 'SELECT count(*),sqlite_source_id(1)+missing FROM t;', 'SELECT sqlite_source_id(1)+missing FROM t GROUP BY v;', 'INSERT INTO t(v) VALUES(sqlite_source_id(1)+missing);', 'UPDATE t SET v=sqlite_source_id(1)+missing;', 'SELECT sum(id ORDER BY sqlite_source_id(1)+missing) FROM t;', 'SELECT count(*),sqlite_source_id(json_type()) FROM t;', 'SELECT sqlite_source_id(json_type()) FROM t GROUP BY v;', 'INSERT INTO t(v) VALUES(sqlite_source_id(json_type()));', 'UPDATE t SET v=sqlite_source_id(json_type());', 'SELECT sum(id ORDER BY sqlite_source_id(json_type())) FROM t;'])
 inputs=[dict(sql=sql,page_size=512<<(i%8),data=rng.randrange(1,9999),group='fixed-call-shapes') for i,sql in enumerate(fixed)]
 for i in range(a.count):
  fn=rng.choice(['sqlite_version()','sqlite_version(*)','sqlite_source_id()','sqlite_source_id(DISTINCT)']);n=rng.randrange(1,200);limit=rng.randrange(1,8)
  templates=[
   'SELECT id,typeof('+fn+'),quote('+fn+') FROM t ORDER BY id;',
   'SELECT substr('+fn+','+str(limit)+','+str(n)+'),length('+fn+');',
   'SELECT '+fn+',count(*) FROM t GROUP BY '+fn+' ORDER BY 1;',
   'SELECT count(*),min('+fn+'),max('+fn+') FROM t;',
   'SELECT t.id,'+fn+' FROM t JOIN u ON u.id=t.id ORDER BY t.id;',
   'SELECT id FROM t WHERE length('+fn+')>'+str(limit)+' ORDER BY id LIMIT '+str(limit)+';',
   'INSERT INTO t(v) VALUES('+fn+');\nSELECT id,v FROM t ORDER BY id;',
   'UPDATE t SET v=substr('+fn+',1,'+str(n)+') WHERE id<=2 RETURNING id,v;',
   'CREATE TABLE snapshot AS SELECT id,'+fn+' AS value FROM t;\nSELECT * FROM snapshot ORDER BY id;',
   'BEGIN;\nUPDATE t SET v='+fn+';\nROLLBACK;\nSELECT id,v FROM t ORDER BY id;',
   'SELECT json_object(\'version\','+fn+');',
   'SELECT '+fn+' IN (\'x\','+fn+'), '+fn+'=sqlite_version();'
  ]
  inputs.append(dict(sql=templates[i%len(templates)],page_size=512<<(i%8),data=rng.randrange(1,9999),group='seeded-query-write-contexts'))
 atoms=['sqlite_version(1)','sqlite_source_id(NULL)','json_type()','json_type(1,2,3)','missing','abs(-1)','0','TRUE','FALSE','NULL']
 def expression(depth):
  if depth==0 or rng.randrange(4)==0:return rng.choice(atoms)
  left=expression(depth-1);right=expression(depth-1);kind=rng.randrange(5)
  if kind==0:return '('+left+' + '+right+')'
  if kind==1:return 'coalesce('+left+','+right+')'
  if kind==2:return 'CASE WHEN 0 THEN '+left+' ELSE '+right+' END'
  if kind==3:return 'CAST('+left+' AS TEXT)'
  return left+' IN ('+right+','+expression(depth-1)+')'
 for i in range(a.count):
  sql='SELECT '+expression(1+i%3)+(' FROM t LIMIT 0;' if i%2 else ';')
  inputs.append(dict(sql=sql,page_size=512<<(i%8),data=rng.randrange(1,9999),group='seeded-diagnostic-expressions'))
 cases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-identity-') as temp:
  folder=Path(temp)
  for i,entry in enumerate(inputs):
   base=folder/(str(i)+'-base.db');setup='PRAGMA page_size='+str(entry['page_size'])+';CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);CREATE TABLE u(id INTEGER PRIMARY KEY);'+''.join('INSERT INTO t VALUES('+str(j)+",'value "+str(entry['data']+j)+"');INSERT INTO u VALUES("+str(j)+');' for j in range(1,4));made=csql(base,setup);assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db');shutil.copyfile(base,left);shutil.copyfile(base,right)
    l,c=run([str(binary),mode,str(left)],entry['sql']),csql(right,entry['sql'])
    observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;SELECT id,typeof(v),hex(v) FROM t ORDER BY id;'
    if 'CREATE TABLE snapshot' in entry['sql']:observe+='SELECT * FROM snapshot ORDER BY id;'
    lo,co=csql(left,observe),csql(right,observe)
    matched=helpers.same(l,c) and lo==co and lo['code']==0 and lo['stdout'].startswith('ok\n')
    cases.append(dict(input=i,group=entry['group'],mode=mode,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,matched=matched))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 r=dict(seed=a.seed,comparison=__doc__.strip(),inputs=inputs,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip());a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=r['failures'])));return bool(r['failures'])
if __name__=='__main__':raise SystemExit(main())
