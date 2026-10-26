#!/usr/bin/env python3
"""PRAGMA listing and exact unknown-schema errors through both public file modes.

Every selected SQL input is retained. Compare full output/error diagnostics,
main/WAL immutability, C-observed catalog/typed data and Lean reopening. The
listed names describe the pinned build's recognized surface, not proof that
all recognized PRAGMAs are implemented by Lean.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('helpers',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def ident(s):return '"'+s.replace('"','""')+'"'
def quoted_schema(s,kind):
 if kind==0:return ident(s)
 if kind==1:return "'"+s.replace("'","''")+"'"
 if kind==2:return '`'+s.replace('`','``')+'`'
 return '['+s+']'
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--count',type=int,default=128);p.add_argument('--readonly',action='store_true');p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 binary=ROOT/'.lake/build/bin/sqleanite';sqlite=os.environ.get('SQLITE3_BIN','sqlite3');source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(command,sql):
  r=subprocess.run(command,input=sql.encode(),capture_output=True,timeout=30);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 assert csql(':memory:','SELECT sqlite_version();')['stdout']=='3.53.4\n'
 inputs=[]
 def add(sql,group):inputs.append(dict(sql=sql,group=group,page_size=512<<(len(inputs)%8)))
 for qualifier in ['', 'main.', 'temp.', '"MAIN".', '"TeMp".']:
  for suffix in ['', '(unused)', '=OFF', "('x;''y')", '(+01)', '(NULL)', "=('unused')"]:
   add('PRAGMA '+qualifier+'pragma_list'+suffix+';', 'fixed-list-syntax')
 for schema in ['missing', '', 'main.part', 'MiXeD"é中', 'table;name']:
  for pragma in ['pragma_list','table_info','table_xinfo','index_info','index_xinfo','index_list','unknown_custom','application_id','user_version']:
   for kind in range(4):add('PRAGMA '+quoted_schema(schema,kind)+'.'+pragma+'(t);', 'fixed-schema-error')
 for i in range(a.count):
  if i%3:
   schema='missing_'+''.join(rng.choice('azAZ09 ;"é中') for _ in range(rng.randrange(1,50)))
   pragma=rng.choice(['pragma_list','table_info','table_xinfo','index_info','index_xinfo','index_list','unknown_custom','application_id','user_version'])
   atom=rng.choice(['', '(t)', "('text')", '=OFF', '(+0x10)', '(-1e20)'])
   sql='PRAGMA '+quoted_schema(schema,rng.randrange(4))+rng.choice(['.',' /* gap */ . '])+pragma+atom+';'
  else:
   spelling=''.join(c.upper() if rng.getrandbits(1) else c for c in 'pragma_list')
   sql='PRAGMA '+rng.choice(['','main.','temp.','"MAIN".'])+ident(spelling)+rng.choice(['','='+str(rng.randrange(-100000,100000)),"('ignored;argument')",'("double quoted")'])+';'
  if i%4==0:sql='SELECT id,v FROM t ORDER BY id;\n'+sql+'\nSELECT 123;'
  elif i%4==1:sql='BEGIN;\n'+sql+'\nROLLBACK;'
  add(sql,'seeded-schema-or-list')
 if a.readonly:
  for sql in ['PRAGMA main.user_version=8;','PRAGMA application_id=9;','PRAGMA temp.user_version=10;']:
   add(sql,'readonly-write-controls')
 cases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-pragma-list-') as tmp:
  folder=Path(tmp)
  for i,entry in enumerate(inputs):
   base=folder/(str(i)+'-base.db');made=csql(base,'PRAGMA page_size='+str(entry['page_size'])+";CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,'payload;é'),(2,NULL);");assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db');shutil.copyfile(base,left);shutil.copyfile(base,right)
    if a.readonly:left.chmod(0o444);right.chmod(0o444)
    before=hashes(left)
    l,c=run([str(binary),mode,str(left)],entry['sql']),csql(right,entry['sql']);unchanged=before==hashes(left)
    obs='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;SELECT id,typeof(v),quote(v) FROM t ORDER BY id;'
    lo,co=csql(left,obs),csql(right,obs);reopen=run([str(binary),mode,str(left)],'SELECT id,v FROM t ORDER BY id;');expected=csql(right,'SELECT id,v FROM t ORDER BY id;')
    cases.append(dict(input=i,mode=mode,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,reopened_lean=reopen,reopened_sqlite=expected,bytes_unchanged=unchanged,matched=helpers.same(l,c) and unchanged and lo==co and lo['code']==0 and lo['stdout'].startswith('ok\n') and helpers.same(reopen,expected)))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 report=dict(seed=a.seed,readonly=a.readonly,comparison=__doc__.strip(),inputs=inputs,cases=cases,failures=sum(not x['matched'] for x in cases),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
