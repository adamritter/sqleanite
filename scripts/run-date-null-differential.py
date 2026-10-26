#!/usr/bin/env python3
"""NULL date/time values, deterministic rejection order and evaluated argument errors.

Fixed controls and seeded NULL placements are retained without outcome filtering.
Inputs include row-dependent NULLIF and errors from argument expressions.
Both modes compare typed outputs, persisted state and reopening.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('helpers',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--count',type=int,default=128);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  try:
   r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=30);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
  except subprocess.TimeoutExpired as r:return dict(code=124,stdout=(r.stdout or b'').decode('latin1'),stderr=(r.stderr or b'').decode('latin1'),timed_out=True)
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def q(s):return "'"+s.replace("'","''")+"'"
 reference=csql(':memory:','SELECT sqlite_version();');assert reference['stdout']=='3.53.4\n'
 functions=['date','time','datetime','julianday','unixepoch','strftime','timediff']
 inputs=[]
 def call(fn,args):return fn+'('+','.join(args)+')'
 def add(expr,group,i):
  inputs.append(dict(expression=expr,sql='SELECT typeof('+expr+'),quote('+expr+'),hex(CAST('+expr+' AS BLOB));',group=group,page_size=512<<(i%8)))
 for fn in functions:
  if fn=='timediff':vectors=[['NULL',"'now'"],["'now'",'NULL'],['NULL',"'2001-02-03'"],['NULL','NULL']]
  else:
   vectors=[["'now'",'NULL'],["'now'","'localtime'",'NULL'],['NULL',"'utc'"],["'invalid'","'utc'"],["'2001-02-03'","'unknown modifier'","'utc'"],["'subsec'",'NULL']]
   if fn=='strftime':vectors=[["'%F'"]+args for args in vectors]+[['NULL',"'now'"],['NULL']]
  for args in vectors:add(call(fn,args),'fixed-null-or-invalid-prefix',len(inputs))
  for bad in ['abs(-9223372036854775808)',"json('malformed')"]:
   args=['NULL',bad]
   if fn=='strftime':args=["'%F'"]+args
   add(call(fn,args),'fixed-argument-error',len(inputs))
 for i in range(a.count):
  fn=rng.choice(functions);base=rng.choice(["'now'","'subsec'","'subsecond'","'2001-02-03'",str(rng.randrange(-300000,300000))])
  mods=rng.choices(["'utc'","'localtime'","'+1 day'","'start of month'","'invalid'"],k=rng.randrange(4));mods.insert(rng.randrange(len(mods)+1),'NULL')
  args=[base]+mods
  if fn=='timediff':args=rng.choice([[base,'NULL'],['NULL',base]])
  if fn=='strftime':args=[rng.choice(["'%F'","'%s'","'%J'","'abc'",'NULL'])]+args
  expr=call(fn,args);add(expr,'seeded-null-contexts',i)
  if i%4==0:inputs[-1]['sql']='UPDATE t SET v='+expr+' WHERE id<=2 RETURNING id,typeof(v),quote(v);'
  elif i%4==1:
   rowexpr=expr.replace('NULL','NULLIF(v,v)')
   inputs[-1]['sql']='SELECT id,typeof('+rowexpr+'),quote('+rowexpr+') FROM t ORDER BY id;'
  elif i%4==2:inputs[-1]['sql']='INSERT INTO t(v) VALUES('+expr+');\nSELECT id,typeof(v),quote(v) FROM t ORDER BY id;'
 cases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-date-null-') as tmp:
  folder=Path(tmp)
  for i,entry in enumerate(inputs):
   base=folder/(str(i)+'-base.db');setup='PRAGMA page_size='+str(entry['page_size'])+';CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(1,10),(2,20),(3,30);';made=csql(base,setup);assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db');shutil.copyfile(base,left);shutil.copyfile(base,right)
    l,c=run([str(binary),mode,str(left)],entry['sql']),csql(right,entry['sql'])
    observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;SELECT id,typeof(v),quote(v),hex(CAST(v AS BLOB)) FROM t ORDER BY id;'
    lo,co=csql(left,observe),csql(right,observe);reopen=run([str(binary),mode,str(left)],'SELECT id,typeof(v),quote(v) FROM t ORDER BY id;');expected=csql(right,'SELECT id,typeof(v),quote(v) FROM t ORDER BY id;')
    matched=not l.get('timed_out',False) and helpers.same(l,c) and lo==co and helpers.same(reopen,expected) and lo['code']==0 and lo['stdout'].startswith('ok\n')
    cases.append(dict(input=i,mode=mode,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,reopened_lean=reopen,reopened_sqlite=expected,matched=matched))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 report=dict(seed=a.seed,comparison=__doc__.strip(),inputs=inputs,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
