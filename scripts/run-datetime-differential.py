#!/usr/bin/env python3
"""Deterministic SQLite dates through public query and file-write contexts.

Fixed edge inputs and seeded dates/modifier chains are evaluated without
outcome filtering. Separate --host-seams probes retain currently unsupported
clock/timezone calls. Both modes compare typed output and C-observed storage.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('helpers',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--count',type=int,default=128);p.add_argument('--host-seams',action='store_true');p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  try:
   r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=30);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
  except subprocess.TimeoutExpired as r:return dict(code=124,stdout=(r.stdout or b'').decode('latin1'),stderr=(r.stderr or b'').decode('latin1'),timed_out=True)
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def q(s):return "'"+s.replace("'","''")+"'"
 reference=csql(':memory:','SELECT sqlite_version();');assert reference['stdout']=='3.53.4\n'
 functions=['date','time','datetime','julianday','unixepoch','strftime']
 dates=["'2001-02-03'","'2024-02-29'","'2023-02-31'","'2024-04-31'","'0000-01-01'","'-0001-12-31'","'-4713-11-24 12:00:00'","'9999-12-31 23:59:59.999'","'2024-01-01 24:15:31.1234'","'2024-01-31 24:15:31'","'12:34'","'12:34:56.999999'","'2001-02-03TT 04:05:06+14:59'","'2001-02-03 04:05:06 -00:30'","'2001-02-03 04:05:06.0005Z'",'0','2451544.5','5373484.49999','5373484.5','-1','NULL',"'not a date'","'2024-00-01'","'2024-01-32'","'2001-02-03 25:00'","'2001-02-03 12:34:60'","' 2001-02-03'","'2001-02-03\t'","CAST(x'323030312D30322D303300ff' AS TEXT)","x'323030312D30322D3033'","x'ff323030312D30322D3033'","'2451544.5junk'"]
 modifiers=[[],['+1 day'],['-1.25 days'],['+1 month'],['+1 month','floor'],['+1 year','ceiling'],['start of month','+1 month','-1 day'],['start of year'],['start of day'],['weekday 0'],['weekday 6'],['subsec'],['floor'],['floor','floor'],['ceiling'],['julianday'],['auto'],['unixepoch'],['+24:00'],['-00:01:02.123'],['+0001-02-03 04:05:06.789'],['-0000-01-00'],['+0.25 year'],['+1 DAY'],['weekday 7'],['start of week'],['+1 day '],['+1 day','unixepoch']]
 formats=['%Y-%m-%d %H:%M:%S','%F|%T|%f|%s|%J','%G|%g|%V|%j|%U|%W|%u|%w','%d|%e|%H|%k|%I|%l|%p|%P|%%','%Q','abc%','']
 inputs=[]
 def add(expr,group,slot):
  check='SELECT typeof('+expr+'),quote('+expr+'),hex(CAST('+expr+' AS BLOB));'
  inputs.append(dict(expression=expr,sql=check,group=group,page_size=512<<(slot%8)))
 for i,date in enumerate(dates):
  for j,fn in enumerate(functions):
   args=([q(formats[i%len(formats)])] if fn=='strftime' else [])+[date]
   add(fn+'('+','.join(args)+')','fixed-date-inputs',i+j)
 for i,mods in enumerate(modifiers):
  for j,date in enumerate(["'2024-01-31 12:34:56.789'",'1700000000',"'2023-02-31'"]):
   fn=functions[(i+j)%6];args=([q(formats[i%len(formats)])] if fn=='strftime' else [])+[date]+list(map(q,mods))
   add(fn+'('+','.join(args)+')','fixed-modifier-inputs',i+j)
 for i in range(a.count):
  year=rng.randrange(-4712,10000);year=('-'+str(-year).zfill(4)) if year<0 else str(year).zfill(4)
  date=year+'-%02d-%02d %02d:%02d:%02d.%03d'%(rng.randrange(1,13),rng.randrange(1,32),rng.randrange(25),rng.randrange(60),rng.randrange(60),rng.randrange(1000))
  mods=rng.choice(modifiers)
  if i%3==0:mods=[str(rng.randrange(-1200,1200)/8)+' '+rng.choice(['days','hours','minutes','seconds','months','years']),rng.choice(['floor','ceiling','subsec'])]
  fn=functions[i%6];args=([q(rng.choice(formats))] if fn=='strftime' else [])+[q(date)]+list(map(q,mods));expr=fn+'('+','.join(args)+')'
  add(expr,'seeded-date-modifier',i)
  if i%4==0:
   inputs[-1]['sql']='UPDATE t SET v='+expr+' WHERE id<=2 RETURNING id,typeof(v),quote(v);\nSELECT id,v FROM t ORDER BY id;'
  elif i%4==1:inputs[-1]['sql']='SELECT id,typeof('+expr+'),quote('+expr+') FROM t ORDER BY id;'
  elif i%4==2:inputs[-1]['sql']='INSERT INTO t(v) VALUES('+expr+');\nSELECT id,typeof(v),quote(v) FROM t ORDER BY id;'
 if a.host_seams:
  inputs=[]
  for i,expr in enumerate(["date()","date('now')","datetime('subsec')","strftime('%F')","datetime('2001-02-03','localtime')","datetime('2001-02-03','utc')"]):add(expr,'known-host-service-seams',i)
 cases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-datetime-') as tmp:
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
