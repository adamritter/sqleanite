#!/usr/bin/env python3
"""Compare exact CTAS catalog spelling on public file paths with fresh names.

Names and affinity choices are generated before either implementation runs.
Both modes compare full SQL output, errors, schema text, stored typed values,
C integrity, reopening and a subsequent C insert. No cases are excluded.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('position',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--count',type=int,default=128);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=120)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def quote(s):return '"'+s.replace('"','""')+'"'
 special=['select','within','ABORT','column','group','a b','a"b','é中','1start','a$b','a;b','a\nb']
 def name():return rng.choice(special) if rng.randrange(3)==0 else ''.join(rng.choice('abAZ_019 é中";$') for _ in range(rng.randrange(1,38)))
 expressions=['1',"'text'",'NULL',"X'0080FF'",'CAST(1 AS INTEGER)','CAST(1.25 AS REAL)','CAST(1 AS NUMERIC)',"CAST('é中' AS TEXT)"]
 inputs=[]
 for i in range(a.count):
  table=name();columns=[]
  for n in range(rng.randrange(1,9)):
   column=name()
   while column.lower() in [x[0].lower() for x in columns]:column=name()
   columns.append((column,rng.choice(expressions)))
  create='CREATE TABLE '+quote(table)+' AS SELECT '+','.join(e+' AS '+quote(n) for n,e in columns)+';'
  select='SELECT rowid,'+','.join('typeof('+quote(n)+'),hex('+quote(n)+')' for n,e in columns)+' FROM '+quote(table)+' ORDER BY rowid;'
  follow='INSERT INTO '+quote(table)+' VALUES('+','.join(e for n,e in columns)+');PRAGMA integrity_check;'+select
  inputs.append(dict(table=table,columns=columns,create=create,select=select,follow=follow,page_size=512<<(i%8)))
 cases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-ctas-catalog-') as tmp:
  folder=Path(tmp)
  for i,entry in enumerate(inputs):
   base=folder/(str(i)+'-base.db');made=csql(base,'PRAGMA page_size='+str(entry['page_size'])+';CREATE TABLE catalog_guard(id INTEGER PRIMARY KEY);');assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db');shutil.copyfile(base,left);shutil.copyfile(base,right)
    sql=entry['create']+'\n'+entry['select'];l=run([str(binary),mode,str(left)],sql);c=csql(right,sql)
    observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;'+entry['select']
    lo,co=csql(left,observe),csql(right,observe);lr,cr=run([str(binary),mode,str(left)],entry['select']),csql(right,entry['select'])
    lw,cw=csql(left,entry['follow']),csql(right,entry['follow'])
    matched=helpers.same(l,c) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and helpers.same(lr,cr) and lw['code']==cw['code']==0 and lw['stdout']==cw['stdout']
    cases.append(dict(input=i,mode=mode,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,reopen_lean=lr,reopen_sqlite=cr,follow_lean=lw,follow_sqlite=cw,matched=matched))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 report=dict(seed=a.seed,inputs=inputs,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),comparison=__doc__.strip(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
