#!/usr/bin/env python3
"""Fresh malformed-trigger EOF/token probes in both public file modes.

Names, values and comments vary under preselected malformed templates. Compare
exact SQL diagnostics after CLI framing removal, result prefixes and unchanged
C-observed catalog/data/integrity. A timeout is a failure. These malformed-input
checks do not claim execution of valid triggers, covered negatively by the gap
survey. The full parser has separate internal unknown-token-after-body controls.
"""
import argparse,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('position',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,required=True);p.add_argument('--count',type=int,default=64);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  try:
   q=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=10);return dict(code=q.returncode,stdout=q.stdout.decode('latin1'),stderr=q.stderr.decode('latin1'))
  except subprocess.TimeoutExpired as expired:return dict(code=124,stdout=(expired.stdout or b'').decode('latin1'),stderr=(expired.stderr or b'').decode('latin1'),timed_out=True,timeout_seconds=10)
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 inputs=[]
 for i in range(a.count):
  value=rng.randrange(1,10000000);name='truncated_'+str(rng.randrange(100000000));unknown='unexpected_'+str(rng.randrange(100000000))
  body=rng.choice(['','SELECT '+str(value)+';','UPDATE t SET n='+str(value)+';','DELETE FROM t;','INSERT INTO t VALUES('+str(value)+');',unknown+' token'])
  sql='CREATE TRIGGER '+name+rng.choice([' AFTER UPDATE ',' BEFORE INSERT ',' AFTER DELETE '])+'ON t BEGIN /* body '+str(value)+' */ '+body
  inputs.append(dict(sql=sql,value=value))
 observe='PRAGMA integrity_check;SELECT type,hex(name),hex(tbl_name),hex(sql) FROM sqlite_schema ORDER BY type,name;SELECT n FROM t ORDER BY n;';cases=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-trigger-eof-') as tmp:
  folder=Path(tmp)
  for i,entry in enumerate(inputs):
   base=folder/(str(i)+'-base.db');made=csql(base,'CREATE TABLE t(n INTEGER);INSERT INTO t VALUES('+str(entry['value'])+');');assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(str(i)+mode+'-lean.db');right=folder/(str(i)+mode+'-sqlite.db');shutil.copyfile(base,left);shutil.copyfile(base,right)
    l,c=run([str(binary),mode,str(left)],entry['sql']),csql(right,entry['sql']);lo,co=csql(left,observe),csql(right,observe)
    matched=not l.get('timed_out') and not c.get('timed_out') and c['code']!=0 and helpers.same(l,c) and lo==co and lo['code']==0 and lo['stdout'].startswith('ok\n')
    cases.append(dict(input=i,mode=mode,lean=l,sqlite=c,observation_lean=lo,observation_sqlite=co,matched=bool(matched)))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 report=dict(seed=a.seed,inputs=inputs,cases=cases,failures=sum(not c['matched'] for c in cases),comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
