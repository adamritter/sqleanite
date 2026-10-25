#!/usr/bin/env python3
"""SQLite blob-token adjacency, quoted prefixes, aliases and persisted DEFAULTs.
Compares successful output, error status and SQLite's persisted observations.
This is a lexical/SQL/file component regression, not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354216);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=60);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([a.sqlite,'-batch','-bail',str(path)],sql)
 def observe(path):
  out=csql(path,"PRAGMA integrity_check;SELECT name,type FROM sqlite_schema ORDER BY name;SELECT * FROM t ORDER BY x;")
  names=csql(path,"SELECT name FROM sqlite_schema WHERE name='Extra';")
  if names['stdout']=='Extra\n':
   more=csql(path,"PRAGMA table_info(Extra);SELECT typeof(a),hex(a) FROM Extra;")
   out['code'] |= more['code'];out['stdout']+=more['stdout'];out['stderr']+=more['stderr']
  return out
 expressions=[]
 for lead in ['x','X','"x"',"'x'",'`x`','[x]']:
  for gap in ['', ' ', '/*gap*/', '\n', '--gap\n']:
   for payload in ['80fF00','gg']:
    expressions.append(lead+gap+"'"+payload+"'")
 for _ in range(a.random_cases):
  payload=rng.randbytes(rng.randrange(0,65)).hex()
  expressions.append(rng.choice(['x','X','"x"'])+rng.choice(['','\t',' /*x*/ ', '\r\n'])+"'"+payload+"'")
 with tempfile.TemporaryDirectory(prefix='sqleanite-blob-token-') as tmp:
  base=Path(tmp)/'base.db';assert csql(base,'CREATE TABLE t(x INTEGER);INSERT INTO t VALUES(7),(19);')['code']==0
  for expression in expressions:
   for sql in ['SELECT '+expression+' FROM t ORDER BY x;', 'CREATE TABLE Extra(a DEFAULT '+expression+');\nINSERT INTO Extra DEFAULT VALUES;']:
    for mode in ['--verified-file','--verified-wal-file']:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref)
     l=run([binary,mode,str(lean)],sql);r=csql(ref,sql);lo=observe(lean);ro=observe(ref)
     matched=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout']
     cases.append(dict(mode=mode,sql=sql,lean=l,sqlite=r,observed_lean=lo,observed_sqlite=ro,matched=matched))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
