#!/usr/bin/env python3
"""DROP TABLE/INDEX statement outcomes, transaction rollback and file contents.

Each script starts from independent copies of a SQLite-created multi-table
image. The pinned CLI checks schema object names, remaining rows and integrity
after both successful and failed scripts. Error codes/messages are not compared.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=353960);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--read-only-format',action='store_true');p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];fixtures=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def observe(path):
  r=run([a.sqlite,'-batch','-bail',str(path)],"PRAGMA integrity_check;SELECT type,name,tbl_name FROM sqlite_schema ORDER BY type,name;")
  if r['code']:return r
  names=run([a.sqlite,'-batch','-bail',str(path)],"SELECT name FROM sqlite_schema WHERE type='table' ORDER BY name;")['stdout'].splitlines()
  for name in names:
   q='"'+name.replace('"','""')+'"';rows=run([a.sqlite,'-batch','-bail',str(path)],f'SELECT rowid,typeof(id),hex(id),typeof(v),hex(v) FROM {q} ORDER BY rowid;');r['stdout']+='TABLE '+name+'\n'+rows['stdout'];r['code']|=rows['code'];r['stderr']+=rows['stderr']
  return r
 scripts=['DROP TABLE t;','DROP INDEX tv;','DROP INDEX unique_v;','DROP TABLE keys;','DROP TABLE t;DROP TABLE keys;DROP TABLE keep;',
  'DROP TABLE IF EXISTS absent;','DROP INDEX IF EXISTS absent;','DROP TABLE absent;','DROP INDEX absent;',
  'DROP INDEX sqlite_autoindex_keys_1;','DROP INDEX IF EXISTS sqlite_autoindex_keys_1;',
  'DROP TABLE IF EXISTS sqlite_schema;','DROP TABLE IF EXISTS sqlite_master;','DROP TABLE IF EXISTS sqlite_temp_schema;',
  'DROP TABLE IF EXISTS tv;','DROP INDEX IF EXISTS t;','DROP TABLE tv;','DROP INDEX t;',
  'BEGIN;DROP TABLE t;ROLLBACK;SELECT count(*) FROM t;','BEGIN;DROP INDEX tv;ROLLBACK;SELECT count(*) FROM t;',
  'BEGIN;DROP TABLE t;COMMIT;','BEGIN;DROP INDEX tv;COMMIT;',
  'DROP INDEX tv;CREATE INDEX tv ON keep(v);','DROP TABLE t;CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(999,7);',
  'BEGIN;DROP TABLE t;CREATE TABLE t(id INTEGER PRIMARY KEY,v);INSERT INTO t VALUES(999,7);ROLLBACK;',
  'DROP INDEX tv;DROP INDEX tv;','DROP TABLE t;DROP TABLE t;',
  'DROP INDEX tv;DROP INDEX IF EXISTS tv;','DROP TABLE t;DROP TABLE IF EXISTS t;',
  'DROP INDEX unique_v;INSERT INTO keep VALUES(999,1);',
  'DROP TABLE t;CREATE INDEX tv ON keep(v);','BEGIN;DROP TABLE t;ROLLBACK;DROP INDEX tv;',
  'DROP TABLE "T";','DROP INDEX [TV];',"DROP TABLE 'keys';"]
 with tempfile.TemporaryDirectory(prefix='sqleanite-drop-') as tmp:
  for sample in range(a.fixtures):
   for page in [512,4096,65536]:
    folder=Path(tmp)/f'{sample}-{page}';folder.mkdir();base=folder/'base.db';count=rng.randrange(6,16)
    setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE TABLE keep(id INTEGER PRIMARY KEY,v);CREATE TABLE keys(id TEXT PRIMARY KEY,v);CREATE INDEX tv ON t(v);CREATE UNIQUE INDEX unique_v ON keep(v);BEGIN;'
    for i in range(1,count+1):
     v=f'{rng.randrange(1000000)}-'+chr(97+i%26)*rng.choice([0,80,2000]);setup+=f"INSERT INTO t VALUES({i},'{v}');INSERT INTO keep VALUES({i},{i});INSERT INTO keys VALUES('key-{i}',{i});"
    r=run([a.sqlite,'-batch','-bail',str(base)],setup+'COMMIT;');assert r['code']==0,r
    if a.read_only_format:
     raw=bytearray(base.read_bytes());raw[18]=255;base.write_bytes(raw)
    fixtures.append(dict(sample=sample,page_size=page,rows=count,read_only_format=a.read_only_format))
    for mode in ['--verified-file','--verified-wal-file']:
     for sql in scripts:
      dest=folder/str(len(cases));dest.mkdir();lean=dest/'lean.db';ref=dest/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref)
      l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail',str(ref)],sql);lo=observe(lean);ro=observe(ref)
      same=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
      cases.append(dict(sample=sample,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=same,observed_lean=lo,observed_sqlite=ro))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=fixtures,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
