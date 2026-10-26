#!/usr/bin/env python3
"""Binary JSON escape controls plus separately counted fresh seeded payloads.

Enumerate every byte after backslash, continuation/Unicode sentinel boundaries,
four text kinds, nonminimal headers and enclosing arrays/objects. Compare all
json_valid masks and default. Root type/length are conditional SQL expressions
guarded by each implementation's own superficial check, not oracle filtering.
Preserve all rows, input bytes, mode status, immutable files and C observations.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def node(kind,data,width=None):
 n=len(data)
 if width is None:width=0 if n<12 else 1 if n<256 else 2 if n<65536 else 4
 return bytes([(n if width==0 else {1:12,2:13,4:14,8:15}[width])*16+kind])+(n.to_bytes(width,'big') if width else b'')+data
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354831);p.add_argument('--random-cases',type=int,default=128);p.add_argument('--fixtures',type=int,default=2);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest();values=[]
 def add(group,kind,data,width=None):
  b=node(kind,data,width)
  for shape,value in [('root',b),('array',node(11,b)),('object',node(12,b'\x17a'+b))]:values.append(dict(group=group,shape=shape,hex=value.hex()))
 for kind in [7,8,9,10]:
  for c in range(256):
   for prefix in [b'',b'a',b'\\\n',b'\\\r\n']:
    for suffix in [b'',b'a']:
     data=prefix+b'\\'+bytes([c])+suffix;width=[0,1,2,4,8][(c+kind+len(prefix)+len(suffix))%5];add('fixed-byte-escape',kind,data,width)
 for value in [0,127,128,0xd800,0xdc00,0xfffe,0xffff,0x99998,0x99999,0x9999a,0x10ffff]:
  data=chr(value).encode('utf-8','surrogatepass')
  for kind in [7,8,9,10]:
   for prefix in [b'',b'\\\n',b'\\\r',b'\\\r\n',b'\\\xe2\x80\xa8',b'\\\xe2\x80\xa9']:
    add('fixed-unicode-boundary',kind,prefix+data)
 fixed=len(values)
 for _ in range(a.random_cases):
  data=bytearray(bytes(rng.randrange(256) for _ in range(rng.randrange(1,32))));pos=rng.randrange(len(data)+1)
  data[pos:pos]=rng.choice([b'\\',b'\\\n',b'\\u',b'\\x',b'\\\r\n']);add('seeded-payload',rng.randrange(7,11),data)
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=600);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snap(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 cases=[];runs=[]
 sql='SELECT id,'+','.join(['json_valid(v)']+[f'json_valid(v,{n})' for n in range(1,16)]+["CASE WHEN json_valid(v,4) THEN quote(json_type(v)) END","CASE WHEN json_valid(v,4) THEN quote(json_array_length(v)) END"])+ ' FROM t ORDER BY id;'
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-escapes-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,65536,1024,32768,2048,16384,4096,8192][fixture%8];folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db'
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v);BEGIN;'+''.join(f"INSERT INTO t VALUES({i},X'{v['hex']}');" for i,v in enumerate(values))+'COMMIT;';made=csql(base,setup);assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snap(left),snap(right)
    l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);ll,cl=l['stdout'].splitlines(),c['stdout'].splitlines();assert len(cl)==len(values),c
    for i,wanted in enumerate(cl):
     actual=ll[i] if i<len(ll) else None;cases.append(dict(fixture=fixture,page_size=page,mode=mode,input=i,group=values[i]['group'],lean=actual,sqlite=wanted,matched=actual==wanted))
    obs='PRAGMA integrity_check;SELECT id,hex(v) FROM t ORDER BY id;';lo,co=csql(left,obs),csql(right,obs)
    runs.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=c,lean_unchanged=bl==snap(left),sqlite_unchanged=br==snap(right),observation_lean=lo,observation_sqlite=co,matched=l['code']==c['code']==0 and l['stdout']==c['stdout'] and bl==snap(left) and br==snap(right) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n')))
 assert source==digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest()
 failures=sum(not c['matched'] for c in cases)+sum(not c['matched'] for c in runs)
 report=dict(seed=a.seed,random_cases=a.random_cases,values=values,fixed_inputs=fixed,seeded_inputs=len(values)-fixed,cases=cases,runs=runs,failures=failures,implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip(),comparison=__doc__.strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures,fixed_inputs=fixed,seeded_inputs=len(values)-fixed)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
