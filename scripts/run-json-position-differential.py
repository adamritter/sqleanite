#!/usr/bin/env python3
"""JSON error offsets through the public Core engines, including statement admission.

New seeded JSON documents and byte mutations mix with fixed position/SQL controls.
Optional maintained component replay is counted as fixed data. No oracle answer
filters inputs. Compare complete output/status/first diagnostic, immutable files,
and independent C typed-row/integrity observations in every configured geometry.
"""
import argparse,hashlib,json,os,random,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest(root=ROOT):
 h=hashlib.sha256()
 for p in sorted((root/'SQLeanite').rglob('*.lean'))+[root/'Main.lean']:h.update(str(p.relative_to(root)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def literal(data):
 if isinstance(data,str):data=data.encode()
 return "CAST(X'"+data.hex()+"' AS TEXT)"
def blob(data):return "X'"+data.hex()+"'"
def error(r):
 if not r['code']:return ''
 line=r['stderr'].splitlines()[0] if r['stderr'] else ''
 return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',line)
def same(l,r):return bool(l['code'])==bool(r['code']) and l['stdout']==r['stdout'] and error(l)==error(r)
def node(kind,data):
 n=len(data);w=0 if n<12 else 1 if n<256 else 2 if n<65536 else 4
 return bytes([(n if w==0 else {1:12,2:13,4:14}[w])*16+kind])+(n.to_bytes(w,'big') if w else b'')+data
def mutate(rng,data):
 data=bytearray(data)
 for _ in range(rng.randrange(1,5)):
  pos=rng.randrange(len(data)+1);op=rng.randrange(3)
  if op==0:data[pos:pos]=bytes([rng.randrange(256)])
  elif pos<len(data) and op==1:del data[pos]
  elif pos<len(data):data[pos]=rng.randrange(256)
 return bytes(data)
def random_value(rng,depth=0):
 pick=rng.randrange(8 if depth<3 else 6)
 if pick==0:return None
 if pick==1:return rng.choice([True,False])
 if pick==2:return rng.randrange(-10**18,10**18)
 if pick==3:return rng.random()*10**rng.randrange(-20,20)
 if pick<6:return ''.join(rng.choice('abé中😀\\\n\t"0123') for _ in range(rng.randrange(16)))
 if pick==6:return [random_value(rng,depth+1) for _ in range(rng.randrange(6))]
 return {''.join(rng.choice('abé中😀\\\n\t".0123') for _ in range(rng.randrange(6))):random_value(rng,depth+1) for _ in range(rng.randrange(6))}
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354862);p.add_argument('--fixtures',type=int,default=2);p.add_argument('--random-cases',type=int,default=128);p.add_argument('--component-replay',action='store_true');p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=600);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 fixed=[]
 def add(group,expr):fixed.append(dict(group=group,expression=expr))
 for text in ['', ' ', '/*x*/','//x','{} x','{a:1} x','[1,] x','[ /*x*/ ]x','{a /*x*/ : 1}x','{true:1}', '[null', '0e+', '+01', '-.e1','["é😀中",]', '["é😀中" bad]', '{"é😀中":}', '"é😀中\\q"', '"é😀中', '1\0junk']:
  add('fixed-position',literal(text))
 for expr in ['NULL','0','-9223372036854775808','1.25','1e999','-1e999','CAST(1e999-1e999 AS REAL)',blob(b'null'),blob(b'1234')]:add('fixed-storage',expr)
 for depth in [999,1000,1001]:
  data=b'\x00'
  for _ in range(depth):data=node(11,data)
  for expr in [literal('['*depth+'0'+']'*depth),blob(data)]:add('fixed-depth',expr)
 if a.component_replay:
  report=json.loads((ROOT/'docs/validation/sqlite-json-position-component-20261026.json').read_text())
  for x in report['cases']:
   encoded=x['input'];expr='NULL' if encoded=='N' else (blob if encoded[0]=='B' else literal)(bytes.fromhex(encoded[1:]));add('fixed-component-replay',expr)
 queries=[]
 def query(group,sql):queries.append(dict(group=group,sql=sql))
 for fn in ['json_error_position','JSON_ERROR_POSITION']:
  for args in ['', '*', '1,2', 'DISTINCT 1,2']:
   call=fn+'('+args+')'
   for expr in [call,'0 AND '+call,'1 IN ('+call+')','CASE WHEN 0 THEN '+call+' ELSE 1 END']:
    for tail in ['', ' FROM t LIMIT 0']:
     query('fixed-admission','SELECT '+expr+tail+';')
 for count in [1000,1001]:query('fixed-argument-limit','SELECT json_error_position('+','.join(['1']*count)+');')
 for sql in ['SELECT json_error_position(abs(-9223372036854775808));','SELECT json_error_position("missing");','SELECT json_error_position(DISTINCT 1);','SELECT 0 AND json_error_position("missing");','SELECT count(*),sum(json_error_position(v)),min(json_error_position(v)),max(json_error_position(v)) FROM t;', 'SELECT json_error_position(v),count(*) FROM t GROUP BY json_error_position(v) ORDER BY 1;', 'SELECT id,json_error_position(v) AS p FROM t WHERE json_error_position(v)>0 ORDER BY p,id LIMIT 17;', 'SELECT t.id,json_error_position(t.v) FROM t JOIN u ON u.id=t.id WHERE t.id BETWEEN 0 AND 19 ORDER BY t.id;', 'SELECT id,CASE WHEN json_error_position(v) THEN json_error_position(v)+10 ELSE 0 END FROM t WHERE id<20 ORDER BY id;']:
  query('fixed-query-shape',sql)
 cases=[];runs=[];fixtures=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-position-') as tmp:
  for fixture in range(a.fixtures):
   values=list(fixed)
   for _ in range(a.random_cases):
    value=random_value(rng);data=json.dumps(value,ensure_ascii=bool(rng.randrange(2)),separators=(',',':')).encode();encoded=csql(':memory:','SELECT hex(jsonb('+literal(data)+'));');assert encoded['code']==0,encoded
    binary_value=bytes.fromhex(encoded['stdout'].strip())
    for expr in [literal(data),blob(binary_value),literal(mutate(rng,data)),blob(mutate(rng,binary_value)),literal(data+rng.choice([b' x',b' /*',b'\0tail',b'\xff'])),blob(bytes(rng.randrange(256) for _ in range(rng.randrange(1,64))))]:values.append(dict(group='seeded-input',expression=expr))
   page=512<<(fixture%8);folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db'
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v);CREATE TABLE u(id INTEGER PRIMARY KEY);BEGIN;'+''.join('INSERT INTO t VALUES('+str(i)+','+v['expression']+');' for i,v in enumerate(values))+''.join('INSERT INTO u VALUES('+str(i)+');' for i in range(20))+'COMMIT;';made=csql(base,setup);assert made['code']==0,made
   fixtures.append(dict(fixture=fixture,page_size=page,values=values))
   sql='SELECT id,typeof(json_error_position(v)),quote(json_error_position(v)),json_valid(v,2),json_valid(v,8) FROM t ORDER BY id;'
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
    l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);ll,cl=l['stdout'].splitlines(),c['stdout'].splitlines();assert len(cl)==len(values),c
    for i,wanted in enumerate(cl):
     actual=ll[i] if i<len(ll) else None;cases.append(dict(fixture=fixture,page_size=page,mode=mode,input=i,group=values[i]['group'],lean=actual,sqlite=wanted,matched=actual==wanted))
    runs.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=c,matched=same(l,c)))
    for q in queries:
     l=run([str(binary),mode,str(left)],q['sql']);c=csql(right,q['sql']);cases.append(dict(q,fixture=fixture,page_size=page,mode=mode,lean=l,sqlite=c,lean_error=error(l),sqlite_error=error(c),matched=same(l,c)))
    obs='PRAGMA integrity_check;SELECT id,typeof(v),hex(v) FROM t ORDER BY id;';lo,co=csql(left,obs),csql(right,obs)
    runs.append(dict(fixture=fixture,page_size=page,mode=mode,observation_lean=lo,observation_sqlite=co,lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),matched=lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and bl==snapshot(left) and br==snapshot(right)))
 assert source==digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 failures=sum(not x['matched'] for x in cases+runs);report=dict(seed=a.seed,random_cases=a.random_cases,component_replay=a.component_replay,fixtures=fixtures,cases=cases,runs=runs,failures=failures,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
