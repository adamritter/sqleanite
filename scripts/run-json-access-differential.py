#!/usr/bin/env python3
"""Compare JSON type/array length and path lookup through both public file engines.

New seeded documents, paths and binary mutations mix with fixed syntax, depth,
arity and query-shape controls. Complete stdout/status and normalized first-line
errors are compared. File reads must preserve main/WAL bytes; independent C
checks integrity and typed rows. No oracle outcomes filter the generated cases.
"""
import argparse,hashlib,json,os,random,re,shutil,subprocess,tempfile,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest(root):
 h=hashlib.sha256()
 for p in sorted((root/'SQLeanite').rglob('*.lean'))+[root/'Main.lean']:h.update(str(p.relative_to(root)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def literal(s):
 data=s.encode() if isinstance(s,str) else s
 return "CAST(X'"+data.hex()+"' AS TEXT)"
def blob(data):return "X'"+data.hex()+"'"
def node(kind,data):
 n=len(data);w=0 if n<12 else 1 if n<256 else 2 if n<65536 else 4
 return bytes([(n if not w else {1:12,2:13,4:14}[w])*16+kind])+(n.to_bytes(w,'big') if w else b'')+data
def error(r):
 if not r['code']:return ''
 line=r['stderr'].splitlines()[0] if r['stderr'] else ''
 return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',line)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354802);p.add_argument('--fixtures',type=int,default=2);p.add_argument('--random-cases',type=int,default=64);p.add_argument('--controls',type=Path);p.add_argument('--implementation-root',type=Path,default=ROOT);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 root=a.implementation_root.resolve();binary=root/'.lake/build/bin/sqleanite';sqlite=os.environ.get('SQLITE3_BIN','sqlite3');source=digest(root);exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=120)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 basecases=[]
 def add(group,value,path=None):
  args=value+('' if path is None else ','+path)
  for fn in ['json_type','json_array_length']:
   expr=f'{fn}({args})';basecases.append(dict(group=group,sql=f'SELECT typeof({expr}),quote({expr});'))
 paths=['$', '$.a', '$[0]', '$[#-1]', '$[#]', '$[#-999bad]', '$[9999999999999999]', '$.missing[bad]', '$.','$."','$."\\u0061"','$."a\\u0000b"']
 for value in ['null','1','1e2','+0xabc','NaN','Infinity','[]','{}','[1,{},[2]]','{"a":[1,2],"a":0}',"{a:[1,],b:'x'}",'"a"','invalid','[','']:
  for path in [None]+paths:add('text-path-controls',literal(value),None if path is None else literal(path))
 for value in ['NULL','0','1.25','1e999',blob(b'null'),blob(b'1234')]:
  for path in [None,'NULL','0',blob(b'$')]:add('sql-storage',value,path)
 for kind in range(16):
  for data in [b'',b'\xff',b'\x17a\x00',b'\x13a\x00']:
   for path in [None,literal('$[0]'),literal('$.a')]:add('binary-tag',blob(node(kind,data)),path)
 for depth in [999,1000,1001]:
  text='['*depth+'0'+']'*depth;data=b'\x13\x30'
  for _ in range(depth):data=node(11,data)
  for val in [literal(text),blob(data)]:
   for path in [None,literal('$'+'[0]'*(depth-1)),literal('$'+'[0]'*depth)]:add('depth',val,path)
 for value in [literal('0'),literal('{}'),literal('{"a":1}')]:
  for path in [b'$.\xff',b'$\xff',b'$."\xff',b'$\0ignored',b"x'y"]:add('path-bytes',value,literal(path))
 if a.controls:
  for c in json.loads(a.controls.read_text())['cases']:add('fixed-component-replay',c['sql_value'],c['sql_path'])
 for fn in ['json_type','json_array_length']:
  for call in [fn+'()',fn.upper()+'(1,2,3)',fn+'(*)']:
   for expr in [call,'0 AND '+call,'CASE WHEN 0 THEN '+call+' ELSE 1 END','1 IN ('+call+')']:
    basecases.append(dict(group='preparation',sql='SELECT '+expr+' FROM t LIMIT 0;'))
  for q in [f'SELECT id,{fn}(v) FROM t;',f'SELECT id,{fn}(v,p) FROM t ORDER BY id;',f'SELECT {fn}(v) FROM t WHERE id<6 ORDER BY {fn}(v);',f'SELECT {fn}(v),count(*) FROM t WHERE id<6 GROUP BY {fn}(v);',f'SELECT sum({fn}(v)) FROM t;',f'SELECT {fn}(NULL,abs(-9223372036854775808));',f'SELECT {fn}("bad",NULL);']:
   basecases.append(dict(group='query-shape',sql=q))
  for args in ["'bad',NULL", "NULL,'bad'", "'[',NULL"]:
   basecases.append(dict(group='null-path-error-order',sql=f'SELECT {fn}({args});'))
  for count in [1000,1001]:
   basecases.append(dict(group='argument-limit',sql='SELECT '+fn+'('+','.join(['1']*count)+');'))

 def random_value(depth=0):
  pick=rng.randrange(8 if depth<3 else 6)
  if pick==0:return None
  if pick==1:return rng.choice([True,False])
  if pick==2:return rng.randrange(-10**15,10**15)
  if pick==3:return rng.random()*10**rng.randrange(-15,15)
  if pick<6:return ''.join(rng.choice('abé中😀\\\n\t"0123') for _ in range(rng.randrange(16)))
  if pick==6:return [random_value(depth+1) for _ in range(rng.randrange(5))]
  return {''.join(rng.choice('abé中😀\\\n\t".0123') for _ in range(rng.randrange(5))):random_value(depth+1) for _ in range(rng.randrange(5))}
 def actual_paths(value,path='$'):
  out=[path]
  if isinstance(value,list):
   for i,v in enumerate(value):out+=actual_paths(v,path+f'[{i}]')
  elif isinstance(value,dict):
   for k,v in value.items():out+=actual_paths(v,path+'.'+json.dumps(k,ensure_ascii=bool(rng.randrange(2))))
  return out
 cases=[];fixtures=[];generated=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-access-') as tmp:
  for fixture in range(a.fixtures):
   queries=list(basecases)
   for _ in range(a.random_cases):
    value=random_value();text=json.dumps(value,ensure_ascii=bool(rng.randrange(2)),separators=(',',':'));paths2=actual_paths(value)
    result=csql(':memory:','SELECT hex(jsonb('+literal(text)+'));');assert result['code']==0,result
    data=bytes.fromhex(result['stdout'].strip());path=rng.choice(paths2)
    if rng.randrange(3)==0:path+=rng.choice(['.a','[0]','[#-1]','."','[bad]','xxx'])
    mutations=bytearray(data)
    pos=rng.randrange(len(mutations)+1);op=rng.randrange(3)
    if op==0:mutations[pos:pos]=bytes([rng.randrange(256)])
    elif pos<len(mutations) and op==1:del mutations[pos]
    elif pos<len(mutations):mutations[pos]=rng.randrange(256)
    generated.append(dict(fixture=fixture,text=text,jsonb=data.hex(),path=path,mutation=mutations.hex(),oracle=result))
    for val in [literal(text),blob(data),blob(mutations)]:
     for fn in ['json_type','json_array_length']:
      expr=fn+'('+val+','+literal(path)+')';queries.append(dict(group='seeded-input-path',sql=f'SELECT typeof({expr}),quote({expr});'))
   page=512<<(fixture%8);folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db'
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v,p);INSERT INTO t VALUES(1,\'null\',\'$\'),(2,\'[1,2]\',\'$[0]\'),(3,\'{{"a":[3]}}\',\'$.a\'),(4,NULL,NULL),(5,X\'0b\',\'$[#-1]\'),(6,\'bad\',\'$\');'
   made=csql(base,setup);assert made['code']==0,made
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
    for q in queries:
     l=run([str(binary),mode,str(left)],q['sql']);c=csql(right,q['sql'])
     cases.append(dict(q,fixture=fixture,page_size=page,mode=mode,lean=l,sqlite=c,lean_error=error(l),sqlite_error=error(c),matched=bool(l['code'])==bool(c['code']) and l['stdout']==c['stdout'] and error(l)==error(c)))
    obs='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(p),hex(p) FROM t ORDER BY id;';lo,co=csql(left,obs),csql(right,obs)
    fixtures.append(dict(fixture=fixture,mode=mode,page_size=page,setup=setup,lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),observation_lean=lo,observation_sqlite=co,matched=bl==snapshot(left) and br==snapshot(right) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n')))
 assert source==digest(root) and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 failures=sum(not c['matched'] for c in cases)+sum(not c['matched'] for c in fixtures)
 a.output.write_text(json.dumps(dict(seed=a.seed,random_cases=a.random_cases,controls=str(a.controls),cases=cases,fixtures=fixtures,generated=generated,failures=failures,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip()),indent=2)+'\n')
 print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
