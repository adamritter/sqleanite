#!/usr/bin/env python3
"""Compare json_pretty() bytes, diagnostics and composition through public SQL.

New seeded documents, C JSONB and unfiltered mutations mix with fixed JSON5,
indent storage classes, binary payload/header and nesting limits. Every input
runs separately with default/custom indentation, followed by separate composition
checks. Full output, status, normalized first diagnostic, unchanged file bytes
and independent C integrity/typed rows must match. Large output is represented
by SHA-256, length and prefix only after exact comparison, without filtering.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('position_corpus',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
literal=helpers.literal;blob=helpers.blob;node=helpers.node;mutate=helpers.mutate;random_value=helpers.random_value

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354992);p.add_argument('--fixtures',type=int,default=2);p.add_argument('--random-cases',type=int,default=32);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=helpers.digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=180);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 def compact(result):
  out=dict(result)
  if len(out['stdout'])>8192:
   data=out.pop('stdout').encode('latin1');out.update(stdout_sha256=hashlib.sha256(data).hexdigest(),stdout_bytes=len(data),stdout_prefix=data[:512].decode('latin1'))
  return out
 indents=['NULL',"''","' '","'--'",'0','1.25','1e999',"X'090a'","X'ff00ab'","CAST(X'00ffff' AS TEXT)","CAST(X'e4b8ad' AS TEXT)"]
 fixed=[]
 for text in ['null','{}','[1,2]','1','1.0','',' ','invalid','[','{true:1}','{a:1,}',"{'x':'a\"b'}",'"\\u0041"',"'\\x41'",'"a\x01b"','1\0tail','+.1','-0xFF','1.e2','Inf','-Infinity','NaN','0xFFFFFFFFFFFFFFFF','0x10000000000000000',"{x:'a\\\r\nb'}"]:
  for expr in [literal(text),blob(text.encode())]:fixed.append(dict(group='fixed-text-storage',expression=expr))
 for expr in ['NULL','0','-9223372036854775808','9223372036854775807','1.25','1e999','-1e999',"X'00'","X'0b'","X'c000'","X'1bff'","X'00ff'","X'f900000000000000025c00'","X'1b00'","X'3c176100'"]:
  fixed.append(dict(group='fixed-storage',expression=expr))
 for n in [11,12,255,256,65535,65536]:fixed.append(dict(group='fixed-header-size',expression=literal(json.dumps('x'*n))))
 for depth in [998,999,1000,1001]:
  data=b'\x00'
  for _ in range(depth):data=node(11,data)
  for expr in [literal('['*depth+'0'+']'*depth),blob(data)]:fixed.append(dict(group='fixed-depth',expression=expr))
 queries=[]
 def query(group,sql):queries.append(dict(group=group,sql=sql))
 for fn in ['json_pretty','JSON_PRETTY']:
  for args in ['', '*','1,2,3','DISTINCT 1,2,3']:
   call=fn+'('+args+')'
   for expr in [call,'0 AND '+call,'1 IN ('+call+')','CASE WHEN 0 THEN '+call+' ELSE 1 END']:
    for tail in ['', ' FROM t LIMIT 0']:query('fixed-admission','SELECT '+expr+tail+';')
 for count in [1000,1001]:query('fixed-argument-limit','SELECT json_pretty('+','.join(['1']*count)+');')
 for indent in indents:query('fixed-indent',"SELECT typeof(json_pretty('[1,{a:2}]',"+indent+")),hex(json_pretty('[1,{a:2}]',"+indent+"));")
 for sql in ["SELECT hex(json_pretty(DISTINCT 1));","SELECT hex(json_pretty(DISTINCT 1,2));",'SELECT json_pretty(abs(-9223372036854775808));','SELECT json_pretty("missing");','SELECT 0 AND json_pretty("missing");','SELECT id FROM t WHERE json_pretty(v) ORDER BY id;','SELECT id,hex(json_pretty(v)) FROM t ORDER BY id;','SELECT id,hex(json_pretty(v)) FROM t ORDER BY id DESC;','SELECT count(*),hex(min(json_pretty(v))),hex(max(json_pretty(v))) FROM t;', 'SELECT hex(json_pretty(v)),count(*) FROM t GROUP BY json_pretty(v) ORDER BY 1;', 'SELECT id,hex(json_pretty(v)) AS b FROM t WHERE id<10 ORDER BY b,id LIMIT 4;', 'SELECT t.id,hex(json_pretty(t.v)) FROM t JOIN u ON t.id=u.id ORDER BY t.id;']:
  query('fixed-query-shape',sql)
 cases=[];runs=[];fixtures=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-pretty-') as tmp:
  for fixture in range(a.fixtures):
   values=list(fixed)
   for _ in range(a.random_cases):
    data=json.dumps(random_value(rng),ensure_ascii=bool(rng.randrange(2)),separators=(',',':')).encode();encoded=csql(':memory:','SELECT hex(jsonb('+literal(data)+'));');assert encoded['code']==0;binary_value=bytes.fromhex(encoded['stdout'].strip())
    for expr in [literal(data),blob(binary_value),literal(mutate(rng,data)),blob(mutate(rng,binary_value)),literal(data+rng.choice([b' x',b' /*',b'\0tail',b'\xff'])),blob(rng.randbytes(rng.randrange(1,64)))]:values.append(dict(group='seeded-input',expression=expr))
   values=[dict(v,indent=rng.choice(indents)) for v in values]
   page=512<<(fixture%8);folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db'
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v,indent);CREATE TABLE u(id INTEGER PRIMARY KEY);BEGIN;'+''.join(f'INSERT INTO t VALUES({i},'+v['expression']+','+v['indent']+');' for i,v in enumerate(values))+''.join(f'INSERT INTO u VALUES({i});' for i in range(20))+'COMMIT;';made=csql(base,setup);assert made['code']==0,made;fixtures.append(dict(fixture=fixture,page_size=page,values=values))
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
    for i,value in enumerate(values):
     for call in ['json_pretty(v)','json_pretty(v,indent)']:
      sql=f'SELECT typeof({call}),hex({call}) FROM t WHERE id={i};';l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);cases.append(dict(fixture=fixture,page_size=page,mode=mode,input=i,group=value['group'],sql=sql,lean=compact(l),sqlite=compact(c),matched=helpers.same(l,c)))
     sql=f'SELECT hex(json_pretty(jsonb(v),indent)),json_error_position(json_pretty(v,indent)) FROM t WHERE id={i};';l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);cases.append(dict(fixture=fixture,page_size=page,mode=mode,input=i,group='composition-'+value['group'],sql=sql,lean=compact(l),sqlite=compact(c),matched=helpers.same(l,c)))
    for q in queries:
     l=run([str(binary),mode,str(left)],q['sql']);c=csql(right,q['sql']);cases.append(dict(q,fixture=fixture,page_size=page,mode=mode,lean=compact(l),sqlite=compact(c),matched=helpers.same(l,c)))
    obs='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(indent),hex(indent) FROM t ORDER BY id;';lo,co=csql(left,obs),csql(right,obs);runs.append(dict(fixture=fixture,page_size=page,mode=mode,observation_lean=compact(lo),observation_sqlite=compact(co),lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),matched=lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and bl==snapshot(left) and br==snapshot(right)))
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 failures=sum(not x['matched'] for x in cases+runs);report=dict(seed=a.seed,random_cases=a.random_cases,fixtures=fixtures,cases=cases,runs=runs,failures=failures,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
