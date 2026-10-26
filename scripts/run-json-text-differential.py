#!/usr/bin/env python3
"""Compare raw bytes (including after NUL), quoted values and public text JSON values and runtime subtypes, BLOB bytes, paths and diagnostics.

Fresh seeded JSON, C JSONB and unfiltered byte mutations mix with fixed numeric,
escape, nesting and header controls. Each JSON operation and nested subtype-propagation request is
executed independently. Full status/output/first diagnostic must match C; files
must stay unchanged and retain identical typed rows and C integrity. Large
observations are compacted only after exact comparison, never for acceptance.
"""
import argparse,concurrent.futures,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('position_corpus',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
literal=helpers.literal;blob=helpers.blob;node=helpers.node;mutate=helpers.mutate;random_value=helpers.random_value

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=355151);p.add_argument('--fixtures',type=int,default=2);p.add_argument('--random-cases',type=int,default=16);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
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
 paths=[literal(x) for x in ['a','v','a.b','a\\nb','é','','[0]','[#-1]','$','$.a','$.v[0]','$[0]','$[1]','$[#-1]','$[0].x','$."a.b"','$."a\\nb"','bad','$..a','$[foo]','$[999]',b'\xff',b'$\0bad']]+['NULL','0','-1','-9223372036854775808','1.0','1.25',"X'242e61'"]
 fixed=[]
 for s in ['null','{}','[]','1','1.0','-0.0','9223372036854775808','0xFFFFFFFFFFFFFFFF','-0xFFFFFFFFFFFFFFFF','0x10000000000000000','NaN','Inf','-.1','1.e2','','invalid','[','{a:1,}',"{'x':'\\xFF'}",'"\\uD800"','"\\uD800\\uDC00"','"a\\u0000b"','"a\x01b"','1\0tail','{"a":1,"a":2,"v":[2,{"x":3}]}','{"a.b":1,"a\\nb":2}']:
  for expression in [literal(s),blob(s.encode())]:fixed.append(dict(group='fixed-text-storage',expression=expression))
 for expression in ['NULL','0','-9223372036854775808','9223372036854775807','1.25','1e999','-1e999',"X'00'","X'0b'","X'c000'","X'1bff'","X'00ff'","X'f900000000000000025c00'"]:
  fixed.append(dict(group='fixed-storage',expression=expression))
 for kind in range(16):
  for payload in [b'',b'-',b'1\r2',b'0xFFFFFFFFFFFFFFFF',b'\\uD800',b'\\q',b'\x17a\x00',b'\xff']:
   fixed.append(dict(group='fixed-binary-node',expression=blob(node(kind,payload))))
 for size in [11,12,255,256,65535,65536]:fixed.append(dict(group='fixed-header-size',expression=literal(json.dumps('x'*size))))
 for depth in [998,999,1000,1001]:
  value=b'\x00'
  for _ in range(depth):value=node(11,value)
  for expression in [literal('['*depth+'0'+']'*depth),blob(value)]:fixed.append(dict(group='fixed-depth',expression=expression))
 def probe(base,choice):
  return [base,'+('+base+')','CAST(('+base+') AS TEXT)','CAST(('+base+') AS BLOB)','coalesce(('+base+'),NULL)','nullif(('+base+'),NULL)','CASE WHEN id%2 THEN '+base+' ELSE jsonb(v) END','min(('+base+'),('+base+")||'')",'max(('+base+'),('+base+")||'')",'subtype('+base+')'][choice]
 queries=[]
 def query(group,sql):queries.append(dict(group=group,sql=sql))
 for fn in ['json','json_extract','json_remove','json_patch','"->"','subtype']:
  for args in ['', '*',"'bad'",'1,2,3','DISTINCT 1',"NULL,'bad'","'bad',NULL","'{}','bad'","'{}',NULL","DISTINCT '{}','$','$'"]:
   for expr in [fn+'('+args+')','0 AND '+fn+'('+args+')','CASE WHEN 0 THEN '+fn+'('+args+') ELSE 1 END']:
    for tail in ['', ' FROM t LIMIT 0']:query('fixed-call-shape','SELECT '+expr+tail+';')
 for fn in ['json','json_extract','json_remove','json_patch','subtype']:
  call=fn+'('+','.join(['1']*1001)+')'
  query('fixed-argument-limit','SELECT '+call+';')
 for sql in ["SELECT id,subtype(v),subtype(p),subtype(q) FROM t WHERE id<10 ORDER BY id;","SELECT json(v) AS j,subtype(json(v)) FROM t WHERE subtype(j)=74 ORDER BY id LIMIT 3;","SELECT id,subtype(json(v)) FROM t ORDER BY id DESC;","SELECT hex(json(v)),subtype(json(v)),count(*) FROM t GROUP BY json(v) ORDER BY 1;","SELECT t.id,subtype(json(t.v)) FROM t JOIN u ON t.id=u.id ORDER BY t.id;","SELECT subtype(json(NULL)),subtype(json('null')),subtype(json_extract('null','$'));","SELECT subtype(CAST(json('{}') AS TEXT)),subtype(CAST(json('{}') AS BLOB));","SELECT 0 AND (missing -> '$');","SELECT CASE WHEN 0 THEN (missing -> '$') ELSE 1 END;"]:
  query('fixed-query-shape',sql)
 for fn in ['min','max']:
  for expr in ['json(v)','json_extract(v,\'$\')',"(v -> '$')"]:
   for extra in ['', ' GROUP BY id%2', ' ORDER BY 1']:
    call=fn+'('+expr+')'
    query('aggregate-subtype','SELECT typeof('+call+'),subtype('+call+'),hex('+call+') FROM t WHERE id<10'+extra+';')
 for expr in ["json('{}')","('{}' -> '$')","json_extract('{}','$')","json_remove('{}')","json_patch('{}','{}')"]:
  for wrapper in ['coalesce('+expr+",'x')",'iif(1,'+expr+",'x')",'min('+expr+",'{}')",'max('+expr+",'{}')",'min(\'{}\','+expr+')','max(\'{}\','+expr+')']:
   query('fixed-subtype-choice',f'SELECT typeof({wrapper}),subtype({wrapper}),hex({wrapper});')
 for fn in ['min','max']:
  for expr in ['json(v)',"CASE WHEN id%2 THEN json(v) ELSE v END","CASE WHEN id%2 THEN v ELSE json(v) END","CAST(json(v) AS BLOB)"]:
   for distinct in ['', 'DISTINCT ']:
    for filt in ['', ' FILTER (WHERE id%2)', ' FILTER (WHERE 0)']:
     call=fn+'('+distinct+expr+')'+filt
     for tail in ['', ' GROUP BY id%2', ' HAVING subtype('+call+')=74', ' GROUP BY id%2 HAVING subtype('+call+')=74 ORDER BY 1']:
      query('aggregate-runtime-boundary','SELECT typeof('+call+'),subtype('+call+'),hex('+call+'),hex(quote('+call+')) FROM t WHERE id<10'+tail+';')
 for fn in ['min','max']:
  call=fn+"(CASE WHEN t.id%2 THEN json(t.v) ELSE t.v END)"
  for extra in ['', ' GROUP BY t.id%2', ' HAVING subtype('+call+')=74']:
   query('joined-aggregate-runtime','SELECT typeof('+call+'),subtype('+call+'),hex('+call+') FROM t JOIN u ON t.id=u.id WHERE t.id<10'+extra+';')
 def run_fixture(fixture,page,folder,base,values):
  cases=[];runs=[]
  for mode in ['--verified-file','--verified-wal-file']:
   left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
   for i,value in enumerate(values):
    for call in ['json(v)','(v -> p)','json_extract(v,p)',"json_extract(v,p,'$')",'json_remove(v,p,p)','json_patch(v,q)',value['probe']]:
     sql=f'SELECT typeof({call}),subtype({call}),hex({call}),hex(quote({call})) FROM t WHERE id={i};';l=run([str(binary),mode,str(left)],sql);c=csql(right,sql);cases.append(dict(fixture=fixture,page_size=page,mode=mode,input=i,group=value['group'],sql=sql,lean=compact(l),sqlite=compact(c),matched=helpers.same(l,c)))

   for q in queries:
    l=run([str(binary),mode,str(left)],q['sql']);c=csql(right,q['sql']);cases.append(dict(q,fixture=fixture,page_size=page,mode=mode,lean=compact(l),sqlite=compact(c),matched=helpers.same(l,c)))
   obs='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(p),hex(p),typeof(q),hex(q) FROM t ORDER BY id;';lo,co=csql(left,obs),csql(right,obs);runs.append(dict(fixture=fixture,page_size=page,mode=mode,observation_lean=compact(lo),observation_sqlite=compact(co),lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),matched=lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and bl==snapshot(left) and br==snapshot(right)))
  return cases,runs
 cases=[];runs=[];fixtures=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-text-') as tmp, concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  futures=[]
  for fixture in range(a.fixtures):
   values=list(fixed)
   for _ in range(a.random_cases):
    data=json.dumps(random_value(rng),ensure_ascii=bool(rng.randrange(2)),separators=(',',':')).encode();encoded=csql(':memory:','SELECT hex(jsonb('+literal(data)+'));');assert encoded['code']==0;binary_value=bytes.fromhex(encoded['stdout'].strip())
    for expression in [literal(data),blob(binary_value),literal(mutate(rng,data)),blob(mutate(rng,binary_value)),literal(data+rng.choice([b' x',b' /*',b'\0tail',b'\xff'])),blob(rng.randbytes(rng.randrange(1,64)))]:values.append(dict(group='seeded-input',expression=expression))
   values=[dict(v,path=rng.choice(paths),path2=literal(json.dumps(random_value(rng),ensure_ascii=False)),probe=probe(rng.choice(['json(v)','(v -> p)','json_extract(v,p)']),rng.randrange(10))) for v in values]
   page=512<<(fixture%8);folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db'
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v,p,q);CREATE TABLE u(id INTEGER PRIMARY KEY);BEGIN;'+''.join(f'INSERT INTO t VALUES({i},'+v['expression']+','+v['path']+','+v['path2']+');' for i,v in enumerate(values))+''.join(f'INSERT INTO u VALUES({i});' for i in range(20))+'COMMIT;';made=csql(base,setup);assert made['code']==0,made;fixtures.append(dict(fixture=fixture,page_size=page,values=values))
   futures.append(pool.submit(run_fixture,fixture,page,folder,base,values))
  for future in futures:
   part_cases,part_runs=future.result();cases.extend(part_cases);runs.extend(part_runs)
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 failures=sum(not x['matched'] for x in cases+runs);report=dict(seed=a.seed,random_cases=a.random_cases,fixtures=fixtures,cases=cases,runs=runs,failures=failures,fixture_workers=2,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256((ROOT/'scripts/run-json-position-differential.py').read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
