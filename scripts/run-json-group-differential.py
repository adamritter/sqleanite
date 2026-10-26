#!/usr/bin/env python3
"""Ordinary JSON aggregates through both public Core file engines.

Fixed byte/header/nesting/diagnostic controls mix with newly seeded rows, keys,
JSON values and unfiltered mutations. Compare complete raw and quoted bytes,
runtime subtype, status and first diagnostic. Every request is independent;
errors never filter later cases. GROUP BY, HAVING, DISTINCT, FILTER, argument
ORDER BY, joined inputs and interleaved errors are included. Window functions
are not implemented or claimed by this ordinary-aggregate corpus.
"""
import argparse,concurrent.futures,hashlib,importlib.util,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('position_corpus',ROOT/'scripts/run-json-position-differential.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
literal=helpers.literal;blob=helpers.blob;node=helpers.node

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=355251);p.add_argument('--fixtures',type=int,default=2);p.add_argument('--random-cases',type=int,default=16);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
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
 functions=['json_group_array','jsonb_group_array','json_group_object','jsonb_group_object']
 fixed=['NULL','0','1','1.0','1.5','1e999','-1e999','9223372036854775807','-9223372036854775808',"''","'{}'","'[1,2]'","'null'",literal(b'a\0b'),literal(bytes(range(256))),"X'ff'","X''","jsonb('{}')","jsonb('[1,2]')"]
 for kind in range(16):
  for payload in [b'',b'1',b'\\q',b'\xff',b'\x17a\x00',b'1\x002']:fixed.append(blob(node(kind,payload)))
 keys=['NULL',"''","'a'","X''","X'ff'",'1','1.5','1e999',literal(b'@\0tail'),literal(b'a\0b'),literal(b'\\"@'),"json('{}')"]
 def call(fn,value='v',key='k',distinct=False,order='',filt=''):
  return fn+'('+('DISTINCT ' if distinct else '')+(key+',' if 'object' in fn else '')+value+(' ORDER BY '+order if order else '')+')'+(' FILTER(WHERE '+filt+')' if filt else '')
 def typed(expr):return 'typeof('+expr+'),subtype('+expr+'),hex('+expr+'),hex(quote('+expr+'))'
 def run_fixture(fixture,page,folder,base,queries):
  cases=[];runs=[]
  for mode in ['--verified-file','--verified-wal-file']:
   left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
   for q in queries:
    l=run([str(binary),mode,str(left)],q['sql']);c=csql(right,q['sql']);cases.append(dict(q,fixture=fixture,page_size=page,mode=mode,lean=compact(l),sqlite=compact(c),matched=helpers.same(l,c)))
   obs='PRAGMA integrity_check;SELECT id,g,typeof(k),hex(k),typeof(v),hex(v) FROM t ORDER BY id;';lo,co=csql(left,obs),csql(right,obs)
   runs.append(dict(fixture=fixture,page_size=page,mode=mode,lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),observation_lean=compact(lo),observation_sqlite=compact(co),matched=lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and bl==snapshot(left) and br==snapshot(right)))
  return cases,runs
 cases=[];runs=[];fixtures=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-group-') as tmp, concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  futures=[]
  for fixture in range(a.fixtures):
   values=list(fixed)
   for i in range(a.random_cases):
    text=json.dumps(helpers.random_value(rng),ensure_ascii=False);value=literal(text)
    values.extend([value,'jsonb('+value+')',blob(helpers.mutate(rng,text.encode()))])
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=512<<(fixture%8)
   rows=[dict(id=i+1,g=i%4,k=rng.choice(keys),v=v) for i,v in enumerate(values)]
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,g,k,v);CREATE TABLE u(id INTEGER PRIMARY KEY,m);CREATE TABLE u_gap(id INTEGER PRIMARY KEY,m);CREATE TABLE u_empty(id INTEGER PRIMARY KEY,m);BEGIN;'+''.join(f"INSERT INTO t VALUES({x['id']},{x['g']},{x['k']},{x['v']});INSERT INTO u VALUES({x['id']},{x['id']%2});" for x in rows)+''.join(f'INSERT INTO u_gap VALUES({i},{i%2});' for i in list(range(1,10))+[len(values)+1,len(values)+2] if i%3)+'COMMIT;'
   made=csql(base,setup);assert made['code']==0,made;queries=[]
   def add(group,sql):queries.append(dict(group=group,sql=sql))
   def select(group,expr,tail=' FROM t',prefix=''):add(group,'SELECT '+prefix+typed(expr)+tail+';')
   for fn in functions:
    for i in range(1,len(values)+1):
     for span in [f'id={i}',f'id BETWEEN {i} AND {i+2}']:select('independent-rows',call(fn),' FROM t WHERE '+span)
    for value in ['v','json(v)',"json_array(v)","jsonb_array(v)","CAST(jsonb_array(v) AS TEXT)","CASE WHEN id%2 THEN json('{}') ELSE '{}' END"]:
     expr=call(fn,value)
     for where in ['',' WHERE 0',' WHERE id<=15',' WHERE id<=2',' WHERE k IS NULL']:
      select('fixed-whole-input',expr,' FROM t'+where)
      for tail in ['', ' ORDER BY g',' ORDER BY g DESC',' ORDER BY g LIMIT 1 OFFSET 1',' HAVING count(*)>1 ORDER BY g']:
       select('fixed-group',expr,' FROM t'+where+' GROUP BY g'+tail,'g,')
     for order in ['id','id DESC','v','v COLLATE nocase','v DESC NULLS LAST','g,id DESC','abs(-9223372036854775808)']:
      for distinct in [False,True]:select('fixed-internal-order',call(fn,value,distinct=distinct,order=order),' FROM t WHERE id<=15')
     for filt in ['0','1','id<=15','id=1','abs(-9223372036854775808)']:
      select('fixed-filter',call(fn,value,filt=filt))
     for wrapper in ['json_array','jsonb_array','json_quote']:
      select('nested-aggregate-subtype',wrapper+'('+expr+')',' FROM t WHERE id<=15')
    for args in ['', '*','1','1,2','1,2,3','DISTINCT 1','DISTINCT 1,2']:
     for tail in ['', ' FROM t WHERE 0',' FROM t LIMIT 0']:
      add('fixed-arity','SELECT '+fn.upper()+'('+args+')'+tail+';')
    for key in keys:
     if 'object' in fn:select('fixed-key-coercion',call(fn,'v',key),' FROM t WHERE id<=15')
    for key in ['NULL',"'k'"]:
     for value in ["X'ff'","X'03'",'abs(-9223372036854775808)']:
      select('fixed-null-key-errors',call(fn,value,key),' FROM t WHERE id<=3')
    for table in ['u','u_gap','u_empty']:
     for join in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']:
      expr=call(fn,'t.v','t.k')
      select('fixed-join',expr,f' FROM t {join} {table} ON t.id={table}.id WHERE t.id<=15')
      select('fixed-unmatched-join',expr,f' FROM t {join} {table} ON t.id={table}.id WHERE t.id<=15 OR t.id IS NULL')
      select('fixed-joined-group',expr,f' FROM t {join} {table} ON t.id={table}.id WHERE t.id<=15 GROUP BY {table}.m ORDER BY {table}.m',table+'.m,')
      select('fixed-unmatched-joined-group',expr,f' FROM t {join} {table} ON t.id={table}.id WHERE t.id<=15 OR t.id IS NULL GROUP BY {table}.m ORDER BY {table}.m',table+'.m,')
    add('fixed-misuse','SELECT v FROM t WHERE '+call(fn)+'>0;')
    add('fixed-nested-aggregate','SELECT '+call(fn,'sum(v)')+' FROM t;')
    select('fixed-no-source',call(fn,"json('{}')","'k'"),'')
    for first in ["X'ff'","X'03'","X'1bff'","X'00'"]:
     value=f'CASE WHEN id=1 THEN {first} ELSE abs(-9223372036854775808) END'
     for order in ['','id DESC']:
      expr=call(fn,value,order=order)
      for tail in [' WHERE id<=3',' WHERE id<=3 LIMIT 0',' WHERE id<=3 GROUP BY g ORDER BY g',' WHERE id<=3 GROUP BY g ORDER BY g LIMIT 1 OFFSET 1']:
       select('fixed-row-error-order',expr,' FROM t'+tail)
      for pred in ['CASE WHEN id=2 THEN abs(-9223372036854775808) ELSE 1 END','id<=3']:
       select('fixed-where-error-order',expr,' FROM t WHERE '+pred)
    errors=[call(fn,"X'ff'"),call(fn,"X'03'"),call(fn,"X'ff'",order='id'),'sum(abs(-9223372036854775808))','sum(CASE WHEN id=1 THEN 9223372036854775807 ELSE 1 END)',call(fn,"X'03'",filt='0')]
    for first in errors:
     for second in errors:add('fixed-interleaved-errors','SELECT '+first+','+second+' FROM t WHERE id<=3;')
   for depth in [998,999,1000,1001,1002]:
    raw=b'\x00'
    for _ in range(depth):raw=node(11,raw)
    for fn in functions:
     for later in ['NULL','abs(-9223372036854775808)',"X'03'","X'ff'"]:
      value='CASE WHEN id=1 THEN '+blob(raw)+' ELSE '+later+' END'
      select('fixed-depth-error-timing',call(fn,value,"'k'"),' FROM t WHERE id<=2')
   for size in [11,12,255,256,65535,65536]:
    for fn in functions:select('fixed-output-header-size',call(fn,literal('x'*size),"'k'"),' FROM t WHERE id<=2')
   for raw in [b'@',b'@@',b'@,',b'"@"',b'1,@,2',b'\\@',b'{"@":1}',b'',b'"',b'\\',b',@,',b'[@,@]']:
    value='CAST(jsonb('+blob(node(3,raw))+') AS TEXT)'
    for fn in ['json_group_object','jsonb_group_object']:
     for pos in [1,2,3]:select('fixed-marker-cleanup',call(fn,value,f"CASE WHEN id={pos} THEN NULL ELSE 'k' END"),' FROM t WHERE id<=3')
   for i in range(a.random_cases):
    fn=rng.choice(functions);lo=rng.randrange(0,len(values)+1);hi=lo+rng.randrange(1,16);expr=call(fn,rng.choice(['v','json(v)','json_array(v)','jsonb_array(v)',"CASE WHEN id%2 THEN json('{}') ELSE v END"]),rng.choice(['k','NULL','v','id']),rng.choice([False,True]),rng.choice(['','id','id DESC','v','g,id']),rng.choice(['','id%2','0']))
    select('seeded-query',expr,f' FROM t WHERE id BETWEEN {lo} AND {hi}'+rng.choice(['',' GROUP BY g ORDER BY g',' LIMIT 0',' LIMIT 1 OFFSET 1']))
   fixtures.append(dict(fixture=fixture,page_size=page,setup=setup,inputs=rows));futures.append(pool.submit(run_fixture,fixture,page,folder,base,queries))
  for future in futures:
   rows,observations=future.result();cases.extend(rows);runs.extend(observations)
 assert source==helpers.digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 failures=sum(not x['matched'] for x in cases+runs);report=dict(seed=a.seed,random_cases=a.random_cases,fixtures=fixtures,cases=cases,runs=runs,failures=failures,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),helper_sha256=hashlib.sha256(Path(helpers.__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
