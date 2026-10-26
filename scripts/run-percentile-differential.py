#!/usr/bin/env python3
"""Ordinary median/percentile aggregates through both public Core file modes.

New seeded rows and fraction variants mix with fixed input-type, arithmetic,
DISTINCT, FILTER, ORDER BY, grouping, arity and error-priority controls. No
oracle outcome filters queries. Compare complete output, status and normalized
first diagnostic, then immutable files and independent C typed-row/integrity.
Window functions remain outside this ordinary-aggregate corpus.
"""
import argparse,hashlib,json,os,random,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def literal(s):
 if isinstance(s,str):s=s.encode()
 return "CAST(X'"+s.hex()+"' AS TEXT)"
def error(r):
 if not r['code']:return ''
 line=r['stderr'].splitlines()[0] if r['stderr'] else ''
 return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',line)
def same(l,r):return bool(l['code'])==bool(r['code']) and l['stdout']==r['stdout'] and error(l)==error(r)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354892);p.add_argument('--fixtures',type=int,default=2);p.add_argument('--random-cases',type=int,default=96);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  proc=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=120);return dict(code=proc.returncode,stdout=proc.stdout.decode('latin1'),stderr=proc.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 cases=[];fixtures=[];runs=[];functions=['median','percentile','percentile_cont','percentile_disc']
 with tempfile.TemporaryDirectory(prefix='sqleanite-percentile-') as tmp:
  for fixture in range(a.fixtures):
   values=[]
   for i in range(24):
    value=rng.choice([str(rng.randrange(-10**18,10**18)),repr(rng.uniform(-1e9,1e9)),rng.choice(['NULL','-0.0','0','1.25','1e308','-1e308','9223372036854775807','-9223372036854775808'])]);values.append((i+1,i%3,value,repr(.5+rng.uniform(-.00049,.00049))))
   for i,(value,parameter) in enumerate([(literal('1'),'0.5'),("X'31'",'0.5'),('1e999','0.5'),('-1e999','0.5'),('NULL','NULL'),('2',literal('.5')),('3',"X'302e35'"),('4','2')]):values.append((25+i,3,value,parameter))
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=512<<(fixture%8)
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,g,y,p);CREATE TABLE u(id INTEGER PRIMARY KEY,m);BEGIN;'+''.join(f'INSERT INTO t VALUES({i},{g},{y},{p});INSERT INTO u VALUES({i},{i%2});' for i,g,y,p in values)+'COMMIT;'
   made=csql(base,setup);assert made['code']==0,made;queries=[]
   def add(group,sql):queries.append(dict(group=group,sql=sql))
   for fn in functions:
    parameter='50' if fn=='percentile' else '.5';args='y' if fn=='median' else 'y,'+parameter;call=fn+'('+args+')'
    for where in ['', ' WHERE id<=24',' WHERE id<=2',' WHERE id=25',' WHERE id=26',' WHERE id=27',' WHERE id>=29',' WHERE 0',' WHERE y IS NULL']:
     add('fixed-typed-result',f'SELECT typeof({call}),quote({call}) FROM t{where};')
     for tail in ['',' ORDER BY g',' ORDER BY g DESC',' ORDER BY 2',' ORDER BY g LIMIT 1',' ORDER BY g LIMIT 1 OFFSET 1']:
      add('fixed-group',f'SELECT g,{call} FROM t{where} GROUP BY g'+tail+';')
    for ordering in ['id','id DESC','y','p DESC','abs(-9223372036854775808)']:
     add('fixed-aggregate-order',f'SELECT {fn}({args} ORDER BY {ordering}) FROM t WHERE id<=24;')
    for filt in ['0','1','id<=24','id=1','abs(-9223372036854775808)']:
     add('fixed-filter',f'SELECT {call} FILTER(WHERE {filt}) FROM t;')
    for args2 in ['', '*','1,2,3','DISTINCT 1,2','DISTINCT 1']:
     for tail in ['', ' FROM t LIMIT 0',' FROM t WHERE 0']:
      add('fixed-arity',f'SELECT {fn.upper()}({args2})'+tail+';')
    add('fixed-distinct',f'SELECT {fn}(DISTINCT {args}) FROM t WHERE id<=24;')
    add('fixed-join',f'SELECT u.m,{fn}({"t.y" if fn=="median" else "t.y,"+parameter}) FROM t JOIN u ON t.id=u.id WHERE t.id<=24 GROUP BY u.m ORDER BY u.m;')
    add('fixed-scalar-wrapper',f'SELECT abs({call}),{call}+1 FROM t WHERE id<=24;')
    add('fixed-having',f'SELECT g,{call} AS q FROM t WHERE id<=24 GROUP BY g HAVING q>0 ORDER BY g;')
    for value in ['NULL','1','1e999',literal('1')]:
     args2=value if fn=='median' else value+','+parameter;add('fixed-no-source',f'SELECT typeof({fn}({args2})),quote({fn}({args2}));')
    if fn!='median':
     for parameter in ['p','NULL','-1','101',literal('.5'),"X'302e35'",literal('.5\0tail'),"CASE WHEN id=2 THEN .5011 ELSE .5 END","CASE WHEN id=2 THEN .501 ELSE .5 END"]:
      add('fixed-fraction',f'SELECT {fn}(y,{parameter}) FROM t;');add('fixed-fraction',f'SELECT {fn}(y,{parameter}) FROM t WHERE id<=24;')
   for first,second in [('median(y)','percentile(y,NULL)'),('percentile(y,NULL)','median(y)'),('median(y)','sum(abs(-9223372036854775808))'),('sum(abs(-9223372036854775808))','median(y)')]:add('fixed-error-priority',f'SELECT {first},{second} FROM t;')
   # Interleave normal steps; ordered aggregates evaluate arguments during
   # scanning but defer steps/finalization until their sorters are drained.
   expressions=['median(y)','median(y ORDER BY id)','percentile(y,NULL)','percentile(y,NULL ORDER BY id)',
    'sum(abs(-9223372036854775808))','sum(abs(-9223372036854775808) ORDER BY id)',
    'sum(CASE WHEN id=1 THEN 9223372036854775807 ELSE 1 END)',
    'group_concat(abs(-9223372036854775808))','count(abs(-9223372036854775808))',
    'min(abs(-9223372036854775808))','max(abs(-9223372036854775808))',
    'median(y) FILTER (WHERE id<=24)','median(y) FILTER (WHERE 0)']
   for first in expressions:
    for second in expressions:
     add('fixed-interleaved-errors',f'SELECT {first},{second} FROM t;')
   for first in ['median(y)','median(y ORDER BY id)','percentile(y,NULL)','sum(abs(-9223372036854775808))']:
    for second in expressions[:6]:
     add('fixed-group-interleaved',f'SELECT g,{first},{second} FROM t GROUP BY g ORDER BY g;')
   add('fixed-nested-aggregate','SELECT median(sum(y)) FROM t;')
   add('fixed-misuse','SELECT y FROM t WHERE median(y)>0;')
   add('fixed-unsupported-ordered-set','SELECT percentile_cont(.5) WITHIN GROUP (ORDER BY y) FROM t;')
   for _ in range(a.random_cases):
    fn=rng.choice(functions);lo=rng.randrange(0,33);hi=lo+rng.randrange(1,12);p=repr(rng.uniform(-.05,1.05)*(100 if fn=='percentile' else 1));arg=rng.choice(['y','y+0.0','-y','CASE WHEN y IS NULL THEN 0 ELSE y END']);call=fn+'('+arg+('' if fn=='median' else ','+p)+')';where=f' WHERE id BETWEEN {lo} AND {hi}';add('seeded-query',f'SELECT typeof({call}),quote({call}) FROM t{where};')
   fixtures.append(dict(fixture=fixture,page_size=page,setup=setup))
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-lean.db');right=folder/(mode+'-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
    for q in queries:
     l=run([str(binary),mode,str(left)],q['sql']);c=csql(right,q['sql']);cases.append(dict(q,fixture=fixture,page_size=page,mode=mode,lean=l,sqlite=c,lean_error=error(l),sqlite_error=error(c),matched=same(l,c)))
    obs='PRAGMA integrity_check;SELECT id,g,typeof(y),hex(y),typeof(p),hex(p) FROM t ORDER BY id;';lo,co=csql(left,obs),csql(right,obs)
    runs.append(dict(fixture=fixture,page_size=page,mode=mode,observation_lean=lo,observation_sqlite=co,lean_unchanged=bl==snapshot(left),sqlite_unchanged=br==snapshot(right),matched=lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and bl==snapshot(left) and br==snapshot(right)))
 assert source==digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 failures=sum(not x['matched'] for x in cases+runs);report=dict(seed=a.seed,random_cases=a.random_cases,fixtures=fixtures,cases=cases,runs=runs,failures=failures,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
