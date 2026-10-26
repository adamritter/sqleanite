#!/usr/bin/env python3
"""Compare WHERE/aggregate scheduling through both public Core file modes.

Fresh seeded input rows, predicate/argument failure positions and query choices
mix with fixed ordering, FILTER, grouping, join, LIMIT and empty-input controls.
No oracle outcomes filter the corpus. Strictly compare full stdout, success/error
status and normalized first diagnostic, unchanged read bytes, persisted typed
rows, independent C integrity, Lean reopen and a subsequent C write. Page-size
conversion on writes is recorded separately. Dynamic ON expressions, unmatched
outer rows and empty joins are included; indexed streaming GROUP BY is outside
this corpus.
"""
import argparse,hashlib,json,os,random,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for f in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(f.relative_to(ROOT)).encode()+b'\0'+f.read_bytes())
 return h.hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=354942);p.add_argument('--fixtures',type=int,default=2);p.add_argument('--random-cases',type=int,default=64);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def error(r):return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',r['stderr'].splitlines()[0]) if r['code'] and r['stderr'] else ''
 def same(l,r):return bool(l['code'])==bool(r['code']) and l['stdout']==r['stdout'] and error(l)==error(r)
 def snapshot(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 cases=[];fixtures=[];runs=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-aggregate-predicate-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=512<<(fixture%8);n=rng.randrange(8,17)
   values=[rng.choice([str(rng.randrange(-1000,1000)),repr(rng.uniform(-1000,1000)),'NULL']) for _ in range(n)]
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,g,v);CREATE TABLE u(id INTEGER PRIMARY KEY,k);CREATE TABLE out(id INTEGER PRIMARY KEY,v);BEGIN;'+''.join(f'INSERT INTO t VALUES({i+1},{i%3},{v});INSERT INTO u VALUES({i+1},{i%2});' for i,v in enumerate(values))+'COMMIT;'
   setup+='CREATE TABLE u_gap(id INTEGER PRIMARY KEY,k);CREATE TABLE u_empty(id INTEGER PRIMARY KEY,k);'+''.join(f'INSERT INTO u_gap VALUES({i},{i%2});' for i in range(1,n+4) if i%5!=0)
   assert csql(base,setup)['code']==0;fixtures.append(dict(fixture=fixture,page_size=page,setup=setup));queries=[];writes=[]
   def add(group,expr,predicate,joined=False,tail='',write=False):
    source='t '+joined if isinstance(joined,str) else ('t JOIN u ON t.id=u.id' if joined else 't')
    sql=f'SELECT {expr} FROM {source} WHERE {predicate}{tail};'
    if write:sql='INSERT INTO out '+sql.replace('SELECT ','SELECT 1,',1)
    (writes if write else queries).append(dict(group=group,sql=sql))
   def expressions(bad):
    value=f"CASE WHEN t.id={bad} THEN 'x' ELSE t.v END";overflow=f'CASE WHEN t.id={bad} THEN abs(-9223372036854775808) ELSE t.v END'
    return [f'median({value})',f'median({value} ORDER BY t.id)',f'percentile(t.v,NULL)',f'percentile(t.v,NULL ORDER BY t.id)',f'sum({overflow})',f'sum({overflow} ORDER BY t.id)',f'group_concat(t.v,{overflow})',f'count({overflow})',f'median({value}),sum(t.v)',f't.id,median({value})',f'sum(CASE WHEN t.id={bad} THEN 9223372036854775807 ELSE 1 END)',f'median({value}) FILTER(WHERE t.id>1)', 'count(*)','min(t.v)','max(t.v)','avg(t.v)']
   for bad in [1,3,n]:
    for pred in [1,3,n]:
     where=f'CASE WHEN t.id={pred} THEN abs(-9223372036854775808) ELSE 1 END'
     for expr in expressions(bad):
      for joined in [False,True]:add('fixed-row-error-order',expr,where,joined)
     for expr in expressions(bad)[:8]:
      add('fixed-sort-before-group',expr,where,False,' GROUP BY t.g ORDER BY t.g')
      add('fixed-limit-zero',expr,where,False,' LIMIT 0')
     for expr in expressions(bad)[:4]:add('fixed-write-atomicity',expr,where,False,write=True)
   for pred in ['0','1','NULL','t.id>2','t.id%2=0','0 AND abs(-9223372036854775808)']:
    for expr in ['median(t.v)','sum(t.v)','avg(t.v)','group_concat(t.v)','t.id,min(t.v)','t.id,max(t.v)']:
     for joined in [False,True]:add('fixed-success-and-empty',expr,pred,joined)
    add('fixed-write-success','median(t.v)',pred,write=True)
   for table in ['u_gap','u_empty']:
    for join in ['JOIN','LEFT JOIN','RIGHT JOIN','FULL JOIN']:
     for on in [f't.id={table}.id',f't.id={table}.id AND CASE WHEN t.id=3 THEN abs(-9223372036854775808) ELSE 1 END']:
      joined=f'{join} {table} ON {on}'
      for expr in expressions(1)[:4]+['count(*)','sum(t.v)','t.id,min(t.v)','avg(t.v)']:
       for pred in ['1','CASE WHEN t.id=3 THEN abs(-9223372036854775808) ELSE 1 END']:
        add('fixed-joined-cursor-errors',expr,pred,joined)
      for expr in ['median(t.v)','count(*)']:
       add('fixed-joined-write',expr,'1',joined,write=True)
   for joined in ['JOIN u ON t.id=u.id','LEFT JOIN u_gap ON t.id=u_gap.id','RIGHT JOIN u_gap ON t.id=u_gap.id','FULL JOIN u_gap ON t.id=u_gap.id']:
    for expr in [expressions(5)[0],expressions(5)[1],expressions(5)[7]]:
     for tail in ['', ' ORDER BY t.g', ' ORDER BY t.g DESC', ' ORDER BY 1', ' ORDER BY t.g LIMIT 1', ' ORDER BY t.g LIMIT 1 OFFSET 1']:
      add('fixed-joined-group-prefix',expr,'1',joined,' GROUP BY t.g'+tail)
   for _ in range(a.random_cases):
    bad=rng.randrange(1,n+2);pred=rng.randrange(1,n+2);expr=rng.choice(expressions(bad));where=rng.choice([f'CASE WHEN t.id={pred} THEN abs(-9223372036854775808) ELSE 1 END',f't.id BETWEEN {rng.randrange(0,n)} AND {n} AND CASE WHEN t.id={pred} THEN abs(-9223372036854775808) ELSE 1 END',f'CASE WHEN t.id={pred} THEN abs(-9223372036854775808) ELSE t.id%2 END','1','0'])
    add('seeded-read',expr,where,rng.choice([False,True]),rng.choice(['',' LIMIT 0',' LIMIT 1 OFFSET 1',' HAVING 0',' GROUP BY t.g ORDER BY t.g']))
    add('seeded-write',rng.choice(expressions(bad)[:8]),where,rng.choice([False,True]),write=True)
   observation='PRAGMA integrity_check;SELECT type,name,tbl_name FROM sqlite_schema ORDER BY type,name;SELECT id,k FROM u ORDER BY id;SELECT id,k FROM u_gap ORDER BY id;SELECT id,k FROM u_empty ORDER BY id;SELECT id,g,typeof(v),quote(v) FROM t ORDER BY id;SELECT id,typeof(v),quote(v) FROM out ORDER BY id;'
   read='SELECT id,g,typeof(v),quote(v) FROM t ORDER BY id;SELECT id,typeof(v),quote(v) FROM out ORDER BY id;'
   for mode in ['--verified-file','--verified-wal-file']:
    left=folder/(mode+'-read-lean.db');right=folder/(mode+'-read-c.db');shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
    for q in queries:
     l=run([str(binary),mode,str(left)],q['sql']);c=csql(right,q['sql']);cases.append(dict(q,fixture=fixture,page_size=page,mode=mode,write=False,lean=l,sqlite=c,lean_error=error(l),sqlite_error=error(c),matched=same(l,c)))
    lo,co=csql(left,observation),csql(right,observation);runs.append(dict(fixture=fixture,mode=mode,lean=lo,sqlite=co,matched=lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and bl==snapshot(left) and br==snapshot(right)))
    for index,q in enumerate(writes):
     case_dir=folder/(mode+str(index));case_dir.mkdir();left=case_dir/'lean.db';right=case_dir/'sqlite.db';shutil.copyfile(base,left);shutil.copyfile(base,right);bl,br=snapshot(left),snapshot(right)
     l=run([str(binary),mode,str(left)],q['sql']);c=csql(right,q['sql']);al,ar=snapshot(left),snapshot(right);lo,co=csql(left,observation),csql(right,observation);lr,cr=run([str(binary),mode,str(left)],read),csql(right,read)
     geometry=dict(lean=csql(left,'PRAGMA page_size;'),sqlite=csql(right,'PRAGMA page_size;'))
     follow="INSERT INTO t VALUES(100000,0,'follow');SELECT id,g,typeof(v),quote(v) FROM t ORDER BY id;PRAGMA integrity_check;";lw,cw=csql(left,follow),csql(right,follow)
     matched=same(l,c) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and same(lr,cr) and lw['code']==cw['code']==0 and lw['stdout']==cw['stdout'] and (ar!=br or al==bl)
     cases.append(dict(q,fixture=fixture,page_size=page,mode=mode,write=True,lean=l,sqlite=c,lean_error=error(l),sqlite_error=error(c),observation_lean=lo,observation_sqlite=co,reopen_lean=lr,reopen_sqlite=cr,subsequent_c_write_lean=lw,subsequent_c_write_sqlite=cw,geometry=geometry,lean_unchanged=al==bl,sqlite_unchanged=ar==br,matched=matched))
 assert source==digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 failures=sum(not x['matched'] for x in cases+runs);report=dict(seed=a.seed,random_cases=a.random_cases,fixtures=fixtures,cases=cases,runs=runs,failures=failures,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),read_cases=sum(not x['write'] for x in cases),write_cases=sum(x['write'] for x in cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
