#!/usr/bin/env python3
"""Compare stored raw result bytes, including bytes after NUL, and persist constructed JSON results and observe subtype erasure on storage and failures in both public Core file engines.

Pinned C supplies page geometry and input JSONB/JSON text. Newly seeded data and SQL
variants mix with fixed transaction/INSERT/UPDATE/DELETE/RETURNING/CTAS
templates. Each statement is delivered on its own input line so the pinned C
CLI honors -bail at the same boundary; the original template is also retained.
Same-line CLI continuation is documented separately. Compare full stdout, normalized first-line error, post-statement
C typed rows/schema shape/integrity, Lean reopen, and a subsequent independent C
write. Preserve unchanged files when C leaves its input unchanged. Page size
is recorded separately because the current writer may convert it to 4096.
"""
import argparse,hashlib,json,os,random,re,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest():
 h=hashlib.sha256()
 for p in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes())
 return h.hexdigest()
def literal(s):
 data=s.encode() if isinstance(s,str) else s
 return "CAST(X'"+data.hex()+"' AS TEXT)"
def statement_lines(sql):
 """Keep SQL tokens intact; put the next statement on a new CLI input line."""
 out=[];quote=None;i=0
 while i<len(sql):
  char=sql[i]
  if quote is not None:
   out.append(char)
   if char==quote:
    if quote!=']' and i+1<len(sql) and sql[i+1]==quote:
     out.append(sql[i+1]);i+=2;continue
    quote=None
   i+=1;continue
  if sql.startswith('--',i):
   end=sql.find('\n',i)
   if end<0:out.append(sql[i:]);break
   out.append(sql[i:end+1]);i=end+1;continue
  if sql.startswith('/*',i):
   end=sql.find('*/',i+2)
   if end<0:out.append(sql[i:]);break
   out.append(sql[i:end+2]);i=end+2;continue
  if char in "'\"`[":quote=']' if char=='[' else char
  out.append(char)
  if char==';':out.append('\n')
  i+=1
 return ''.join(out)

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--seed',type=int,default=355222);p.add_argument('--fixtures',type=int,default=4);p.add_argument('--random-cases',type=int,default=16);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed)
 sqlite=os.environ.get('SQLITE3_BIN','sqlite3');binary=ROOT/'.lake/build/bin/sqleanite';source=digest();exe=hashlib.sha256(binary.read_bytes()).hexdigest()
 def run(cmd,sql):
  r=subprocess.run(cmd,input=sql.encode(),capture_output=True,timeout=120)
  return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([sqlite,'-batch','-bail',str(path)],sql)
 def error(r):
  if not r['code']:return ''
  line=r['stderr'].splitlines()[0] if r['stderr'] else ''
  return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',line)
 def snapshot(path):
  return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 def same(l,r):return bool(l['code'])==bool(r['code']) and l['stdout']==r['stdout'] and error(l)==error(r)
 inputs=[literal(s) for s in ['null','1','[]','{"a":[1,true]}','{a:1}','[1,]','"\\x41"','invalid','[','01','1\0junk']]
 inputs += ['NULL','1','1.25',"X'00'","X'0b'","X'3c176100'","X'1bff'","X'c000'","X'00ff'"]
 inputs += [literal('"a\\u0000b"'),literal('"\\u0000tail"'),"X'3a610062'","X'37ff007a'"]
 generated=[]
 for _ in range(a.random_cases):
  value={'v':[rng.randrange(-100000,100000),rng.choice([None,True,False]),''.join(rng.choice('abé中😀') for _ in range(5))]}
  s=json.dumps(value,ensure_ascii=False);r=csql(':memory:','SELECT hex(jsonb('+literal(s)+'));');assert r['code']==0,r
  generated.append(dict(text=s,jsonb_hex=r['stdout'].strip()))
  inputs.extend([literal(s),"X'"+r['stdout'].strip()+"'"])
 scripts=[]
 def add(group,sql):scripts.append(dict(group=group,template_sql=sql,sql=statement_lines(sql)))
 expressions=['json_array(v,flags)','jsonb_array(v,flags)','json_object(flags,v)','jsonb_object(flags,v)','json_quote(v)','json_array(json(v),v,jsonb(v))','subtype(jsonb_array(v))','subtype(CAST(jsonb_array(v) AS BLOB))','json_array(CAST(jsonb_array(v) AS TEXT))']
 for expr in expressions:
  add('update',f'UPDATE t SET valid={expr};')
  add('insert-select',f'INSERT INTO out SELECT id,{expr} FROM t;')
  add('ctas',f'CREATE TABLE made AS SELECT id,{expr} AS valid FROM t;')
  add('delete',f'DELETE FROM t WHERE {expr}>0;')
  add('update-returning',f'UPDATE t SET valid={expr} WHERE id<=20 RETURNING id,valid;')
 for suffix in ['ROLLBACK;','COMMIT;']:
  add('transaction',"BEGIN;\nUPDATE t SET valid=json_array(v,'$[0]');\n"+suffix+'\nSELECT id,valid FROM t ORDER BY id;')
 add('savepoint',"SAVEPOINT j;\nUPDATE t SET valid=json_array(v,'$[0]');\nROLLBACK TO j;\nRELEASE j;\nSELECT id,valid FROM t ORDER BY id;")
 error_expr="json_array(CASE WHEN id=3 THEN abs(-9223372036854775808) ELSE v END,'$[0]')"
 add('atomic-error','UPDATE t SET valid='+error_expr+';')
 add('transaction-error',"BEGIN;\nUPDATE t SET valid=json_array(v,'$[0]');\nUPDATE t SET valid="+error_expr+';\nCOMMIT;')
 add('returning-error','UPDATE t SET valid=1 WHERE id<5 RETURNING id,'+error_expr+';')
 add('insert-returning',"INSERT INTO t VALUES(999,'[1,]',2,json_array('[1,]','$[0]')) RETURNING id,valid;")
 add('insert-error','INSERT INTO out SELECT id,'+error_expr+' FROM t;')
 add('ctas-error','CREATE TABLE made AS SELECT id,'+error_expr+' AS valid FROM t;')
 add('empty-argument-list','UPDATE t SET valid=json_array();')
 add('empty-argument-list','INSERT INTO out SELECT id,json_array(v) FROM t;')
 add('star-call','UPDATE t SET valid=json_array(*);')
 add('argument-limit',"UPDATE t SET valid=json_array('1',"+','.join(["'$'"]*1000)+') WHERE 0;')
 for expr in expressions[:3]:
  for where in [' WHERE id<=7',' WHERE id>21']:
   add('successful-update',f'UPDATE t SET valid={expr}'+where+' RETURNING id,valid;')
   add('successful-insert',f'INSERT INTO out SELECT id,{expr} FROM t'+where+';')
   add('successful-ctas',f'CREATE TABLE made AS SELECT id,{expr} AS valid FROM t'+where+';')
 add('successful-savepoint',"SAVEPOINT j; UPDATE t SET valid=json_array(v,'$[0]') WHERE id<=7; ROLLBACK TO j; RELEASE j; SELECT id,valid FROM t ORDER BY id;")
 add('successful-transaction',"BEGIN; UPDATE t SET valid=json_array(v,'$[0]') WHERE id<=7; COMMIT; SELECT id,hex(valid) FROM t ORDER BY id;")
 for _ in range(a.random_cases):
  expr=rng.choice(['v','CAST(v AS TEXT)','NULL',error_expr,'flags']);path=rng.choice(["'$'","'$.v'",'flags','NULL']);lo=rng.randrange(len(inputs)+1);hi=lo+rng.randrange(1,10)
  add('seeded-constructor-update',f'UPDATE t SET valid=json_array({expr},{path}) WHERE id BETWEEN {lo} AND {hi};')
 for name in ['json_array','jsonb_array','json_object','jsonb_object','json_quote','coalesce']:
  call=name+'('+','.join(['1']*1001)+')'
  for value in [call,'('+call+')','(('+call+'))','('+call+',2)','(2,'+call+')']:
   names='(valid,flags)' if value.endswith(',2)') or value.startswith('(2,') else 'valid'
   add('fixed-limit-diagnostic','UPDATE t SET '+names+'='+value+' WHERE 0;')
 for paths in ["'$.v[0]'","'$.v[#-1]'","'$.a','$.a'","'$[0]','$[0]'"]:
  for value in ["'{v:[1,2,3],a:1,a:2}'","'[1,2,[3,4]]'"]:
   add('fixed-constructor-update','UPDATE t SET valid=json_array('+value+','+paths+') WHERE id<=7 RETURNING id,hex(valid);')
 for expr in ["json_array()","jsonb_array(1)","json_object('a',1)","jsonb_object('a',NULL)","json_quote(NULL)"]:
  add('stored-subtype-update','UPDATE t SET valid='+expr+' WHERE id<=7 RETURNING id,subtype(valid),subtype('+expr+');')
  add('stored-subtype-insert','INSERT INTO out VALUES(999,'+expr+'); SELECT id,subtype(valid),hex(valid) FROM out;')
  add('stored-subtype-ctas','CREATE TABLE made AS SELECT 1 AS id,'+expr+' AS valid; SELECT subtype(valid),hex(valid) FROM made;')
 for expr in ["json_array()","jsonb_array(1)","json_object('a',1)","jsonb_object('a',NULL)","json_quote(NULL)"]:
  for insert_source in ['VALUES(998,'+expr+')','VALUES(998,'+expr+'),(999,'+expr+')','SELECT 998,'+expr]:
   add('insert-returning-subtype','INSERT INTO out '+insert_source+' RETURNING id,typeof(valid),subtype(valid),hex(valid); SELECT id,subtype(valid),hex(valid) FROM out ORDER BY id;')
 for affinity in ['', 'BLOB','TEXT','INT','REAL','NUMERIC']:
  for auto in ['', 'AUTOINCREMENT']:
   setup="CREATE TABLE made(id INTEGER PRIMARY KEY "+auto+",valid "+affinity+" NOT NULL ON CONFLICT REPLACE DEFAULT (json('{}')));"
   for mutation in ["INSERT INTO made DEFAULT VALUES", "INSERT INTO made(id) VALUES(1),(2)","INSERT INTO made VALUES(1,json('1'))","INSERT INTO made VALUES(1,NULL)"]:
    add('default-returning-subtype',setup+mutation+' RETURNING id,typeof(valid),subtype(valid),hex(valid);SELECT id,subtype(valid),hex(valid) FROM made ORDER BY id;')
 for _ in range(a.random_cases):
  affinity=rng.choice(['','BLOB','TEXT','INT','REAL','NUMERIC']);auto=rng.choice(['','AUTOINCREMENT']);policy=rng.choice(['',' OR ABORT',' OR IGNORE',' OR REPLACE']);value=rng.choice(["json('{}')","json('1')","json('1.5')","json(NULL)","CAST(json('{}') AS BLOB)","json_extract('{}','$')","jsonb('{}')","NULL"])
  setup="CREATE TABLE made(id INTEGER PRIMARY KEY "+auto+",valid "+affinity+" NOT NULL ON CONFLICT REPLACE DEFAULT (json('{}'))); INSERT INTO made VALUES(1,'{}');"
  mutation=rng.choice(['UPDATE'+policy+' made SET valid='+value+' WHERE id=1','INSERT'+policy+' INTO made VALUES(2,'+value+')','INSERT'+policy+' INTO made VALUES(2,'+value+'),(3,'+value+')','INSERT'+policy+' INTO made SELECT 2,'+value])
  add('seeded-returning-subtype',setup+mutation+' RETURNING id,typeof(valid),subtype(valid),hex(valid);SELECT id,subtype(valid),hex(valid) FROM made ORDER BY id;')
 observation='PRAGMA integrity_check;PRAGMA user_version;PRAGMA application_id;PRAGMA table_info(t);PRAGMA table_info(out);PRAGMA table_info(made);SELECT id,typeof(v),hex(v),typeof(flags),quote(flags),typeof(valid),hex(valid),quote(valid) FROM t ORDER BY id;SELECT id,typeof(valid),hex(valid),quote(valid) FROM out ORDER BY id;'
 read='SELECT id,typeof(v),hex(v),typeof(flags),quote(flags),typeof(valid),hex(valid),quote(valid) FROM t ORDER BY id;SELECT id,typeof(valid),hex(valid),quote(valid) FROM out ORDER BY id;'
 cases=[];fixtures=[]
 with tempfile.TemporaryDirectory(prefix='sqleanite-json-write-') as tmp:
  for fixture in range(a.fixtures):
   folder=Path(tmp)/str(fixture);folder.mkdir();base=folder/'base.db';page=512<<(fixture%8)
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v,flags,valid);CREATE TABLE out(id INTEGER PRIMARY KEY,valid);'
   for i,value in enumerate(inputs):
    flags=rng.choice(["'$'","'$.v'","'$.v[0]'","'$.a'","'$[0]'","'$[1]'","'$[#-1]'","'bad'",'NULL'])
    setup+=f'INSERT INTO t VALUES({i+1},{value},{flags},NULL);'
   created=csql(base,setup);assert created['code']==0,created
   fixtures.append(dict(fixture=fixture,page_size=page,setup=setup))
   for mode in ['--verified-file','--verified-wal-file']:
    for index,script in enumerate(scripts):
     case_dir=folder/(mode+str(index));case_dir.mkdir();left=case_dir/'lean.db';right=case_dir/'sqlite.db';shutil.copyfile(base,left);shutil.copyfile(base,right)
     bl,br=snapshot(left),snapshot(right)
     l=run([str(binary),mode,str(left)],script['sql']);c=csql(right,script['sql']);al,ar=snapshot(left),snapshot(right)
     lo,co=csql(left,observation),csql(right,observation)
     made=csql(right,"SELECT count(*) FROM sqlite_schema WHERE name='made';")['stdout']=='1\n'
     extra='SELECT id,typeof(valid),hex(valid),quote(valid) FROM made ORDER BY id;' if made else ''
     lr=run([str(binary),mode,str(left)],read+extra);cr=csql(right,read+extra)
     geometry=dict(lean=csql(left,'PRAGMA page_size;'),sqlite=csql(right,'PRAGMA page_size;'))
     follow="INSERT INTO t VALUES(100000,'{}',1,1);SELECT id,typeof(v),hex(v),typeof(valid),hex(valid),quote(valid) FROM t ORDER BY id;PRAGMA integrity_check;"
     lw,cw=csql(left,follow),csql(right,follow)
     matched=same(l,c) and lo['code']==co['code']==0 and lo['stdout']==co['stdout'] and lo['stdout'].startswith('ok\n') and same(lr,cr) and lw['code']==cw['code']==0 and lw['stdout']==cw['stdout'] and (ar!=br or al==bl)
     cases.append(dict(script,fixture=fixture,page_size=page,mode=mode,lean=l,sqlite=c,lean_error=error(l),sqlite_error=error(c),observation_lean=lo,observation_sqlite=co,reopen_lean=lr,reopen_sqlite=cr,subsequent_c_write_lean=lw,subsequent_c_write_sqlite=cw,geometry=geometry,lean_unchanged=al==bl,sqlite_unchanged=ar==br,matched=matched))
 assert source==digest() and exe==hashlib.sha256(binary.read_bytes()).hexdigest(),'Implementation changed during evaluation'
 failures=sum(not c['matched'] for c in cases)
 report=dict(seed=a.seed,random_cases=a.random_cases,generated_jsonb=generated,fixtures=fixtures,cases=cases,failures=failures,comparison=__doc__.strip(),implementation_sha256=source,executable_sha256=exe,harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([sqlite,'--version'],text=True).strip())
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=failures)));return bool(failures)
if __name__=='__main__':raise SystemExit(main())
