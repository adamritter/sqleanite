#!/usr/bin/env python3
"""Catalog index admission and physical content checks against pinned SQLite.

SQL comparisons use complete successful output bytes and positive errors.
Damaged-index probes are separately labelled defensive integrity checks: SQLite
must diagnose corruption and Lean must reject admission; this is not an exact
SQLite error-timing claim. Every read must preserve main/WAL bytes. Valid
imports then undergo a Lean UPDATE, C integrity/data observation and C INSERT
followed by Lean reopen, independently for each public file mode.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354150);p.add_argument('--fixtures',type=int,default=12);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([a.sqlite,'-batch','-bail',str(path)],sql)
 def literal(value):return "'"+value.replace("'","''")+"'"
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 query='SELECT id,typeof(v),hex(v) FROM t ORDER BY id;'
 with tempfile.TemporaryDirectory(prefix='sqleanite-index-schema-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][(fixture//4)%3];typ=['TEXT','REAL','NUMERIC','BLOB'][fixture%4];base=Path(tmp)/f'base{fixture}.db';alpha='alpha-'+format(rng.getrandbits(48),'012x')
   setup=f"PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v {typ});INSERT INTO t VALUES(1,1),(2,1.5),(3,-0.0),(4,'3.0'),(5,X'80FF00'),(6,NULL),(7,'{alpha}');CREATE INDEX Ix ON t(v);"
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   variants=[('plain','CREATE INDEX Ix ON t(v)',False,None),('quoted','CREATE INDEX "Ix" ON "t"("v")',False,None),('comments','CREATE INDEX Ix /*owner*/ ON t( /*column*/ v)',False,None),('ascending','CREATE INDEX Ix ON t(v ASC)',False,None),('key_ascending','CREATE INDEX Ix ON t(v)',False,f'CREATE TABLE t(id INTEGER PRIMARY KEY ASC,v {typ})'),('tail_delete','CREATE INDEX Ix ON t(v);DELETE FROM t WHERE id=1;',False,None),('tail_invalid','CREATE INDEX Ix ON t(v);broken "unterminated',False,None),('wrong_update',"UPDATE t SET v='changed' WHERE id=1;",False,None),('wrong_delete','DELETE FROM t;',False,None),('wrong_drop','DROP TABLE t;',False,None),('wrong_name','CREATE INDEX Other ON t(v)',False,None),('wrong_owner','CREATE INDEX Ix ON missing(v)',False,None),('wrong_kind','CREATE TABLE Ix(x)',False,None),('wrong_column','CREATE INDEX Ix ON t(missing)',False,None),('leading_space',' CREATE INDEX Ix ON t(v)',False,None),('leading_comment','/*prefix*/CREATE INDEX Ix ON t(v)',False,None),('damaged_plain','CREATE INDEX Ix ON t(v)',True,None),('damaged_quoted','CREATE INDEX "Ix" ON "t"("v")',True,None)]
   for _ in range(a.random_cases):
    column='V' if rng.getrandbits(1) else 'v';table='T' if rng.getrandbits(1) else 't';name='IX' if rng.getrandbits(1) else 'Ix';tail=rng.choice(['',';DELETE FROM t;',';broken "'])
    sql=f'CREATE INDEX {name} /*{rng.getrandbits(32):08x}*/ ON {table}({column}'+rng.choice(['',' ASC'])+')'+tail
    variants.append(('fresh_source',sql,False,None))
   for label,index_sql,damaged,table_sql in variants:
    path=Path(tmp)/f'input{fixture}-{len(cases)}.db';shutil.copyfile(base,path)
    rewrite='.dbconfig defensive off\nPRAGMA writable_schema=ON;UPDATE sqlite_schema SET sql='+literal(index_sql)+" WHERE name='Ix';"
    if table_sql:rewrite+='UPDATE sqlite_schema SET sql='+literal(table_sql)+" WHERE name='t';"
    rewrite+='PRAGMA writable_schema=OFF;';rewritten=csql(path,rewrite);assert rewritten['code']==0,rewritten
    if damaged:
     root=int(csql(base,"SELECT rootpage FROM sqlite_schema WHERE name='Ix';")['stdout']);data=bytearray(path.read_bytes());start=(root-1)*page;leaf=data[start:start+page];assert leaf[0]==10
     offset=leaf.find(alpha.encode());assert offset>=0;data[start+offset]=ord('z');path.write_bytes(data)
    ref=Path(tmp)/f'ref{fixture}-{len(cases)}.db';shutil.copyfile(path,ref);r=csql(ref,query);integrity=csql(ref,'PRAGMA integrity_check;')
    for mode in ['--verified-file','--verified-wal-file']:
     lean=Path(tmp)/f'lean{len(cases)}.db';shutil.copyfile(path,lean);before=hashes(lean);l=run([binary,mode,str(lean)],query);unchanged=before==hashes(lean)
     family='defensive_integrity' if damaged else 'sql_comparison'
     matched=((integrity['code']!=0 or integrity['stdout']!='ok\n') and l['code']!=0) if damaged else ((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']))
     item=dict(fixture=fixture,page_size=page,declared_type=typ,label=label,family=family,mode=mode,index_sql=index_sql,table_sql=table_sql,sql=query,lean=l,sqlite=r,sqlite_integrity=integrity,read_bytes_unchanged=unchanged,matched=matched and unchanged)
     if family=='sql_comparison' and r['code']==0:
      refwrite=Path(tmp)/f'write-ref{len(cases)}.db';shutil.copyfile(ref,refwrite)
      update="UPDATE t SET v='99' WHERE id=1;\n"+query
      lw=run([binary,mode,str(lean)],update);rw=csql(refwrite,update)
      lo=csql(lean,'PRAGMA integrity_check;'+query);ro=csql(refwrite,'PRAGMA integrity_check;'+query)
      follow="INSERT INTO t VALUES(17,CAST(X'80FF00' AS TEXT));"
      lf=csql(lean,follow);rf=csql(refwrite,follow)
      lr=run([binary,mode,str(lean)],query);rr=csql(refwrite,query)
      item.update(write_sql=update,lean_write=lw,sqlite_write=rw,observed_lean=lo,observed_sqlite=ro,c_followup_sql=follow,c_followup_lean=lf,c_followup_sqlite=rf,reopened_lean=lr,reopened_sqlite=rr)
      item['matched'] &= lw['code']==rw['code']==0 and lw['stdout']==rw['stdout'] and lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n') and lf['code']==rf['code']==0 and lr['code']==rr['code']==0 and lr['stdout']==rr['stdout']
     cases.append(item)
   # Empty SQL on an automatic primary index has the same catalog meaning as NULL.
   implicit=Path(tmp)/f'implicit{fixture}.db'
   prepared=csql(implicit,f".dbconfig defensive off\nPRAGMA page_size={page};CREATE TABLE t(id INTEGER,v TEXT PRIMARY KEY);INSERT INTO t VALUES(1,'{alpha}'),(2,NULL);PRAGMA writable_schema=ON;UPDATE sqlite_schema SET sql='' WHERE type='index';PRAGMA writable_schema=OFF;");assert prepared['code']==0,prepared
   r=csql(implicit,query);integrity=csql(implicit,'PRAGMA integrity_check;')
   for mode in ['--verified-file','--verified-wal-file']:
    lean=Path(tmp)/f'lean{len(cases)}.db';shutil.copyfile(implicit,lean);before=hashes(lean);l=run([binary,mode,str(lean)],query);unchanged=before==hashes(lean)
    matched=l['code']==r['code']==0 and l['stdout']==r['stdout'] and integrity['code']==0 and integrity['stdout']=='ok\n' and unchanged
    cases.append(dict(fixture=fixture,page_size=page,declared_type='TEXT PRIMARY KEY',label='implicit_empty_sql',family='sql_comparison',mode=mode,index_sql='',sql=query,lean=l,sqlite=r,sqlite_integrity=integrity,read_bytes_unchanged=unchanged,matched=matched))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 families={name:dict(cases=sum(c['family']==name for c in cases),failures=sum(c['family']==name and not c['matched'] for c in cases)) for name in ['sql_comparison','defensive_integrity']}
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,families=families,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'],families=families)));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
