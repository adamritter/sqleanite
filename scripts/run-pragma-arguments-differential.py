#!/usr/bin/env python3
"""PRAGMA lexical arguments and explicit schema binding against pinned SQLite.

Compare full successful result bytes or positive error status, without sorting
or normalizing names. Every read must preserve main/WAL bytes. Keyword fixtures
come from the pinned upstream keyword table, not result-dependent filtering.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
KEYWORDS=['ABORT', 'ACTION', 'ADD', 'AFTER', 'ALL', 'ALTER', 'ALWAYS', 'ANALYZE', 'AND', 'AS', 'ASC', 'ATTACH', 'AUTOINCREMENT', 'BEFORE', 'BEGIN', 'BETWEEN', 'BY', 'CASCADE', 'CASE', 'CAST', 'CHECK', 'COLLATE', 'COLUMN', 'COMMIT', 'CONFLICT', 'CONSTRAINT', 'CREATE', 'CROSS', 'CURRENT', 'CURRENT_DATE', 'CURRENT_TIME', 'CURRENT_TIMESTAMP', 'DATABASE', 'DEFAULT', 'DEFERRED', 'DEFERRABLE', 'DELETE', 'DESC', 'DETACH', 'DISTINCT', 'DO', 'DROP', 'END', 'EACH', 'ELSE', 'ESCAPE', 'EXCEPT', 'EXCLUSIVE', 'EXCLUDE', 'EXISTS', 'EXPLAIN', 'FAIL', 'FILTER', 'FIRST', 'FOLLOWING', 'FOR', 'FOREIGN', 'FROM', 'FULL', 'GENERATED', 'GLOB', 'GROUP', 'GROUPS', 'HAVING', 'IF', 'IGNORE', 'IMMEDIATE', 'IN', 'INDEX', 'INDEXED', 'INITIALLY', 'INNER', 'INSERT', 'INSTEAD', 'INTERSECT', 'INTO', 'IS', 'ISNULL', 'JOIN', 'KEY', 'LAST', 'LEFT', 'LIKE', 'LIMIT', 'MATCH', 'MATERIALIZED', 'NATURAL', 'NO', 'NOT', 'NOTHING', 'NOTNULL', 'NULL', 'NULLS', 'OF', 'OFFSET', 'ON', 'OR', 'ORDER', 'OTHERS', 'OUTER', 'OVER', 'PARTITION', 'PLAN', 'PRAGMA', 'PRECEDING', 'PRIMARY', 'QUERY', 'RAISE', 'RANGE', 'RECURSIVE', 'REFERENCES', 'REGEXP', 'REINDEX', 'RELEASE', 'RENAME', 'REPLACE', 'RESTRICT', 'RETURNING', 'RIGHT', 'ROLLBACK', 'ROW', 'ROWS', 'SAVEPOINT', 'SELECT', 'SET', 'TABLE', 'TEMP', 'TEMPORARY', 'THEN', 'TIES', 'TO', 'TRANSACTION', 'TRIGGER', 'UNBOUNDED', 'UNION', 'UNIQUE', 'UPDATE', 'USING', 'VACUUM', 'VALUES', 'VIEW', 'VIRTUAL', 'WHEN', 'WHERE', 'WINDOW', 'WITH', 'WITHIN', 'WITHOUT']

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=354170);p.add_argument('--fixtures',type=int,default=3);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def csql(path,sql):return run([a.sqlite,'-batch','-bail',str(path)],sql)
 def ident(s):return '"'+s.replace('"','""')+'"'
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 numbers=['0','1','01','-1','+1','-0','+0','1.0','1e0','1E+0','.5','0x10','0Xf','-0x10','+0x10','9223372036854775808','-9223372036854775808','-9223372036854775809','1_0','1.0_0']
 queries=['PRAGMA table_info('+value+');' for value in numbers+KEYWORDS]
 names=['Users','sqlite_schema','sqlite_master','sqlite_temp_schema','sqlite_temp_master','Odd.Name','missing']
 for schema in ['main','MAIN','temp','missing','main.part','']:
  for name in names:queries.append('PRAGMA '+ident(schema)+'.table_xinfo('+ident(name)+');')
 for schema in ['main','temp','missing']:
  for pragma in ['index_list','index_info','index_xinfo']:
   for name in ['Users','Ix1','missing']:queries.append('PRAGMA '+schema+'.'+pragma+'('+ident(name)+');')
 queries+=['PRAGMA "main"."table_info"(Users);','PRAGMA "main.table_info"(Users);','PRAGMA unknown_custom(Users);','PRAGMA main.unknown_custom=1;','PRAGMA missing.unknown_custom;','PRAGMA main.table_info;']
 queries += ['PRAGMA table_info('+expr+');' for expr in ["('Users')",'Users+1','+Users','--1\n1','- -1','+ +1','NULL',"X'31'",'Users COLLATE binary',"CAST('Users' AS TEXT)"]]
 generated_names=[]
 for random_index in range(a.random_cases):
  value=rng.randrange(1000000);spell=rng.choice([str(value),'0'+str(value),hex(value),str(value)+'.0',str(value)+'e0']);sign=rng.choice(['','+','-']);schema=rng.choice(['','main.','"MAIN".','temp.']);queries.append('PRAGMA '+schema+'table_info('+sign+spell+');')
  if random_index<10:generated_names.append(('-' if sign=='-' else '')+spell)
 with tempfile.TemporaryDirectory(prefix='sqleanite-pragma-arguments-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3];base=Path(tmp)/f'base{fixture}.db'
   object_names=list(dict.fromkeys(['Users','Odd.Name','CAST','current_date','true','false','ON','DEFAULT','DELETE','FILTER','OVER','WINDOW','BEGIN']+[n.lstrip('+') for n in numbers]+generated_names+['payload-'+str(rng.getrandbits(48))]))
   setup=f'PRAGMA page_size={page};'+''.join('CREATE TABLE '+ident(name)+'('+ident('column-'+name)+' TEXT);' for name in object_names)+'CREATE INDEX "Ix1" ON Users("column-Users");'
   prepared=csql(base,setup);assert prepared['code']==0,prepared
   for mode in ['--verified-file','--verified-wal-file']:
    path=Path(tmp)/f'{fixture}-{mode}.db';shutil.copyfile(base,path);before=hashes(path)
    for sql in queries:
     l=run([binary,mode,str(path)],sql);r=csql(base,sql);unchanged=before==hashes(path)
     matched=((l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout'])) and unchanged
     cases.append(dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,read_bytes_unchanged=unchanged,matched=matched))
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),sqlite_pragma_names=subprocess.check_output([a.sqlite,':memory:','PRAGMA pragma_list;'],text=True).splitlines(),sqlite_compile_options=subprocess.check_output([a.sqlite,':memory:','PRAGMA compile_options;'],text=True).splitlines(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
