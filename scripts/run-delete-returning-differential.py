#!/usr/bin/env python3
"""DELETE RETURNING public-file differential against pinned SQLite.

Compare successful output bytes, positive errors, and independently observed
stored rows, storage classes, and integrity after every script. Failed single
statements must retain main/WAL bytes. Large successful captures are stored
as byte counts, SHA-256 and previews after full-byte comparison. Failures keep
full captures. This is not full SQLite equivalence.
"""
import argparse,hashlib,json,os,random,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--sqlite',default=os.environ.get('SQLITE3_BIN','sqlite3'));p.add_argument('--seed',type=int,default=353990);p.add_argument('--random-cases',type=int,default=0);p.add_argument('--fixtures',type=int,default=1);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(a.seed);cases=[];binary=str(ROOT/'.lake/build/bin/sqleanite')
 def run(args,sql):
  r=subprocess.run(args,input=sql.encode(),capture_output=True,timeout=120);return dict(code=r.returncode,stdout=r.stdout.decode('latin1'),stderr=r.stderr.decode('latin1'))
 def hashes(path):return {s:hashlib.sha256(Path(str(path)+s).read_bytes()).hexdigest() for s in ['','-wal'] if Path(str(path)+s).exists()}
 queries=['DELETE FROM t RETURNING *;','DELETE FROM t WHERE id=0 RETURNING id,v,w;',
  'DELETE FROM t WHERE id<0 RETURNING rowid,typeof(v),hex(v),typeof(w),hex(w);',
  'DELETE FROM t WHERE id IN (-4,0,3) RETURNING *,id+1 AS next;',
  'DELETE FROM t WHERE 0 RETURNING abs(-9223372036854775808);',
  'DELETE FROM t WHERE 0 RETURNING missing;',
  'DELETE FROM t WHERE 0 RETURNING no_function();',
  'DELETE FROM t RETURNING count(*);','DELETE FROM t RETURNING 0 AND count(*);',
  'DELETE FROM t RETURNING max(id);','DELETE FROM t RETURNING max(id,2);',
  'DELETE FROM t RETURNING t.*;','DELETE FROM t AS x RETURNING x.id;',
  'DELETE FROM t AS x WHERE x.id<0 RETURNING t.id;',
  'DELETE FROM t AS x WHERE t.id<0 RETURNING id;',
  'DELETE FROM t RETURNING id AS n,n;',
  'DELETE FROM t RETURNING id AS v,v;',
  'DELETE FROM t WHERE id<0 RETURNING CASE WHEN id=-1 THEN abs(-9223372036854775808) ELSE id END;',
  'DELETE FROM t WHERE id<0 RETURNING CAST(X\'80FF\' AS TEXT),hex(CAST(X\'610062\' AS TEXT));',
  'DELETE FROM t WHERE abs(-9223372036854775808)>0 RETURNING id;',
  'DELETE FROM t WHERE id=id AND abs(-9223372036854775808)>0 RETURNING id;',
  'DELETE FROM t RETURNING id+100,id COLLATE nocase,printf(\'%04d\',id);',
  'DELETE FROM empty RETURNING *;',
  'DELETE FROM empty RETURNING abs(-9223372036854775808);',
  'DELETE FROM empty WHERE abs(-9223372036854775808)>0 RETURNING id;',
  'DELETE FROM empty RETURNING missing;',
  'BEGIN;\nDELETE FROM t WHERE id<0 RETURNING id,v;\nROLLBACK;',
  'BEGIN;\nDELETE FROM t WHERE id<0 RETURNING id,v;\nCOMMIT;',
  'BEGIN;\nINSERT INTO t(id,v) VALUES(999,7);\nDELETE FROM t RETURNING abs(-9223372036854775808);\nCOMMIT;',
  'DELETE FROM t WHERE id=0 RETURNING id;\nDELETE FROM t WHERE id=0 RETURNING id;',
  'DELETE FROM t RETURNING sum(id) FILTER (WHERE 0);',
  'DELETE FROM t RETURNING 0 AND no_function();',
  'DELETE FROM t RETURNING 0 AND missing;']
 queries += ["DELETE FROM implicit RETURNING *,rowid,oid,_rowid_;",
  "DELETE FROM keyed WHERE k<'k2' RETURNING *,rowid;",
  "DELETE FROM shadow WHERE rowid>0 RETURNING *,rowid,_rowid_;",
  "DELETE FROM t RETURNING \"v\",t.\"id\";",
  "DELETE FROM t RETURNING 0 AND abs();",
  "DELETE FROM t RETURNING 0 AND likely(id);",
  "DELETE FROM t RETURNING id AS \"quoted alias\";"]
 expressions=['id','v','w','*','typeof(v)','hex(v)','quote(v)','id+1','printf(\'%g\',w)','coalesce(v,id)','CASE WHEN id%2=0 THEN v ELSE w END','CAST(v AS INTEGER)','min(id,2)','id COLLATE nocase','hex(CAST(X\'80FF\' AS TEXT))']
 predicates=['1','0','id<0','id>=0','id IN (-5,-2,1,4)','id%2=0','v IS NULL','typeof(v)=\'blob\'','length(v)>1','w+1>0','id=-4 AND id IN (-4,id,abs(-9223372034775808))']
 for _ in range(a.random_cases):
  projection=','.join(rng.choice(expressions) for _ in range(rng.randrange(1,6)))
  queries.append('DELETE FROM t WHERE '+rng.choice(predicates)+' RETURNING '+projection+';')
 with tempfile.TemporaryDirectory(prefix='sqleanite-delete-returning-') as tmp:
  for fixture in range(a.fixtures):
   page=[512,4096,65536][fixture%3];base=Path(tmp)/f'base{fixture}.db'
   values=['NULL','0','-7','1.25',"'a'","'A'","'a'||char(0)||'b'","X'00FF'","CAST(X'80FF' AS TEXT)","'12x'"]
   if fixture:values += ["'"+('x'*(5000+fixture))+"'", "zeroblob(6000)"]
   rows=[f'({i},{rng.choice(values)},{rng.choice(values)})' for i in range(-5,7+fixture*12)]
   setup=f'PRAGMA page_size={page};CREATE TABLE t(id INTEGER PRIMARY KEY,v,w REAL);CREATE INDEX tv ON t(v);CREATE TABLE empty(id INTEGER PRIMARY KEY,v,w REAL);INSERT INTO t VALUES'+','.join(rows)+';';setup += "CREATE TABLE implicit(v,w);INSERT INTO implicit VALUES('a',7),(X'80FF',NULL);CREATE TABLE keyed(k TEXT PRIMARY KEY NOT NULL,v,w);INSERT INTO keyed VALUES('k1',1,2),('k2',3,4);CREATE TABLE shadow(rowid,v,w);INSERT INTO shadow VALUES(-1,5,6),(2,7,8);"
   r=run([a.sqlite,'-batch','-bail',str(base)],setup);assert r['code']==0,r
   for mode in ['--verified-file','--verified-wal-file']:
    for sql in queries:
     folder=Path(tmp)/str(len(cases));folder.mkdir();lean=folder/'lean.db';ref=folder/'sqlite.db';shutil.copyfile(base,lean);shutil.copyfile(base,ref);before=hashes(lean)
     l=run([binary,mode,str(lean)],sql);r=run([a.sqlite,'-batch','-bail',str(ref)],sql)
     same=(l['code']!=0 and r['code']!=0) or (l['code']==r['code']==0 and l['stdout']==r['stdout']);item=dict(fixture=fixture,page_size=page,mode=mode,sql=sql,lean=l,sqlite=r,matched=same)
     observation='PRAGMA integrity_check;SELECT id,typeof(v),hex(v),typeof(w),hex(w) FROM t ORDER BY id;SELECT id,typeof(v),hex(v),typeof(w),hex(w) FROM empty ORDER BY id;SELECT rowid,typeof(v),hex(v),typeof(w),hex(w) FROM implicit ORDER BY rowid;SELECT rowid,k,typeof(v),hex(v),typeof(w),hex(w) FROM keyed ORDER BY rowid;SELECT _rowid_,rowid,typeof(v),hex(v),typeof(w),hex(w) FROM shadow ORDER BY _rowid_;';lo=run([a.sqlite,'-batch','-bail',str(lean)],observation);ro=run([a.sqlite,'-batch','-bail',str(ref)],observation);item.update(observed_lean=lo,observed_sqlite=ro);item['matched'] &= lo['code']==ro['code']==0 and lo['stdout']==ro['stdout'] and lo['stdout'].startswith('ok\n')
     if r['code'] and '\n' not in sql:item['failed_statement_bytes_unchanged']=before==hashes(lean);item['matched'] &= item['failed_statement_bytes_unchanged']
     if item['matched']:
      for key in ['lean','sqlite','observed_lean','observed_sqlite']:
       value=item[key];raw=value['stdout'].encode('latin1')
       if len(raw)>4096:
        value.update(stdout_bytes=len(raw),stdout_sha256=hashlib.sha256(raw).hexdigest(),stdout_prefix=raw[:128].decode('latin1'),stdout_suffix=raw[-128:].decode('latin1'));del value['stdout']
     cases.append(item)
 d=hashlib.sha256()
 for path in sorted((ROOT/'SQLeanite').rglob('*.lean'))+[ROOT/'Main.lean']:d.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes())
 report=dict(seed=a.seed,fixtures=a.fixtures,random_cases=a.random_cases,cases=cases,failures=sum(not c['matched'] for c in cases),implementation_sha256=d.hexdigest(),executable_sha256=hashlib.sha256(Path(binary).read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),sqlite_version=subprocess.check_output([a.sqlite,'--version'],text=True).strip(),comparison=__doc__.strip());a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(cases=len(cases),failures=report['failures'])));return bool(report['failures'])
if __name__=='__main__':raise SystemExit(main())
