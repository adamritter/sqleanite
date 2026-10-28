#!/usr/bin/env python3
"""Further UTF-16 compatibility regressions beyond the first read checkpoint.
Known failures remain ordinary failures, with no skips or output corrections.
"""
import os,random,shutil,subprocess,tempfile,unittest
from pathlib import Path
from test_check_add_column import case,statement_lines,SQLITE,BINARY
class UTF16Edges(unittest.TestCase):pass
DATA="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);INSERT INTO t VALUES(1,'a'),(2,'Ā'),(3,'😀'),(4,'\ue000');"
READS={
 'ordinal_sort':'SELECT id,v FROM t ORDER BY 2,id;',
 'distinct_sort':'SELECT DISTINCT v FROM t ORDER BY v;',
 'grouped_sort':'SELECT v,count(*) FROM t GROUP BY v ORDER BY v;',
 'compound_union':"SELECT v FROM t UNION SELECT 'z' ORDER BY v;",
 'compound_intersect':'SELECT v FROM t INTERSECT SELECT v FROM t ORDER BY v;',
 'join_sort':'SELECT a.id,a.v FROM t a JOIN t b ON a.id=b.id ORDER BY a.v,a.id;',
 'window_order':'SELECT id,row_number() OVER(ORDER BY v) FROM t ORDER BY id;',
 'scalar_extremes':"SELECT min('a','Ā'),max('a','Ā'),nullif('a','Ā');",
 'aggregate_extremes':'SELECT min(v),max(v),hex(min(v)),hex(max(v)) FROM t;',
}
for enc in ['UTF-16le','UTF-16be']:
 setup=f"PRAGMA encoding='{enc}';"+DATA
 for name,sql in READS.items():
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(UTF16Edges,'test_'+enc.replace('-','_')+'_'+name+'_'+suffix,case(sql,mode,setup))

# Independent seeded data for final-checkpoint examples. All fresh queries
# execute through the same public modes and ordinary pinned-reference observer.
rng=random.Random(int(os.environ.get('SQLEANITE_UTF16_EDGE_SEED','905701')))
for enc in ['UTF-16le','UTF-16be']:
 values=rng.sample(['é','Ω','你','𐐀','😀','','Ā','z','a','ß','𝄞','Ж'],6)
 setup=f"PRAGMA encoding='{enc}';CREATE TABLE fresh(id INTEGER PRIMARY KEY,v TEXT);"
 setup+='INSERT INTO fresh VALUES'+','.join(f"({i+1},'{v}')" for i,v in enumerate(values))+';'
 queries={
  'fresh_except':f"SELECT v FROM fresh EXCEPT SELECT '{values[2]}' ORDER BY 1;",
  'fresh_compound_expression':"SELECT substr(v,1) AS x FROM fresh UNION ALL SELECT 'Q' ORDER BY x;",
  'fresh_window_filter':"SELECT id,sum(id) FILTER(WHERE id>1) OVER(PARTITION BY id%2 ORDER BY v ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW) FROM fresh ORDER BY id;",
  'fresh_partition_order':"SELECT id,row_number() OVER(PARTITION BY id%2 ORDER BY v DESC) FROM fresh ORDER BY id;",
 }
 for name,sql in queries.items():
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(UTF16Edges,'test_'+enc.replace('-','_')+'_'+name+'_'+suffix,case(sql,mode,setup))

def raw_read_case(encoding,payload,mode):
 def test(self):
  with tempfile.TemporaryDirectory(prefix='sqleanite-utf16-raw-') as folder:
   base=Path(folder)/'base.db';left=Path(folder)/'lean.db';right=Path(folder)/'sqlite.db'
   setup=f"PRAGMA encoding='{encoding}';CREATE TABLE t(v TEXT);INSERT INTO t VALUES(CAST(X'{payload}' AS TEXT));"
   subprocess.run([SQLITE,str(base)],input=setup.encode(),capture_output=True,check=True)
   shutil.copyfile(base,left);shutil.copyfile(base,right);before=left.read_bytes()
   sql='SELECT hex(v),length(v),unicode(v),octet_length(v) FROM t;'
   lean=subprocess.run([str(BINARY),mode,str(left)],input=statement_lines(sql).encode(),capture_output=True,timeout=30)
   ref=subprocess.run([SQLITE,'-batch','-bail',str(right)],input=statement_lines(sql).encode(),capture_output=True,timeout=30)
   self.assertEqual(ref.returncode,0,ref.stderr)
   self.assertEqual(lean.returncode,ref.returncode,lean.stderr)
   self.assertEqual(lean.stdout,ref.stdout)
   self.assertEqual(left.read_bytes(),before,'read changed actual database bytes')
   self.assertEqual(subprocess.check_output([SQLITE,str(left),'PRAGMA integrity_check;']),b'ok\n')
 return test
for enc,payloads in [('UTF-16le',['00D84100','00D8','FEFF']),('UTF-16be',['D8000041','D800','FFFE'])]:
 for i,payload in enumerate(payloads):
  for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
   setattr(UTF16Edges,f'test_{enc.replace("-","_")}_raw_{i}_{suffix}',raw_read_case(enc,payload,mode))
if __name__=='__main__':unittest.main()
