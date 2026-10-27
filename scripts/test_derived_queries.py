#!/usr/bin/env python3
"""Differential regressions for scoped CTE and FROM-query execution."""
import os
import re
from pathlib import Path
import random
import subprocess
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
SQLITE=os.environ.get('SQLITE3_BIN','sqlite3')
BINARY=ROOT/'.lake/build/bin/sqleanite'
QUERIES={
 'from_sum':'SELECT sum(n) FROM (SELECT n FROM t WHERE id>1);',
 'from_alias':'SELECT q.id,q.n FROM (SELECT id,n FROM t) AS q ORDER BY q.id;',
 'from_nested':'SELECT sum(n) FROM (SELECT n FROM (SELECT n FROM t WHERE id>1));',
 'from_two':'SELECT a.id,b.n FROM (SELECT id,n FROM t) a JOIN (SELECT id,n FROM t) b ON a.id=b.id ORDER BY a.id;',
 'from_empty':'SELECT count(*),sum(n) FROM (SELECT n FROM t WHERE 0);',
 'from_distinct':'SELECT n FROM (SELECT DISTINCT n FROM t) ORDER BY n;',
 'from_limit':'SELECT * FROM (SELECT id FROM t ORDER BY id DESC LIMIT 2) ORDER BY id;',
 'from_values':'SELECT column1,column2 FROM (VALUES(1,2),(3,4)) ORDER BY column1;',
 'from_type':'SELECT typeof(x),x FROM (SELECT 1 AS x UNION ALL SELECT \'02\');',
 'from_null':'SELECT typeof(x),x FROM (SELECT NULL AS x UNION ALL SELECT 2);',
 'from_duplicate_names':'SELECT id,\"id:1\" FROM (SELECT id,id FROM t) ORDER BY id;',
 'from_blob':'SELECT typeof(x),hex(x) FROM (SELECT X\'00FF\' AS x);',
 'from_compound':'SELECT id FROM (SELECT id FROM t WHERE id=1) UNION ALL SELECT id FROM (SELECT id FROM t WHERE id=3);',
 'cte_sum':'WITH c AS (SELECT n FROM t) SELECT sum(n) FROM c;',
 'cte_alias':'WITH c(x) AS (SELECT n FROM t) SELECT x FROM c ORDER BY x;',
 'cte_star_alias':'WITH c(a,b,c) AS (SELECT * FROM t) SELECT a,c FROM c ORDER BY a;',
 'cte_values':'WITH c(x,y) AS (VALUES(1,2),(3,4)) SELECT sum(x+y) FROM c;',
 'cte_shadow':'WITH t AS (SELECT 42 AS id) SELECT id FROM t;',
 'cte_main_shadow':'WITH t AS (SELECT 42 AS id) SELECT id FROM main.t ORDER BY id;',
 'cte_self_join':'WITH c AS (SELECT id,n FROM t) SELECT a.id,b.n FROM c a JOIN c b ON a.id=b.id ORDER BY a.id;',
 'cte_derived_body':'WITH c AS (SELECT n FROM t) SELECT sum(n) FROM (SELECT n FROM c);',
 'cte_derived_source':'WITH c AS (SELECT n FROM (SELECT n FROM t)) SELECT sum(n) FROM c;',
 'cte_materialized':'WITH c AS MATERIALIZED (SELECT n FROM t) SELECT sum(n) FROM c;',
 'cte_not_materialized':'WITH c AS NOT MATERIALIZED (SELECT n FROM t) SELECT sum(n) FROM c;',
 'cte_counters':'WITH c AS (SELECT changes() AS n) SELECT n,total_changes() FROM c;',
 'from_counters':'SELECT * FROM (SELECT changes(),total_changes());',
 'scope_lifetime':'WITH c AS (SELECT n FROM t) SELECT sum(n) FROM c;SELECT * FROM c;',
 'from_rowid':'SELECT rowid FROM (SELECT id FROM t);',
}
QUERIES.update({
 'qualified_dotted_collision': 'CREATE TABLE "main.t"(id INTEGER);INSERT INTO "main.t" VALUES(999);SELECT id FROM main.t ORDER BY id;SELECT id FROM "main.t";',

 'unused_cte': 'WITH c AS (SELECT abs(-9223372036854775808)) SELECT 17;',
 'unused_recursive': 'WITH RECURSIVE c(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM c) SELECT 17;',

 'recursive_sum': 'WITH RECURSIVE c(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM c WHERE x<8) SELECT sum(x) FROM c;',
 'recursive_queue': 'WITH RECURSIVE c(x) AS (VALUES(1),(10) UNION ALL SELECT x+1 FROM c WHERE x<3) SELECT x FROM c;',
 'recursive_duplicate_seeds': 'WITH RECURSIVE c(x) AS (VALUES(1),(1) UNION SELECT x+1 FROM c WHERE x<4) SELECT x FROM c;',
 'recursive_cycle': 'WITH RECURSIVE c(x) AS (VALUES(1) UNION SELECT 1 FROM c) SELECT x FROM c;',
 'recursive_null_cycle': 'WITH RECURSIVE c(x) AS (VALUES(NULL) UNION SELECT NULL FROM c) SELECT typeof(x),x FROM c;',
 'recursive_without_keyword': 'WITH c(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM c WHERE x<5) SELECT sum(x) FROM c;',
 'recursive_multiple_columns': 'WITH RECURSIVE c(x,y) AS (VALUES(1,2) UNION ALL SELECT x+1,y*2 FROM c WHERE x<6) SELECT * FROM c ORDER BY x;',
 'recursive_table_seed': 'WITH RECURSIVE c(x) AS (SELECT id FROM t WHERE id=1 UNION ALL SELECT x+1 FROM c WHERE x<5) SELECT sum(x) FROM c;',
 'recursive_empty': 'WITH RECURSIVE c(x) AS (SELECT id FROM t WHERE 0 UNION ALL SELECT x+1 FROM c WHERE x<5) SELECT count(*) FROM c;',
 'rowid_mixed_join': 'SELECT rowid FROM (SELECT id FROM t) d JOIN t ON d.id=t.id ORDER BY t.id;',
 'rowid_declared': 'SELECT rowid FROM (SELECT id AS rowid FROM t) ORDER BY rowid;',
 'rowid_alias_order': 'SELECT id+1 AS rowid FROM (SELECT id FROM t) ORDER BY rowid;',
 'quoted_period': 'WITH "main.t" AS (SELECT 42 AS id) SELECT id FROM "main.t";',
})
rng = random.Random(int(os.environ.get('SQLEANITE_DERIVED_SEED','356501')))
for i in range(10):
 bound=rng.randrange(2,45)
 step=rng.randrange(1,5)
 QUERIES['generated_recursive_'+str(i)]=f'WITH RECURSIVE c(x) AS (VALUES({step}) UNION ALL SELECT x+{step} FROM c WHERE x<{bound}) SELECT count(*),sum(x),max(x) FROM c;'
 cutoff=rng.randrange(-1000,1000)
 QUERIES['generated_nested_'+str(i)]=f'WITH c AS (SELECT n FROM (SELECT n FROM t WHERE n>{cutoff})) SELECT count(*),sum(n) FROM (SELECT n FROM c);'
class DerivedQueries(unittest.TestCase):pass

def case(sql,mode):
 def test(self):
  rng=random.Random(int(os.environ.get('SQLEANITE_DERIVED_SEED','356501')))
  setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);'+''.join(f"INSERT INTO t VALUES({i},'value {rng.randrange(1000)}',{rng.randrange(-1000,1000)});" for i in range(1,4))
  with tempfile.TemporaryDirectory(prefix='sqleanite-derived-') as directory:
   left=Path(directory)/'lean.db';right=Path(directory)/'sqlite.db'
   for path in [left,right]:subprocess.run([SQLITE,str(path)],input=setup,text=True,check=True,capture_output=True)
   lean=subprocess.run([str(BINARY),mode,str(left)],input=sql,text=True,capture_output=True,timeout=30)
   ref=subprocess.run([SQLITE,'-batch','-bail',str(right)],input=sql,text=True,capture_output=True,timeout=30)
   self.assertEqual(lean.returncode,ref.returncode,lean.stderr+' / '+ref.stderr)
   self.assertEqual(lean.stdout,ref.stdout,lean.stderr)
   if ref.returncode:
    def error(result):
     line=result.stderr.splitlines()[0] if result.stderr else ''
     return re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?', '',line)
    self.assertEqual(error(lean),error(ref))
   observation='PRAGMA integrity_check;SELECT type,name,tbl_name,sql FROM sqlite_schema ORDER BY name;SELECT * FROM t ORDER BY id;'
   self.assertEqual(subprocess.check_output([SQLITE,str(left),observation]),subprocess.check_output([SQLITE,str(right),observation]))
 return test
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(DerivedQueries,'test_'+name+'_'+suffix,case(sql,mode))
if __name__=='__main__':unittest.main()
