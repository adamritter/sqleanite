#!/usr/bin/env python3
"""Scalar-subquery regression cases, including lazy branches and correlation."""
import os,random,unittest
from test_pragma_tables import case
SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'a',3),(2,'b',7),(3,'c',2);"
QUERIES={
 'collation':"SELECT (SELECT v COLLATE NOCASE FROM t WHERE id=1)='A';",
 'collation_nested':"SELECT (SELECT (SELECT v COLLATE NOCASE FROM t WHERE id=1))='A';",
 'json_source':"SELECT json_array((SELECT json_array(n) FROM t ORDER BY id LIMIT 1));",
 'json_nested':"SELECT json_array((SELECT (SELECT json('[1]'))));",
 'json_mixed':"SELECT id,json_array((SELECT CASE WHEN a.id=1 THEN json('[1]') ELSE '[1]' END)) FROM t a ORDER BY id;",
 'json_subtype':"SELECT json_array((SELECT json('[1]')));",
 'order_lazy':"SELECT (SELECT CASE WHEN id=1 THEN n ELSE json('bad') END FROM t LIMIT 1);",
 'first_null':'SELECT (SELECT NULL FROM t);',
 'qualified':'SELECT (SELECT t.n FROM t WHERE id=2);',
 'outer_shadow':'SELECT a.id,(SELECT a.n FROM t a WHERE id=2) FROM t a ORDER BY id;',
 'quoted_outer':'SELECT a.id,(SELECT "a"."n") FROM t a ORDER BY id;',
 'compound':'SELECT (SELECT 3 UNION ALL SELECT 4);',
 'values':'SELECT (VALUES(3),(4));',
 'dead_missing':'SELECT CASE WHEN 1 THEN 7 ELSE (SELECT missing FROM t) END;',
 'lazy_coalesce':"SELECT coalesce(7,(SELECT json('bad')));",
 'lazy_where':"SELECT id FROM t WHERE 0 AND (SELECT json('bad'));",
 'empty_outer':"SELECT (SELECT json('bad')) FROM t WHERE id<0;",
 'outer_limit_zero':"SELECT (SELECT json('bad')) FROM t LIMIT 0;",
 'private_annotation':"SELECT __sqlean_bound_value(1,'INT');",
 'private_uppercase':"SELECT __SQLEAN_BOUND_VALUE(1,'INT');",
 'constant':'SELECT (SELECT 42);',
 'aggregate':'SELECT id,(SELECT max(n) FROM t) FROM t ORDER BY id;',
 'correlated':'SELECT a.id,(SELECT sum(b.n) FROM t b WHERE b.id<=a.id) FROM t a ORDER BY a.id;',
 'correlated_alias':'SELECT a.id,(SELECT b.v FROM t b WHERE b.id=a.id) FROM t a ORDER BY a.id;',
 'unqualified_inner':'SELECT a.id,(SELECT n FROM t WHERE id=a.id) FROM t a ORDER BY a.id;',
 'outer_only':'SELECT a.id,(SELECT a.n+1) FROM t a ORDER BY a.id;',
 'empty':'SELECT (SELECT n FROM t WHERE id<0);',
 'first_row':'SELECT (SELECT n FROM t);',
 'ordered':'SELECT (SELECT n FROM t ORDER BY n DESC);',
 'limit_offset':'SELECT (SELECT n FROM t ORDER BY id LIMIT 1 OFFSET 1);',
 'limit_zero':'SELECT (SELECT n FROM t LIMIT 0);',
 'filter':'SELECT id FROM t a WHERE n>(SELECT min(n) FROM t) ORDER BY id;',
 'ordering':'SELECT id FROM t a ORDER BY (SELECT -a.n),id;',
 'coalesce':'SELECT coalesce((SELECT n FROM t WHERE 0),99);',
 'lazy_case':"SELECT CASE WHEN 1 THEN 7 ELSE (SELECT json('bad')) END;",
 'lazy_rows':"SELECT id,CASE WHEN id<4 THEN n ELSE (SELECT json('bad')) END FROM t ORDER BY id;",
 'lazy_iif':"SELECT iif(1,7,(SELECT json('bad')));",
 'bad_column':'SELECT (SELECT missing FROM t) WHERE 0;',
 'bad_table':'SELECT (SELECT n FROM missing) WHERE 0;',
 'width':'SELECT (SELECT id,n FROM t);',
 'width_dead':'SELECT CASE WHEN 1 THEN 7 ELSE (SELECT id,n FROM t) END;',
 'column_affinity':"SELECT (SELECT n FROM t WHERE id=1)='3',(SELECT v FROM t WHERE id=1)=3;",
 'computed_affinity':"SELECT (SELECT n+0 FROM t WHERE id=1)='3';",
 'nested':'SELECT a.id,(SELECT (SELECT a.n+1)) FROM t a ORDER BY id;',
}
rng=random.Random(int(os.environ.get('SQLEANITE_SUBQUERY_SEED','357900')))
CASES=[(name,sql,SETUP) for name,sql in QUERIES.items()]
for i in range(12):
 rows=','.join(f"({j},'v{j}',{rng.randrange(-100,100)})" for j in range(1,9))
 setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES'+rows+';'
 CASES.append(('generated_'+str(i),'SELECT a.id,(SELECT sum(b.n) FROM t b WHERE b.id<=a.id),(SELECT max(b.n) FROM t b WHERE b.id>a.id) FROM t a ORDER BY id;',setup))
class ScalarSubqueries(unittest.TestCase):pass
for name,sql,setup in CASES:
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(ScalarSubqueries,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
