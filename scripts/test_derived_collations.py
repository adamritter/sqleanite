#!/usr/bin/env python3
"""Declared result metadata through private derived/CTE materializations."""
import os
import random
import unittest
from test_check_add_column import case

class DerivedCollations(unittest.TestCase):
    pass

QUERIES={
    'derived_where': "SELECT id,v FROM (SELECT id,v FROM t) AS d WHERE v='A' ORDER BY id;",
    'derived_star': "SELECT id,v FROM (SELECT * FROM t) AS d WHERE v='A' ORDER BY id;",
    'derived_qualified': "SELECT d.id,d.v FROM (SELECT id,v FROM t) AS d WHERE d.v='A' ORDER BY d.id;",
    'derived_alias': "SELECT x FROM (SELECT v AS x FROM t) AS d WHERE x='A' ORDER BY x;",
    'derived_order': 'SELECT v FROM (SELECT v FROM t) AS d ORDER BY v;',
    'derived_distinct': 'SELECT DISTINCT v FROM (SELECT v FROM t) AS d ORDER BY v;',
    'derived_group': 'SELECT v,count(*) FROM (SELECT v FROM t) AS d GROUP BY v ORDER BY v;',
    'derived_nested': "SELECT id FROM (SELECT id,v FROM (SELECT id,v FROM t) AS x) AS d WHERE v='A' ORDER BY id;",
    'derived_union': "SELECT v FROM (SELECT v FROM t UNION SELECT 'A') AS d WHERE v='A' ORDER BY v;",
    'derived_union_all': "SELECT v FROM (SELECT v FROM t UNION ALL SELECT 'A') AS d WHERE v='A' ORDER BY v;",
    'derived_right_explicit': "SELECT x='A' FROM (SELECT 'a' AS x UNION ALL SELECT 'b' COLLATE NOCASE) AS d;",
    'derived_right_declared': "SELECT x='A' FROM (SELECT 'a' AS x UNION ALL SELECT v FROM t) AS d;",
    'derived_first_binary': "SELECT x='A' FROM (SELECT w AS x FROM t UNION ALL SELECT v FROM t) AS d;",
    'derived_first_cast_binary': "SELECT x='A' FROM (SELECT CAST('a' AS TEXT) AS x UNION ALL SELECT v FROM t) AS d;",
    'cte_values_cast_first': "WITH q(x) AS (VALUES(CAST('a' AS TEXT)),('b' COLLATE NOCASE)) SELECT x='A' FROM q;",
    'derived_explicit_binary': "SELECT id FROM (SELECT id,v COLLATE BINARY AS x FROM t) AS d WHERE x='A' ORDER BY id;",
    'derived_explicit_nocase': "SELECT id FROM (SELECT id,w COLLATE NOCASE AS x FROM t) AS d WHERE x='a' ORDER BY id;",
    'derived_explicit_rtrim': "SELECT id FROM (SELECT id,w COLLATE RTRIM AS x FROM t) AS d WHERE x='A' ORDER BY id;",
    'derived_outer_override': "SELECT id FROM (SELECT id,v FROM t) AS d WHERE v COLLATE BINARY='A' ORDER BY id;",
    'derived_unary_plus': "SELECT id FROM (SELECT id,+v AS x FROM t) AS d WHERE x='A' ORDER BY id;",
    'derived_cast': "SELECT id FROM (SELECT id,CAST(v AS TEXT) AS x FROM t) AS d WHERE x='A' ORDER BY id;",
    'derived_function_binary': "SELECT id FROM (SELECT id,lower(v) AS x FROM t) AS d WHERE x='A' ORDER BY id;",
    'derived_concat_binary': "SELECT id FROM (SELECT id,v||'' AS x FROM t) AS d WHERE x='A' ORDER BY id;",
    'derived_case_binary': "SELECT id FROM (SELECT id,CASE WHEN 1 THEN v END AS x FROM t) AS d WHERE x='A' ORDER BY id;",
    'derived_correlated_in': "SELECT id,v IN (SELECT w FROM t AS x WHERE x.id=d.id) FROM (SELECT id,v FROM t) AS d ORDER BY id;",
    'derived_join': "SELECT d.id,b.id FROM (SELECT id,v FROM t) AS d JOIN t AS b ON d.v=b.w ORDER BY d.id,b.id;",
    'derived_join_reverse': "SELECT d.id,b.id FROM (SELECT id,v FROM t) AS d JOIN t AS b ON b.w=d.v ORDER BY d.id,b.id;",
    'derived_join_binary': "SELECT d.id,b.id FROM (SELECT id,v FROM t) AS d JOIN t AS b ON d.v COLLATE BINARY=b.w ORDER BY d.id,b.id;",
    'derived_join_nocase': "SELECT d.id,b.id FROM (SELECT id,v FROM t) AS d JOIN t AS b ON b.w COLLATE NOCASE=d.v ORDER BY d.id,b.id;",
    'derived_join_left': "SELECT d.id,b.id FROM (SELECT id,v FROM t) AS d LEFT JOIN t AS b ON d.v=b.w ORDER BY d.id,b.id;",
    'derived_join_range': "SELECT d.id,b.id FROM (SELECT id,v FROM t) AS d JOIN t AS b ON d.v<b.w ORDER BY d.id,b.id;",
    'derived_empty': "SELECT v FROM (SELECT v FROM t WHERE 0) AS d UNION SELECT 'A' ORDER BY 1;",
    'derived_zero_limit': "SELECT v FROM (SELECT v FROM t LIMIT 0) AS d UNION SELECT 'A' ORDER BY 1;",
    'derived_duplicate_name': "SELECT x,\"x:1\" FROM (SELECT v AS x,v AS x FROM t) AS d WHERE x='A' ORDER BY x;",
    'cte_default': "WITH q AS (SELECT id,v FROM t) SELECT id FROM q WHERE v='A' ORDER BY id;",
    'cte_materialized': "WITH q AS MATERIALIZED (SELECT id,v FROM t) SELECT id FROM q WHERE v='A' ORDER BY id;",
    'cte_not_materialized': "WITH q AS NOT MATERIALIZED (SELECT id,v FROM t) SELECT id FROM q WHERE v='A' ORDER BY id;",
    'cte_aliases': "WITH q(a,b) AS (SELECT id,v FROM t) SELECT a FROM q WHERE b='A' ORDER BY a;",
    'cte_nested': "WITH q AS (SELECT id,v FROM t), r AS (SELECT id,v FROM q) SELECT id FROM r WHERE v='A' ORDER BY id;",
    'cte_join': "WITH q AS (SELECT id,v FROM t) SELECT a.id,b.id FROM q AS a JOIN q AS b ON a.v=b.v ORDER BY a.id,b.id;",
    'cte_values_first': "WITH q(x) AS (VALUES('a' COLLATE NOCASE),('A'),('b')) SELECT x FROM q WHERE x='A' ORDER BY x;",
    'cte_values_later': "WITH q(x) AS (VALUES('a'),('A' COLLATE NOCASE),('b')) SELECT x FROM q WHERE x='A' ORDER BY x;",
    'cte_explicit_binary': "WITH q(x) AS (SELECT v COLLATE BINARY FROM t) SELECT x FROM q WHERE x='A' ORDER BY x;",
    'cte_explicit_nocase': "WITH q(x) AS (SELECT w COLLATE NOCASE FROM t) SELECT x FROM q WHERE x='a' ORDER BY x;",
    'scalar_correlated_derived': "SELECT id,(SELECT x FROM (SELECT t.v AS x) AS d)='A' FROM t ORDER BY id;",
    'scalar_in_derived': "SELECT 'A' IN (SELECT v FROM (SELECT v FROM t) AS d);",
    'scalar_lazy_derived': "SELECT CASE WHEN 0 THEN (SELECT x FROM (SELECT abs(-9223372036854775808) AS x) AS d) ELSE 17 END;",
    'scalar_lazy_invalid_name': "SELECT CASE WHEN 0 THEN (SELECT x FROM (SELECT missing AS x) AS d) ELSE 17 END;",
    'scalar_zero_limit_derived': "SELECT (SELECT x FROM (SELECT abs(-9223372036854775808) AS x) AS d LIMIT 0);",
    'cte_three': "WITH q AS (SELECT id,v FROM t), r AS (SELECT * FROM q), s AS (SELECT * FROM r) SELECT id FROM s WHERE v='A' ORDER BY id;",
    'cte_unused_first': "WITH q AS (SELECT abs(-9223372036854775808)), r AS (SELECT 17 AS x) SELECT x FROM r;",
    'cte_unused_chain': "WITH q AS (SELECT abs(-9223372036854775808)), r AS (SELECT * FROM q), s AS (SELECT 17 AS x) SELECT x FROM s;",
    'cte_recursive_keyword': "WITH RECURSIVE q AS (SELECT id,v FROM t), r AS (SELECT * FROM q) SELECT id FROM r WHERE v='A' ORDER BY id;",
    'cte_duplicate': "WITH q AS (SELECT v FROM t), q AS (SELECT 1) SELECT * FROM q;",
    'scalar_boundary_binary': "SELECT (SELECT v FROM (SELECT v FROM t) AS d WHERE v='a' LIMIT 1)='A';",
    'ctas_binary': "CREATE TABLE c AS SELECT v FROM (SELECT v FROM t) AS d;PRAGMA table_info(c);SELECT count(*) FROM c WHERE v='A';",
    'insert_source': "CREATE TABLE c(v TEXT);INSERT INTO c SELECT v FROM (SELECT v FROM t) AS d WHERE v='A';SELECT rowid,v FROM c ORDER BY rowid;",
    'private_state': "SELECT last_insert_rowid(),changes(),total_changes();SELECT v FROM (SELECT v FROM t) AS d ORDER BY v;SELECT last_insert_rowid(),changes(),total_changes();SELECT count(*) FROM sqlite_schema;",
}
for collation in ('NOCASE','RTRIM'):
    setup=f'CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT COLLATE {collation},w TEXT);'+"INSERT INTO t VALUES(1,'a','A'),(2,'A','a'),(3,'b','B'),(4,'a ','A '),(5,NULL,'X');"
    for name,sql in QUERIES.items():
        for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
            setattr(DerivedCollations,'test_'+collation.lower()+'_'+name+'_'+suffix,case(sql,mode,setup))
EXTRA={
    'recursive_declared_filter': "WITH RECURSIVE q(x,n) AS (SELECT 'a' COLLATE NOCASE,1 UNION ALL SELECT x,n+1 FROM q WHERE x='A' AND n<3) SELECT x,n FROM q ORDER BY n;",
    'recursive_declared_union': "WITH RECURSIVE q(x) AS (SELECT 'a' COLLATE NOCASE UNION SELECT 'A' FROM q) SELECT x FROM q;",
    'recursive_declared_union_null': "WITH RECURSIVE q(x) AS (SELECT NULL COLLATE NOCASE UNION SELECT 'A' FROM q WHERE x IS NULL UNION SELECT 'a' FROM q WHERE x IS NOT NULL) SELECT x FROM q;",
    'recursive_rtrim_filter': "WITH RECURSIVE q(x,n) AS (SELECT 'a ' COLLATE RTRIM,1 UNION ALL SELECT x,n+1 FROM q WHERE x='a' AND n<3) SELECT x,n FROM q ORDER BY n;",
    'recursive_rhs_distinct_collation': "WITH RECURSIVE q(x) AS (SELECT 'a' UNION SELECT 'A' COLLATE NOCASE FROM q) SELECT x,x='A' FROM q;",
    'recursive_seed_distinct_collation': "WITH RECURSIVE q(x) AS (SELECT 'a' COLLATE NOCASE UNION SELECT 'A' COLLATE BINARY FROM q) SELECT x,x='A' FROM q;",
    'recursive_binary_override': "WITH RECURSIVE q(x,n) AS (SELECT 'a' COLLATE NOCASE,1 UNION ALL SELECT x,n+1 FROM q WHERE x COLLATE BINARY='A' AND n<3) SELECT x,n FROM q ORDER BY n;",
    'recursive_empty_invalid_function': 'WITH RECURSIVE q(x) AS (SELECT 1 WHERE 0 UNION ALL SELECT absent(x) FROM q) SELECT * FROM q;',
    'recursive_empty_invalid_column': 'WITH RECURSIVE q(x) AS (SELECT 1 WHERE 0 UNION ALL SELECT missing FROM q) SELECT * FROM q;',
    'recursive_empty_runtime_skipped': 'WITH RECURSIVE q(x) AS (SELECT 1 WHERE 0 UNION ALL SELECT abs(-9223372036854775808) FROM q) SELECT * FROM q;',
    'recursive_prepare_before_seed': 'WITH RECURSIVE q(x) AS (SELECT abs(-9223372036854775808) UNION ALL SELECT absent(x) FROM q) SELECT * FROM q;',
    'quoted_alias': 'SELECT "X X" FROM (SELECT v AS "X X" FROM t) AS d WHERE "X X"=\'A\' ORDER BY "X X";',
    'generated_source': "CREATE TABLE g(a TEXT,b TEXT COLLATE NOCASE AS(a) STORED);INSERT INTO g(a) VALUES('a'),('A');SELECT b FROM (SELECT b FROM g) AS d WHERE b='A' ORDER BY b;",
}
setup="CREATE TABLE t(v TEXT COLLATE NOCASE);INSERT INTO t VALUES('a'),('A');"
for name,sql in EXTRA.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(DerivedCollations,'test_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_DERIVED_COLLATION_SEED','370401')))
for i in range(8):
    values=[rng.choice(['a','A','b','B','a ']) for _ in range(rng.randrange(2,12))]
    setup='CREATE TABLE t(v TEXT COLLATE NOCASE);INSERT INTO t VALUES'+','.join("('"+v+"')" for v in values)+';'
    sql="WITH q AS MATERIALIZED (SELECT v FROM t) SELECT v,count(*) FROM q GROUP BY v ORDER BY v;"
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(DerivedCollations,f'test_fresh_{i}_{suffix}',case(sql,mode,setup))
if __name__=='__main__':
    unittest.main()
