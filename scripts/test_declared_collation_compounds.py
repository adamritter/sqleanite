#!/usr/bin/env python3
"""Declared result collations through UNION/INTERSECT/EXCEPT and compound tails."""
import os
import random
import unittest
from test_check_add_column import case

class DeclaredCompounds(unittest.TestCase):
    pass

QUERIES={
    'union': "SELECT v FROM t UNION SELECT 'A';",
    'union_order': "SELECT v FROM t UNION SELECT 'A' ORDER BY 1;",
    'union_all': "SELECT v FROM t UNION ALL SELECT 'A';",
    'union_all_order': "SELECT v FROM t UNION ALL SELECT 'A' ORDER BY 1;",
    'intersect': "SELECT v FROM t INTERSECT SELECT 'A';",
    'except': "SELECT v FROM t EXCEPT SELECT 'A';",
    'literal_first': "SELECT 'A' UNION SELECT v FROM t ORDER BY 1;",
    'literal_first_intersect': "SELECT 'A' INTERSECT SELECT v FROM t;",
    'binary_first': 'SELECT w FROM t UNION SELECT v FROM t ORDER BY 1;',
    'declared_first': 'SELECT v FROM t UNION SELECT w FROM t ORDER BY 1;',
    'explicit_binary': "SELECT v COLLATE BINARY FROM t UNION SELECT 'A' ORDER BY 1;",
    'explicit_rtrim': "SELECT v COLLATE RTRIM FROM t UNION SELECT 'A' ORDER BY 1;",
    'right_explicit': 'SELECT w FROM t UNION SELECT v COLLATE NOCASE FROM t ORDER BY 1;',
    'function_loses': "SELECT upper(v) FROM t UNION SELECT 'a' ORDER BY 1;",
    'unary_plus': "SELECT +v FROM t UNION SELECT 'A' ORDER BY 1;",
    'cast': "SELECT CAST(v AS TEXT) FROM t UNION SELECT 'A' ORDER BY 1;",
    'where': "SELECT v FROM t WHERE v='a' UNION SELECT 'A' ORDER BY 1;",
    'tail_limit': "SELECT v FROM t UNION SELECT 'A' ORDER BY 1 DESC LIMIT 2 OFFSET 1;",
    'all_tail_limit': "SELECT v FROM t UNION ALL SELECT 'A' ORDER BY 1 DESC LIMIT 3 OFFSET 1;",
    'multiple_columns': "SELECT 0,v FROM t UNION SELECT 0,'A' ORDER BY 2;",
    'three_arms': "SELECT v FROM t UNION SELECT 'A' EXCEPT SELECT 'a' ORDER BY 1;",
    'all_then_union': "SELECT v FROM t UNION ALL SELECT 'A' UNION SELECT 'a' ORDER BY 1;",
    'empty_left': "SELECT v FROM t WHERE 0 UNION SELECT 'A';",
    'null_right': 'SELECT v FROM t UNION SELECT NULL ORDER BY 1;',
    'in_query': "SELECT 'A' IN (SELECT v FROM t WHERE id=1 UNION ALL SELECT NULL);",
    'in_first_explicit_null': "SELECT 'A' IN (SELECT v COLLATE NOCASE FROM t WHERE id=1 UNION ALL SELECT NULL);",
    'in_last_declared': "SELECT 'A' IN (SELECT NULL UNION ALL SELECT v FROM t WHERE id=1);",
    'in_last_explicit': "SELECT 'A' IN (SELECT NULL UNION ALL SELECT v COLLATE NOCASE FROM t WHERE id=1);",
    'in_left_explicit': "SELECT 'A' COLLATE NOCASE IN (SELECT v FROM t WHERE id=1 UNION ALL SELECT NULL);",
    'in_values_first': "SELECT 'A' IN (VALUES('a' COLLATE NOCASE),(NULL));",
    'in_values_last': "SELECT 'A' IN (VALUES(NULL),('a' COLLATE NOCASE));",
    'in_right_binary': "SELECT v IN (SELECT NULL UNION ALL SELECT w COLLATE BINARY FROM t WHERE id=1) FROM t ORDER BY id;",
    'in_left_binary': "SELECT w COLLATE BINARY IN (SELECT NULL UNION ALL SELECT v FROM t WHERE id=1) FROM t ORDER BY id;",
    'in_join_last_declared': "SELECT 'A' IN (SELECT NULL UNION ALL SELECT l.v FROM t AS l JOIN t AS r ON l.id=r.id WHERE l.id=1);",
    'in_join_last_explicit': "SELECT 'A' IN (SELECT NULL UNION ALL SELECT l.w COLLATE NOCASE FROM t AS l JOIN t AS r ON l.id=r.id WHERE l.id=1);",
    'in_join_first_declared': "SELECT 'A' IN (SELECT l.v FROM t AS l JOIN t AS r ON l.id=r.id WHERE l.id=1 UNION ALL SELECT NULL);",
    'in_join_last_binary': "SELECT 'A' IN (SELECT NULL UNION ALL SELECT l.v COLLATE BINARY FROM t AS l JOIN t AS r ON l.id=r.id WHERE l.id=1);",
    'in_join_left_binary': "SELECT 'A' COLLATE BINARY IN (SELECT NULL UNION ALL SELECT l.v FROM t AS l JOIN t AS r ON l.id=r.id WHERE l.id=1);",
    'in_join_correlated': "SELECT x.id,'A' IN (SELECT NULL UNION ALL SELECT l.v FROM t AS l JOIN t AS r ON l.id=r.id WHERE l.id=x.id) FROM t AS x ORDER BY x.id;",
    'ctas_binary': "CREATE TABLE c AS SELECT v FROM t UNION SELECT 'A';SELECT count(*) FROM c WHERE v='a';PRAGMA table_info(c);",
}
for collation in ('NOCASE','RTRIM'):
    setup=f'CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT COLLATE {collation},w TEXT);'+"INSERT INTO t VALUES(1,'a','A'),(2,'A','a'),(3,'b','B'),(4,'a ','A '),(5,NULL,'X');"
    for name,sql in QUERIES.items():
        for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
            setattr(DeclaredCompounds,'test_'+collation.lower()+'_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_DECLARED_COMPOUND_SEED','369401')))
for i in range(8):
    values=[rng.choice(['a','A','b','B','a ']) for _ in range(rng.randrange(2,12))]
    setup='CREATE TABLE t(v TEXT COLLATE NOCASE);INSERT INTO t VALUES'+','.join("('"+v+"')" for v in values)+';'
    sql="SELECT v FROM t UNION SELECT 'A' ORDER BY 1;SELECT v FROM t EXCEPT SELECT 'A' ORDER BY 1;"
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(DeclaredCompounds,f'test_fresh_{i}_{suffix}',case(sql,mode,setup))
if __name__=='__main__':
    unittest.main()
