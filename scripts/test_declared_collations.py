#!/usr/bin/env python3
"""Declared BINARY/NOCASE/RTRIM on ordinary rowid columns without collation indexes."""
import os
import random
import unittest
from test_check_add_column import case

class DeclaredCollations(unittest.TestCase):
    pass

QUERIES={
    'all': 'SELECT * FROM t ORDER BY id;',
    'equal': "SELECT id FROM t WHERE v='a' ORDER BY id;",
    'not_equal': "SELECT id FROM t WHERE v!='a' ORDER BY id;",
    'is': "SELECT id FROM t WHERE v IS 'a' ORDER BY id;",
    'is_not': "SELECT id FROM t WHERE v IS NOT 'a' ORDER BY id;",
    'less': "SELECT id FROM t WHERE v<'b' ORDER BY id;",
    'right_literal': "SELECT id FROM t WHERE 'a'=v ORDER BY id;",
    'binary_left': 'SELECT id FROM t WHERE w=v ORDER BY id;',
    'declared_left': 'SELECT id FROM t WHERE v=w ORDER BY id;',
    'explicit_right': "SELECT id FROM t WHERE v='a' COLLATE BINARY ORDER BY id;",
    'explicit_left': "SELECT id FROM t WHERE v COLLATE BINARY='a' ORDER BY id;",
    'explicit_nocase': "SELECT id FROM t WHERE v='a' COLLATE NOCASE ORDER BY id;",
    'explicit_rtrim': "SELECT id FROM t WHERE v='a' COLLATE RTRIM ORDER BY id;",
    'order': 'SELECT id,v FROM t ORDER BY v,id;',
    'reverse_order': 'SELECT id,v FROM t ORDER BY v DESC,id;',
    'order_alias': 'SELECT v AS label,id FROM t ORDER BY label,id;',
    'order_ordinal': 'SELECT v,id FROM t ORDER BY 1,id;',
    'order_explicit_binary': 'SELECT id,v FROM t ORDER BY v COLLATE BINARY,id;',
    'order_plus': 'SELECT id,v FROM t ORDER BY +v,id;',
    'order_cast': 'SELECT id,v FROM t ORDER BY CAST(v AS TEXT),id;',
    'order_limit': 'SELECT id,v FROM t ORDER BY v,id LIMIT 2 OFFSET 1;',
    'order_reverse_limit': 'SELECT id,v FROM t ORDER BY v DESC,id LIMIT 2;',
    'correlated_bool': "SELECT id,(SELECT v='a') FROM t ORDER BY id;",
    'scalar_local': "SELECT (SELECT count(*) FROM t WHERE v='a');",
    'correlated_local': "SELECT id,(SELECT count(*) FROM t u WHERE u.v=t.v) FROM t ORDER BY id;",
    'distinct': 'SELECT DISTINCT v FROM t ORDER BY v;',
    'group': 'SELECT v,count(*) FROM t GROUP BY v ORDER BY min(id);',
    'having': 'SELECT v,count(*) FROM t GROUP BY v HAVING count(*)>1 ORDER BY min(id);',
    'count_distinct': 'SELECT count(DISTINCT v) FROM t;',
    'aggregate_min_max': 'SELECT min(v),max(v) FROM t;',
    'scalar_min': "SELECT id,min(v,'A') FROM t ORDER BY id;",
    'scalar_max': "SELECT id,max(v,'A') FROM t ORDER BY id;",
    'nullif': 'SELECT id,nullif(v,w) FROM t ORDER BY id;',
    'in_single': "SELECT id FROM t WHERE v IN ('a') ORDER BY id;",
    'in_multiple': "SELECT id FROM t WHERE v IN ('a','B') ORDER BY id;",
    'not_in': "SELECT id FROM t WHERE v NOT IN ('a','B') ORDER BY id;",
    'between': "SELECT id FROM t WHERE v BETWEEN 'a' AND 'b' ORDER BY id;",
    'case_base': "SELECT id,CASE v WHEN 'a' THEN 1 ELSE 0 END FROM t ORDER BY id;",
    'unary_plus': "SELECT id FROM t WHERE +v='a' ORDER BY id;",
    'cast': "SELECT id FROM t WHERE CAST(v AS TEXT)='a' ORDER BY id;",
    'concat_loses': "SELECT id FROM t WHERE (v||'')='a' ORDER BY id;",
    'function_loses': "SELECT id FROM t WHERE upper(v)='a' ORDER BY id;",
    'projection': "SELECT id,v='a',typeof(v) FROM t ORDER BY id;",
    'update': "UPDATE t SET n=n+1 WHERE v='a';SELECT id,n FROM t ORDER BY id;",
    'update_rhs': "UPDATE t SET n=(v='a') RETURNING id,n;",
    'update_returning': "UPDATE t SET n=n+1 WHERE v='a' RETURNING id,v='a';",
    'delete': "DELETE FROM t WHERE v='a';SELECT id FROM t ORDER BY id;",
    'delete_returning': "DELETE FROM t WHERE v='a' RETURNING id,v='a';",
    'info': 'PRAGMA table_info(t);',
    'ctas_binary': "CREATE TABLE c AS SELECT v FROM t;SELECT count(*) FROM c WHERE v='a';",
    'rollback': "BEGIN;UPDATE t SET v='changed' WHERE v='a';ROLLBACK;SELECT * FROM t ORDER BY id;",
}
for collation in ('NOCASE','RTRIM'):
    setup=f'CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT COLLATE {collation},w TEXT,n INTEGER);' + "INSERT INTO t VALUES(1,'a','A',1),(2,'A','a',2),(3,'b','b',3),(4,'a ','A ',4),(5,NULL,'A',5);"
    for name,sql in QUERIES.items():
        for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
            setattr(DeclaredCollations,'test_'+collation.lower()+'_'+name+'_'+suffix,case(sql,mode,setup))
EXTRA={
    'create': ('',"CREATE TABLE g(v TEXT COLLATE NOCASE);INSERT INTO g VALUES('a'),('A');SELECT count(*) FROM g WHERE v='a';"),
    'create_rtrim': ('',"CREATE TABLE g(v TEXT COLLATE RTRIM);INSERT INTO g VALUES('a'),('a ');SELECT count(*) FROM g WHERE v='a';"),
    'check_pass': ('',"CREATE TABLE g(v TEXT COLLATE NOCASE CHECK(v='a'));INSERT INTO g VALUES('A');SELECT * FROM g;"),
    'check_fail': ("CREATE TABLE g(v TEXT COLLATE NOCASE CHECK(v='a'));", "INSERT INTO g VALUES('b');"),
    'generated': ("CREATE TABLE g(v TEXT COLLATE NOCASE,b AS(v='a') STORED);", "INSERT INTO g(v)VALUES('A')RETURNING v,b;"),
    'strict': ("CREATE TABLE g(v TEXT COLLATE NOCASE) STRICT;", "INSERT INTO g VALUES('a'),('A');SELECT count(*) FROM g WHERE v='a';"),
    'rename': ("CREATE TABLE g(v TEXT COLLATE NOCASE);INSERT INTO g VALUES('a'),('A');", "ALTER TABLE g RENAME v TO renamed;SELECT count(*) FROM g WHERE renamed='a';"),
    'rename_table': ("CREATE TABLE g(v TEXT COLLATE NOCASE);INSERT INTO g VALUES('a'),('A');", "ALTER TABLE g RENAME TO renamed;SELECT count(*) FROM renamed WHERE v='a';"),
    'quoted': ('CREATE TABLE "odd table"("odd column" TEXT COLLATE NOCASE);INSERT INTO "odd table"VALUES(\'a\'),(\'A\');', 'SELECT count(*) FROM "odd table" WHERE "odd column"=\'a\';'),
    'unknown': ('','CREATE TABLE g(v COLLATE absent);'),
    'unicode_ascii_only': ("CREATE TABLE g(v TEXT COLLATE NOCASE);INSERT INTO g VALUES('á'),('Á'),('a'),('A');", "SELECT count(*) FROM g WHERE v='á';SELECT count(*) FROM g WHERE v='a';"),
    'binary_control': ("CREATE TABLE g(v TEXT COLLATE BINARY);INSERT INTO g VALUES('a'),('A');", "SELECT count(*) FROM g WHERE v='a';"),
}
for name,(setup,sql) in EXTRA.items():
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(DeclaredCollations,'test_'+name+'_'+suffix,case(sql,mode,setup))
rng=random.Random(int(os.environ.get('SQLEANITE_DECLARED_COLLATION_SEED','369001')))
for i in range(8):
    values=[rng.choice(['a','A','b','B','a ']) for _ in range(rng.randrange(2,12))]
    setup='CREATE TABLE g(v TEXT COLLATE NOCASE);INSERT INTO g VALUES'+','.join("('"+v+"')" for v in values)+';'
    sql="SELECT count(*) FROM g WHERE v='a';SELECT v,count(*) FROM g GROUP BY v ORDER BY v;"
    for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
        setattr(DeclaredCollations,f'test_fresh_{i}_{suffix}',case(sql,mode,setup))
if __name__=='__main__':
    unittest.main()
