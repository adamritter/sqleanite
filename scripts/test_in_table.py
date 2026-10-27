#!/usr/bin/env python3
"""Reference comparisons for SQLite's IN table shorthand and certified names."""
import os
import random
import unittest
from test_pragma_tables import case

class InTable(unittest.TestCase):
    pass

SETUP = '''CREATE TABLE t(x INTEGER);INSERT INTO t VALUES(1),(2),(NULL);
CREATE TABLE e(x);CREATE TABLE wide(x,y);CREATE TABLE "odd name"(x);
INSERT INTO "odd name" VALUES('A');CREATE TABLE "a.b"(x);INSERT INTO "a.b" VALUES(3);
CREATE TABLE "t\"\"x"(x);INSERT INTO "t\"\"x" VALUES(4);
CREATE TABLE "t); SELECT 99; --"(x);INSERT INTO "t); SELECT 99; --" VALUES(5);'''
QUERIES = {
    'in': 'SELECT 1 IN t,3 IN t,NULL IN t;',
    'not_in': 'SELECT 1 NOT IN t,3 NOT IN t,NULL NOT IN t;',
    'empty': 'SELECT NULL IN e,NULL NOT IN e,1 IN e,1 NOT IN e;',
    'case': 'SELECT 1 IN T,1 NOT IN T;',
    'main': 'SELECT 1 IN main.t,3 NOT IN main.t;',
    'quoted_main': 'SELECT 1 IN "main"."t";',
    'quoted': 'SELECT \'a\' IN "odd name",\'a\' COLLATE NOCASE IN "odd name";',
    'single_quoted': "SELECT 'A' IN 'odd name';",
    'bracket': "SELECT 'A' IN [odd name];",
    'backtick': "SELECT 'A' IN `odd name`;",
    'dot_name': 'SELECT 3 IN "a.b",3 NOT IN "a.b";',
    'embedded_quote': 'SELECT 4 IN "t\"\"x";',
    'syntax_in_name': 'SELECT 5 IN "t); SELECT 99; --";',
    'comment': 'SELECT 1 IN /* before */ main /* dot */ . /* table */ t;',
    'precedence': 'SELECT NOT 1 IN t,NOT (1 IN t),1 NOT IN t,1 IN t=1;',
    'nested_left': 'SELECT (SELECT 1) IN t,EXISTS(SELECT 1) NOT IN e;',
    'where': 'SELECT x FROM t WHERE x IN t ORDER BY x;',
    'correlated': 'SELECT x,(SELECT t.x IN t) FROM t ORDER BY rowid;',
    'wide': 'SELECT 1 IN wide;',
    'wide_not_in': 'SELECT 1 NOT IN wide;',
    'missing': 'SELECT 1 IN missing;',
    'missing_schema': 'SELECT 1 IN missing.t;',
    'lazy_error': 'SELECT CASE WHEN 1 THEN 7 ELSE abs(-9223372036854775808) IN t END;',
    'lazy_name_check': 'SELECT CASE WHEN 1 THEN 7 ELSE 1 IN missing END;',
    'folded': 'SELECT 0 AND 1 IN missing;',
    'left_error': 'SELECT abs(-9223372036854775808) IN e;',
}
for name, sql in QUERIES.items():
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(InTable, 'test_' + name + '_' + suffix, case(sql, mode, SETUP))
rng = random.Random(int(os.environ.get('SQLEANITE_IN_TABLE_SEED', '365301')))
for i in range(12):
    values = [rng.randrange(-20, 20) for _ in range(rng.randrange(1, 12))]
    needle = rng.randrange(-20, 20)
    setup = 'CREATE TABLE fresh(x INTEGER);INSERT INTO fresh VALUES' + ','.join(f'({v})' for v in values) + ',(NULL);'
    sql = f'SELECT {needle} IN fresh,{needle} NOT IN main.fresh;'
    for suffix, mode in [('rollback', '--verified-file'), ('wal', '--verified-wal-file')]:
        setattr(InTable, f'test_fresh_{i}_{suffix}', case(sql, mode, setup))
if __name__ == '__main__':
    unittest.main()
