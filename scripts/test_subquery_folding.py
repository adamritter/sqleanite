#!/usr/bin/env python3
"""Parser-time subquery folding, including erased name-resolution failures."""
import os
import random
import unittest
from test_pragma_tables import case
class SubqueryFolding(unittest.TestCase): pass
QUERIES={
 'scalar_missing':'SELECT 0 AND (SELECT missing);',
 'scalar_error':'SELECT 0 AND (SELECT abs(-9223372036854775808));',
 'exists_missing':'SELECT 0 AND EXISTS(SELECT missing FROM absent);',
 'in_missing':'SELECT 0 AND 1 IN (SELECT missing);',
 'scalar_empty_in':'SELECT (SELECT missing) IN ();',
 'exists_empty_in':'SELECT EXISTS(SELECT missing FROM absent) IN ();',
 'aggregate_missing':'SELECT 0 AND (SELECT sum(missing) FROM absent);',
 'collate_missing':'SELECT 0 AND ((SELECT missing) COLLATE BINARY);',
 'right_zero':'SELECT (SELECT missing) AND 0;',
 'where':'SELECT * FROM t WHERE 0 AND (SELECT missing);',
 'nested':'SELECT (SELECT 0 AND (SELECT missing));',
 'order':'SELECT x FROM t ORDER BY 0 AND (SELECT missing),x;',
 'order_second':'SELECT x FROM t ORDER BY x,0 AND EXISTS(SELECT missing);',
 'order_third':'SELECT x FROM t ORDER BY x,x,0 AND 1 IN (SELECT missing);',
 'order_eleventh':'SELECT x FROM t ORDER BY x,x,x,x,x,x,x,x,x,x,0 AND (SELECT missing);',
 'order_twenty_second':'SELECT x FROM t ORDER BY '+','.join(['x']*21+['0 AND (SELECT missing)'])+';',
 'order_collate':'SELECT x FROM t ORDER BY (0 AND (SELECT missing)) COLLATE BINARY;',
 'order_negative':'SELECT x FROM t ORDER BY -(0 AND (SELECT missing));',
 'order_outside':'SELECT x FROM t ORDER BY 2;',
 'check_scalar':'CREATE TABLE c(x CHECK(0 AND (SELECT 1)));',
 'check_exists':'CREATE TABLE c(x CHECK(0 AND EXISTS(SELECT 1)));',
 'check_in':'CREATE TABLE c(x CHECK(0 AND x IN (SELECT 1)));',
 'check_empty_in':'CREATE TABLE c(x CHECK((SELECT 1) IN ()));',
 'check_function_not_folded':'CREATE TABLE c(x CHECK(0 AND abs(x) IN (SELECT 1)));',
 'check_scalar_not_folded':'CREATE TABLE c(x CHECK((SELECT 1)));',
 'check_exists_not_folded':'CREATE TABLE c(x CHECK(EXISTS(SELECT 1)));',
 'function_not_folded':'SELECT 0 AND abs(-9223372036854775808);',
 'false_not_folded':'SELECT false AND (SELECT missing);',
 'insert':'INSERT INTO t VALUES(0 AND (SELECT missing));SELECT * FROM t ORDER BY x;',
 'update':'UPDATE t SET x=0 AND (SELECT missing);SELECT * FROM t;',
 'case':'SELECT CASE WHEN 0 AND (SELECT missing) THEN 1 ELSE 2 END;',
}
SETUP='CREATE TABLE t(x);INSERT INTO t VALUES(1),(2);'
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(SubqueryFolding,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
rng=random.Random(int(os.environ.get('SQLEANITE_SUBQUERY_FOLD_SEED','363001')))
for i in range(12):
 value=rng.randrange(-10000,10000)
 sql=f'SELECT (0 AND (SELECT absent_{abs(value)})), {value} + ((SELECT absent_{i}) IN ());'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(SubqueryFolding,'test_fresh_'+str(i)+'_'+suffix,case(sql,mode,SETUP))
if __name__=='__main__':unittest.main()
