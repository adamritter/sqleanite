#!/usr/bin/env python3
"""Actual NOCASE/RTRIM auxiliary index keys, predicates and physical files."""
import os,random,unittest
from test_check_add_column import case
class CollatedIndexes(unittest.TestCase):pass
BASE="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'A',1),(2,'b ',2),(3,'C',3),(4,NULL,4);"
OBSERVE='SELECT * FROM t ORDER BY id;PRAGMA index_list(t);PRAGMA index_xinfo(ci);'
Q={
 'declared_full_create':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE'),'CREATE INDEX ci ON t(v);'+OBSERVE),
 'declared_full_open':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE')+'CREATE INDEX ci ON t(v);',OBSERVE),
 'declared_full_update':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE')+'CREATE INDEX ci ON t(v);',"UPDATE t SET v='Z' WHERE id=1;"+OBSERVE),
 'declared_full_unique':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE'),"CREATE UNIQUE INDEX ci ON t(v);INSERT INTO t VALUES(5,'a',5);"),
 'declared_full_ignore':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE'),"CREATE UNIQUE INDEX ci ON t(v);INSERT OR IGNORE INTO t VALUES(5,'a',5);"+OBSERVE),
 'declared_full_replace':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE'),"CREATE UNIQUE INDEX ci ON t(v);INSERT OR REPLACE INTO t VALUES(5,'a',5);"+OBSERVE),
 'unrelated_declaration':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE'),'CREATE INDEX ci ON t(n);'+OBSERVE),
 'outer_unary':(BASE,'CREATE INDEX ci ON t(+(v COLLATE NOCASE));'+OBSERVE),
 'inner_concat':(BASE,'CREATE INDEX ci ON t((v COLLATE NOCASE)||n);'+OBSERVE),
 'mixed_values':("CREATE TABLE t(id INTEGER PRIMARY KEY,v,n);INSERT INTO t VALUES(1,NULL,1),(2,2,2),(3,1.5,3),(4,'A',4),(5,'a',5),(6,x'41',6);",'CREATE INDEX ci ON t(v COLLATE NOCASE);'+OBSERVE),
 'nul_nocase':(BASE,"CREATE INDEX ci ON t(v COLLATE NOCASE);INSERT INTO t VALUES(5,'A'||char(0)||'z',5),(6,'a'||char(0)||'Z',6);"+OBSERVE),
 'rtrim_spaces':(BASE,"CREATE INDEX ci ON t(v COLLATE RTRIM);INSERT INTO t VALUES(5,'A ',5),(6,'A  ',6);"+OBSERVE),
 'create_duplicate':(BASE+"INSERT INTO t VALUES(5,'a',5);",'CREATE UNIQUE INDEX ci ON t(v COLLATE NOCASE);'),
 'create_if_exists':(BASE+'CREATE INDEX ci ON t(v COLLATE NOCASE);','CREATE INDEX IF NOT EXISTS ci ON t(absent(v) COLLATE missing);'+OBSERVE),
 'nocase_create':(BASE,'CREATE INDEX ci ON t(v COLLATE NOCASE);'+OBSERVE),
 'rtrim_create':(BASE,'CREATE INDEX ci ON t(v COLLATE RTRIM);'+OBSERVE),
 'nocase_open':(BASE+'CREATE INDEX ci ON t(v COLLATE NOCASE);',OBSERVE),
 'rtrim_open':(BASE+'CREATE INDEX ci ON t(v COLLATE RTRIM);',OBSERVE),
 'expression':(BASE,'CREATE INDEX ci ON t((v||n) COLLATE NOCASE);'+OBSERVE),
 'expression_inner':(BASE,'CREATE INDEX ci ON t(lower(v COLLATE NOCASE));'+OBSERVE),
 'binary_override':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE'),'CREATE INDEX ci ON t(v COLLATE BINARY) WHERE n>0;'+OBSERVE),
 'declared_partial':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE'),'CREATE INDEX ci ON t(v) WHERE n>0;'+OBSERVE),
 'predicate_declared':(BASE.replace('v TEXT','v TEXT COLLATE NOCASE'),"CREATE INDEX ci ON t(n) WHERE v='a';"+OBSERVE),
 'unique_nocase':(BASE,"CREATE UNIQUE INDEX ci ON t(v COLLATE NOCASE);INSERT INTO t VALUES(5,'a',5);"),
 'ignore_nocase':(BASE,"CREATE UNIQUE INDEX ci ON t(v COLLATE NOCASE);INSERT OR IGNORE INTO t VALUES(5,'a',5);"+OBSERVE),
 'replace_nocase':(BASE,"CREATE UNIQUE INDEX ci ON t(v COLLATE NOCASE);INSERT OR REPLACE INTO t VALUES(5,'a',5);"+OBSERVE),
 'unique_rtrim':(BASE,"CREATE UNIQUE INDEX ci ON t(v COLLATE RTRIM);INSERT INTO t VALUES(5,'b',5);"),
 'ignore_rtrim':(BASE,"CREATE UNIQUE INDEX ci ON t(v COLLATE RTRIM);INSERT OR IGNORE INTO t VALUES(5,'b',5);"+OBSERVE),
 'replace_rtrim':(BASE,"CREATE UNIQUE INDEX ci ON t(v COLLATE RTRIM);INSERT OR REPLACE INTO t VALUES(5,'b',5);"+OBSERVE),
 'update_nocase':(BASE+'CREATE INDEX ci ON t(v COLLATE NOCASE);',"UPDATE t SET v='changed' WHERE id=1;"+OBSERVE),
 'virtual':(BASE+'CREATE INDEX ci ON t(v COLLATE NOCASE);',"SELECT * FROM pragma_index_xinfo('ci');"),
 'unused_unknown_lower':(BASE,'CREATE INDEX ci ON t(lower(v COLLATE missing));'+OBSERVE),
 'unused_unknown_concat':(BASE,"CREATE INDEX ci ON t((v COLLATE missing)||'x');"+OBSERVE),
 'unused_unknown_case':(BASE,'CREATE INDEX ci ON t(CASE WHEN 1 THEN v ELSE v COLLATE missing END);'+OBSERVE),
 'unused_unknown_min':(BASE,'CREATE INDEX ci ON t(min(v,v COLLATE missing));'+OBSERVE),
 'used_unknown_min':(BASE,'CREATE INDEX ci ON t(min(v COLLATE missing,v));'),
 'used_unknown_comparison':(BASE,"CREATE INDEX ci ON t((v COLLATE missing)='a');"),
 'unknown_collation':(BASE,'CREATE INDEX ci ON t(v COLLATE missing);'),
}
rng=random.Random(int(os.environ.get('SQLEANITE_COLLATED_INDEX_SEED','1834001')))
for i in range(12):
 amount=rng.randrange(10,900)
 Q[f'fresh_{i}']=(BASE+'CREATE INDEX ci ON t((v||n) COLLATE NOCASE);',f"UPDATE t SET v='Z{amount}' WHERE id={i%4+1};"+OBSERVE)
for name,(setup,sql) in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(CollatedIndexes,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
