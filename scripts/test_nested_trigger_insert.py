#!/usr/bin/env python3
"""Captured trigger INSERT inputs share actual lexical scopes and row registers."""
import os,random,unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class NestedInsert(unittest.TestCase):pass
Q={
 'mixed_key':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES((SELECT max(id) FROM t)+total_changes()+10,new.v,4);END;UPDATE log SET v='d';"+TAIL,
 'discard_ordinary':"CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t(id,v,n,n) VALUES(4,(SELECT new.v),4,abs(-9223372036854775808));END;UPDATE log SET v='d';"+TAIL,
 'discard_rowid':"CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t(id,rowid,v,n) VALUES(abs(-9223372036854775808),(SELECT 4),new.v,4);END;UPDATE log SET v='d';"+TAIL,
 'multi_materialized':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES(4,(SELECT new.v),total_changes()),(5,(SELECT new.v),total_changes());END;UPDATE log SET v='d';"+TAIL,
 'captured_subtype':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=subtype(new.v);END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES(4,(SELECT json('[1]')),4);END;UPDATE log SET v='d';"+TAIL,
 'direct_tag_with_capture':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=subtype(new.v);END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES((SELECT 4),json('[1]'),4);END;UPDATE log SET v='d';"+TAIL,
 'scalar_after_mutation':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN DELETE FROM t WHERE id=3;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES((SELECT max(id)+10 FROM t),new.v,4);END;UPDATE log SET v='d';"+TAIL,
}
Q.update({
 'single_after_tag':"CREATE TRIGGER b AFTER INSERT ON t BEGIN UPDATE log SET n=subtype(new.v);END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES((SELECT 4),json('[1]'),4);END;UPDATE log SET v='d';"+TAIL,
 'no_target_multi_counter':"CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES(4,(SELECT new.v),total_changes()),(5,(SELECT new.v),total_changes());END;UPDATE log SET v='d';"+TAIL,
 'no_target_multi_rowid':"CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES(4,(SELECT new.v),last_insert_rowid()),(5,(SELECT new.v),last_insert_rowid());END;UPDATE log SET v='d';"+TAIL,
 'multi_discarded_error':"CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t(id,v,n,n) VALUES(4,(SELECT new.v),4,abs(-9223372036854775808)),(5,'e',5,5);END;UPDATE log SET v='d';",
 'physical_order':"CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t(n,v,id) VALUES(abs(-9223372036854775808),json('bad'),(SELECT 4));END;UPDATE log SET v='d';",
 'double_capture':"CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES(4,(SELECT (SELECT new.v)),(SELECT (SELECT new.n)));END;UPDATE log SET v='d',n=8;"+TAIL,
 'correlated_local_new':"CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES(4,(SELECT new.v FROM t AS new WHERE id=2),new.n);END;UPDATE log SET v='d',n=8;"+TAIL,
 'old_new_input':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET v=new.v,n=new.n;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES(4,(SELECT old.v||'/'||new.v),(SELECT old.n+new.n));END;UPDATE log SET v='d',n=8;"+TAIL,
 'insert_select_input':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t SELECT id+10,(SELECT new.v),n+new.n FROM t WHERE id<3;END;UPDATE log SET v='d',n=8;"+TAIL,
 'ignore_input':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT OR IGNORE INTO t VALUES((SELECT 1),new.v,new.n);END;UPDATE log SET v='d',n=8;"+TAIL,
 'replace_input':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT OR REPLACE INTO t VALUES((SELECT 1),new.v,new.n);END;UPDATE log SET v='d',n=8;"+TAIL,
 'nested_preparation_empty':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN SELECT new.missing;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES((SELECT 4),new.v,new.n);END;UPDATE log SET v='d' WHERE 0;",
 'own_multi_materialization':"CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO t VALUES(new.id+10,(SELECT new.v),total_changes()),(new.id+20,(SELECT new.v),total_changes());END;INSERT INTO t VALUES(4,'d',4);"+TAIL,
 'parameter_isolation':"CREATE TRIGGER b BEFORE DELETE ON t BEGIN SELECT new.id;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN DELETE FROM t WHERE id=1;END;UPDATE log SET v='d';",
})
for name,expr in {
 'cached_inner_counter':"(SELECT max(id)+total_changes() FROM t)+10",
 'cached_parameter_counter':"(SELECT new.n+total_changes())+10",
 'cached_table_parameter_counter':"(SELECT max(id)+new.n+total_changes() FROM t)+10",
 'live_surrounding_counter':"(SELECT max(id) FROM t)+total_changes()+10",
}.items():
 Q[name]="CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;DELETE FROM t WHERE id=3;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES("+expr+",new.v,4);END;UPDATE log SET v='d',n=5;"+TAIL
rng=random.Random(int(os.environ.get('SQLEANITE_NESTED_INSERT_SEED','1813001')))
for i in range(12):
 key=rng.randrange(4,100);delta=rng.randrange(-40,41)
 Q[f'fresh_{i}']=f"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t VALUES({key},(SELECT old.v||'/'||new.v),(SELECT new.n)+({delta}));END;UPDATE log SET v='fresh',n={delta};"+TAIL
for name,q in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(NestedInsert,'test_'+name+'_'+suffix,case(q,mode,SETUP))
if __name__=='__main__':unittest.main()
