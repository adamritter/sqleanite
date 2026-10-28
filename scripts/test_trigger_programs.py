#!/usr/bin/env python3
"""Nested AFTER programs, inherited conflict policy and SELECT inputs."""
import os
import random
import unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class TriggerPrograms(unittest.TestCase):pass
QUERIES={
 'insert_select_body':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log SELECT new.id+10,old.v||new.v,new.n;END;UPDATE t SET n=n+10 WHERE id<3;"+TAIL,
 'insert_select_source':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log SELECT id+10,new.v,n FROM t WHERE id=new.id;END;UPDATE t SET n=n+10 WHERE id<3;"+TAIL,
 'insert_select_empty':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log SELECT new.id+10,old.v,new.n WHERE 0;END;UPDATE t SET n=n+10;"+TAIL,
 'insert_select_zero_prepare':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log SELECT new.missing,0,0;END;UPDATE t SET n=n+10 WHERE 0;",
 'insert_values_subquery':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(new.id+10,(SELECT old.v||new.v),(SELECT n FROM t WHERE id=new.id));END;UPDATE t SET n=n+10 WHERE id<3;"+TAIL,
 'update_subquery':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET v=(SELECT old.v||new.v),n=(SELECT new.n) WHERE id=1;END;UPDATE t SET n=n+10 WHERE id<3;"+TAIL,
 'update_where_subquery':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1 WHERE EXISTS(SELECT 1 WHERE new.n>old.n);END;UPDATE t SET n=n+10;"+TAIL,
 'delete_where_subquery':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN DELETE FROM log WHERE EXISTS(SELECT 1 WHERE new.id=2);END;UPDATE t SET n=n+10;"+TAIL,
 'update_correlated_local':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=(SELECT log.n+new.n),v=(SELECT t.v FROM t WHERE t.id=new.id) WHERE id=1;END;UPDATE t SET n=n+10 WHERE id<3;"+TAIL,
 'outer_insert_select':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN UPDATE log SET v=v||new.id,n=n+new.n;END;INSERT INTO t SELECT id+10,v||'x',n+20 FROM t WHERE id<3 RETURNING id,n;"+TAIL,
 'outer_insert_values_select':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN UPDATE log SET v=v||new.id,n=n+new.n;END;INSERT INTO t SELECT * FROM (VALUES(8,'x',8),(9,'y',9)) RETURNING id,n;"+TAIL,
 'outer_insert_select_empty':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t SELECT 8,'x',8 WHERE 0;"+TAIL,
 'outer_insert_select_prepare':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN SELECT new.missing;END;INSERT INTO t SELECT 8,'x',8 WHERE 0;",
 'outer_ignore_body_conflict':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(1,new.v,new.n);END;UPDATE OR IGNORE t SET n=n+10;"+TAIL,
 'outer_replace_body_conflict':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(1,new.v,new.n);END;UPDATE OR REPLACE t SET n=n+10;"+TAIL,
 'outer_ignore_overrides_replace':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT OR REPLACE INTO log VALUES(1,new.v,new.n);END;UPDATE OR IGNORE t SET n=n+10;"+TAIL,
 'body_ignore_default_outer':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT OR IGNORE INTO log VALUES(1,new.v,new.n);END;UPDATE t SET n=n+10;"+TAIL,
 'body_replace_default_outer':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT OR REPLACE INTO log VALUES(1,new.v,new.n);END;UPDATE t SET n=n+10;"+TAIL,
 'nested_invalid_empty':"CREATE TRIGGER first AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1 WHERE 0;END;CREATE TRIGGER second AFTER UPDATE ON log BEGIN SELECT new.missing;END;UPDATE t SET n=n+10 WHERE 0;",
 'nested_invalid_false_when':"CREATE TRIGGER first AFTER UPDATE ON t WHEN 0 BEGIN UPDATE log SET n=n+1;END;CREATE TRIGGER second AFTER UPDATE ON log BEGIN SELECT new.missing;END;UPDATE t SET n=n+10;",
 'body_insert_default':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log DEFAULT VALUES;END;UPDATE t SET n=n+10 WHERE id=2;"+TAIL,
 'scalar_local_shadow':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=(SELECT new.n FROM t AS new WHERE new.id=1),v=(SELECT new.v);END;UPDATE t SET n=n+10 WHERE id=2;"+TAIL,
 'insert_select_affinity':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log SELECT new.id+10,new.n,old.v;END;UPDATE t SET n=n+10 WHERE id<3;"+TAIL,
 'when_correlated':"CREATE TRIGGER tr AFTER UPDATE ON t WHEN EXISTS(SELECT 1 FROM log WHERE log.n<new.n) BEGIN UPDATE log SET n=new.n,v=old.v;END;UPDATE t SET n=n+10;"+TAIL,
}
QUERIES.update({
 'outer_streaming_register':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN UPDATE log SET n=new.n,v=new.v WHERE id=1;END;INSERT INTO t SELECT * FROM (VALUES(4,'d',last_insert_rowid()),(5,'e',last_insert_rowid())) RETURNING id,n;"+TAIL,
 'body_streaming_register':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log SELECT * FROM (VALUES(10,'a',last_insert_rowid()),(11,'b',last_insert_rowid()));END;UPDATE t SET n=n+1 WHERE id=1;"+TAIL,
 'sorted_select_register':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN UPDATE log SET n=new.n WHERE id=1;END;INSERT INTO t SELECT * FROM (VALUES(4,'d',last_insert_rowid()),(5,'e',last_insert_rowid())) ORDER BY 1 DESC RETURNING id,n;"+TAIL,
 'body_values_register':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(10,'a',(SELECT last_insert_rowid())),(11,'b',(SELECT last_insert_rowid()));END;UPDATE t SET n=n+1 WHERE id=1;"+TAIL,
})
QUERIES.update({
 'body_triggered_register':"CREATE TRIGGER outer_tr AFTER UPDATE ON t BEGIN INSERT INTO log SELECT * FROM (VALUES(10,'a',last_insert_rowid()),(11,'b',last_insert_rowid()));END;CREATE TRIGGER inner_tr AFTER INSERT ON log BEGIN UPDATE t SET v='nested' WHERE id=2;END;UPDATE t SET n=n+1 WHERE id=1;"+TAIL,
})
rng=random.Random(int(os.environ.get('SQLEANITE_TRIGGER_PROGRAM_SEED','1312001')))
for i in range(16):
 delta=rng.randrange(-30,31)
 maximum=rng.randrange(1,4)
 QUERIES[f'fresh_{i}']=f"CREATE TRIGGER tr AFTER UPDATE OF n ON t WHEN new.n-old.n=({delta}) BEGIN UPDATE log SET n=(SELECT log.n+new.n-old.n),v=old.v||'/'||new.v WHERE id=1;INSERT INTO log SELECT new.id+10,old.v||'/'||new.v,(SELECT n FROM log WHERE id=1);END;UPDATE t SET n=n+({delta}),v=v||'x' WHERE id<={maximum};"+TAIL
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(TriggerPrograms,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
if __name__=='__main__':unittest.main()
