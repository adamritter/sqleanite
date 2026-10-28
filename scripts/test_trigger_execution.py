#!/usr/bin/env python3
"""Persistent row-trigger execution regressions against pinned SQLite.
Each scenario is separately selectable; unsupported semantics are real failures.
"""
import os
import random
import unittest
from test_check_add_column import case
class TriggerExecution(unittest.TestCase):pass
SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'a',1),(2,'b',2),(3,'c',3);CREATE TABLE log(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO log VALUES(1,'',0);"
TAIL='SELECT id,v,n FROM t ORDER BY id;SELECT id,v,n FROM log ORDER BY id;SELECT changes(),total_changes(),last_insert_rowid();'
QUERIES={
 'after_update':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET v=new.v,n=n+new.n-old.n WHERE id=1; END;UPDATE t SET n=n+10,v=v||'!' WHERE id=2;"+TAIL,
 'after_insert':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN UPDATE log SET v=new.v,n=n+new.n WHERE id=1; END;INSERT INTO t VALUES(4,'d',4);"+TAIL,
 'after_delete':"CREATE TRIGGER tr AFTER DELETE ON t BEGIN UPDATE log SET v=old.v,n=n+old.n WHERE id=1; END;DELETE FROM t WHERE id=2;"+TAIL,
 'self_update':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE t SET v='triggered' WHERE id=new.id; END;UPDATE t SET n=n+1 WHERE id=1;"+TAIL,
 'multi_update':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET v=v||new.id,n=n+new.n WHERE id=1; END;UPDATE t SET n=n+10 WHERE id<3;"+TAIL,
 'multi_delete':"CREATE TRIGGER tr AFTER DELETE ON t BEGIN UPDATE log SET v=v||old.id,n=n+old.n WHERE id=1; END;DELETE FROM t WHERE id<3;"+TAIL,
 'multi_insert':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN UPDATE log SET v=v||new.id,n=n+new.n WHERE id=1; END;INSERT INTO t VALUES(4,'d',4),(5,'e',5);"+TAIL,
 'update_of_match':"CREATE TRIGGER tr AFTER UPDATE OF n ON t BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE t SET n=n WHERE id=2;"+TAIL,
 'update_of_miss':"CREATE TRIGGER tr AFTER UPDATE OF n ON t BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE t SET v='x' WHERE id=2;"+TAIL,
 'update_of_unknown':"CREATE TRIGGER tr AFTER UPDATE OF missing ON t BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE t SET n=8 WHERE id=2;"+TAIL,
 'when_true':"CREATE TRIGGER tr AFTER UPDATE ON t WHEN new.n>old.n BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE t SET n=n+1;"+TAIL,
 'when_false':"CREATE TRIGGER tr AFTER UPDATE ON t WHEN new.n<old.n BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE t SET n=n+1;"+TAIL,
 'unrelated_table':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE log SET n=9 WHERE id=1;"+TAIL,
 'zero_rows':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE t SET n=9 WHERE 0;"+TAIL,
 'noop_update':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE t SET n=n WHERE id=2;"+TAIL,
 'body_insert':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(new.id+10,old.v||new.v,new.n); END;UPDATE t SET n=n+10 WHERE id<3;"+TAIL,
 'body_delete':"CREATE TRIGGER tr AFTER DELETE ON t BEGIN DELETE FROM log WHERE id=old.id; END;DELETE FROM t WHERE id=1;"+TAIL,
 'body_select':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN SELECT new.id,old.v; END;UPDATE t SET n=n+1 WHERE id=1;"+TAIL,
 'program_order':"CREATE TRIGGER first AFTER UPDATE ON t BEGIN UPDATE log SET v=v||'first' WHERE id=1; END;CREATE TRIGGER second AFTER UPDATE ON t BEGIN UPDATE log SET v=v||'second' WHERE id=1; END;UPDATE t SET n=n+1 WHERE id=1;"+TAIL,
 'old_new_fixed':"CREATE TRIGGER first AFTER UPDATE ON t BEGIN UPDATE log SET v=v||old.v||new.v WHERE id=1; END;CREATE TRIGGER second AFTER UPDATE ON t BEGIN UPDATE t SET v='changed' WHERE id=new.id; END;UPDATE t SET v='original' WHERE id=1;"+TAIL,
 'insert_ignore':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN UPDATE log SET n=n+1 WHERE id=1; END;INSERT OR IGNORE INTO t VALUES(1,'ignored',7);"+TAIL,
 'update_ignore':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE OR IGNORE t SET id=1 WHERE id=2;"+TAIL,
 'returning_update':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE t SET n=100 WHERE id=new.id; END;UPDATE t SET n=n+10 WHERE id<3 RETURNING id,n;"+TAIL,
 'returning_insert':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN UPDATE t SET n=100 WHERE id=new.id; END;INSERT INTO t VALUES(4,'d',4) RETURNING id,n;"+TAIL,
 'returning_delete':"CREATE TRIGGER tr AFTER DELETE ON t BEGIN UPDATE log SET n=n+old.n WHERE id=1; END;DELETE FROM t WHERE id<3 RETURNING id,n;"+TAIL,
 'counter_frame':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN INSERT INTO log VALUES(new.id+10,printf('%d/%d/%d',changes(),total_changes(),last_insert_rowid()),0);UPDATE log SET n=changes() WHERE id=new.id+10; END;INSERT INTO t VALUES(4,'d',4),(5,'e',5);"+TAIL,
 'rowid_change':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET v=old.id||'/'||new.id WHERE id=1; END;UPDATE t SET id=20 WHERE id=2;"+TAIL,
 'indirect_delete':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN DELETE FROM t WHERE id=new.id+1; END;UPDATE t SET n=n+10;"+TAIL,
 'selected_before_mutation':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE t SET n=99 WHERE id=new.id+1; END;UPDATE t SET n=n+10 WHERE n<3;"+TAIL,
 'body_error_atomic':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(1,'conflict',0); END;UPDATE t SET n=n+10;",
 'prepare_missing_even_empty':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN SELECT new.missing; END;UPDATE t SET n=9 WHERE 0;",
 'when_zero_still_prepare':"CREATE TRIGGER tr AFTER UPDATE ON t WHEN 0 BEGIN SELECT absent(new.id); END;UPDATE t SET n=9;",
}
QUERIES.update({
 'null_images':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET v=coalesce(old.v,'old-null')||coalesce(new.v,'new-null'),n=new.n WHERE id=1; END;UPDATE t SET v=NULL,n=NULL WHERE id=2;"+TAIL,
 'mixed_case':"CREATE TRIGGER Tr AFTER UPDATE OF N ON T BEGIN UPDATE LOG SET v=NeW.v,n=OLD.n WHERE id=1; END;UPDATE t SET n=10 WHERE id=2;"+TAIL,
 'negative_rowids':"INSERT INTO t VALUES(-4,'x',4),(-2,'y',2);CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET v=v||new.id||',' WHERE id=1; END;UPDATE t SET n=n+1;"+TAIL,
 'body_insert_register':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN INSERT INTO log VALUES(new.id+10,'body',last_insert_rowid());UPDATE log SET n=last_insert_rowid() WHERE id=1; END;INSERT INTO t VALUES(5,'e',5),(6,'f',6);"+TAIL,
 'outer_counters_fixed':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1 WHERE id=1; END;UPDATE t SET n=changes()+total_changes() RETURNING id,n,changes(),total_changes();"+TAIL,
 'rowid_replace':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET v=old.id||'/'||new.id,n=n+1 WHERE id=1; END;UPDATE OR REPLACE t SET id=1 WHERE id=2 RETURNING id,v,n;"+TAIL,
 'replace_event':"CREATE TRIGGER ins AFTER INSERT ON t BEGIN UPDATE log SET v=v||'i',n=n+1 WHERE id=1; END;CREATE TRIGGER del AFTER DELETE ON t BEGIN UPDATE log SET v=v||'d',n=n+1 WHERE id=1; END;INSERT OR REPLACE INTO t VALUES(2,'r',8);"+TAIL,
 'chained_events':"CREATE TRIGGER upd AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(new.id+10,new.v,new.n); END;CREATE TRIGGER ins AFTER INSERT ON log BEGIN UPDATE t SET v='chain' WHERE id=new.id-10; END;UPDATE t SET n=8 WHERE id=2;"+TAIL,
 'body_error_late':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(CASE new.id WHEN 3 THEN 1 ELSE new.id END,'new',0); END;UPDATE t SET n=n+10 WHERE id>=2;",
 'prepare_parent_column':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1; END;UPDATE t SET missing=9 WHERE 0;",
 'prepare_body_update':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET missing=new.n; END;UPDATE t SET n=9 WHERE 0;",
 'prepare_body_where':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN DELETE FROM log WHERE missing=new.n; END;UPDATE t SET n=9 WHERE 0;",
 'prepare_missing_old':"CREATE TRIGGER tr AFTER INSERT ON t BEGIN SELECT old.id; END;INSERT INTO t VALUES(4,'d',4);",
 'prepare_missing_new':"CREATE TRIGGER tr AFTER DELETE ON t BEGIN SELECT new.id; END;DELETE FROM t WHERE 0;",
 'local_alias_new':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET v=new.v,n=n+1 WHERE id=1;SELECT new.id FROM log AS new WHERE new.id=1; END;UPDATE t SET v='real' WHERE id=2;"+TAIL,
 'nested_select':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN SELECT (SELECT old.id+new.id),EXISTS(SELECT 1 WHERE new.n>old.n);END;UPDATE t SET n=n+1;"+TAIL,
 'transaction_rollback':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=n+new.n; END;BEGIN;UPDATE t SET n=9;ROLLBACK;"+TAIL,
 'savepoint_restore':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=n+new.n; END;SAVEPOINT s;UPDATE t SET n=9;ROLLBACK TO s;RELEASE s;"+TAIL,
})
rng=random.Random(int(os.environ.get('SQLEANITE_TRIGGER_EXECUTION_SEED','1211001')))
for i in range(16):
 delta=rng.randrange(-40,41)
 low=rng.randrange(-1,5)
 high=rng.randrange(low,6)
 QUERIES[f'fresh_{i}']=f"CREATE TRIGGER tr AFTER UPDATE OF n ON t WHEN new.n<>old.n BEGIN UPDATE log SET v=v||old.id||':'||new.n||';',n=n+new.n-old.n WHERE id=1; END;UPDATE t SET n=n+({delta}) WHERE id>={low} AND id<={high} RETURNING id,n;"+TAIL
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(TriggerExecution,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
if __name__=='__main__':unittest.main()
