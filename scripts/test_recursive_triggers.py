#!/usr/bin/env python3
"""Connection recursion controls, actual frame depth and event recursion."""
import os,random,unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class RecursiveTriggers(unittest.TestCase):pass
Q={
 'default':'PRAGMA recursive_triggers;',
 'on':'PRAGMA recursive_triggers=ON;PRAGMA recursive_triggers;',
 'off':'PRAGMA recursive_triggers=OFF;PRAGMA recursive_triggers;',
 'toggle':'PRAGMA recursive_triggers=ON;PRAGMA recursive_triggers=OFF;PRAGMA recursive_triggers;',
 'numeric':'PRAGMA recursive_triggers=257;PRAGMA recursive_triggers;PRAGMA recursive_triggers=256;PRAGMA recursive_triggers;',
 'quoted':"PRAGMA recursive_triggers='yes';PRAGMA recursive_triggers;PRAGMA recursive_triggers='unknown';PRAGMA recursive_triggers;",
 'temp':'PRAGMA temp.recursive_triggers=ON;PRAGMA main.recursive_triggers;',
 'unknown_schema':'PRAGMA missing.recursive_triggers=ON;',
 'tvf':'PRAGMA recursive_triggers=ON;SELECT * FROM pragma_recursive_triggers;',
 'tvf_args':"SELECT * FROM pragma_recursive_triggers('t');",
 'tvf_direct_only':'CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT * FROM pragma_recursive_triggers;END;UPDATE t SET n=n+1 WHERE 0;',
 'transaction':'BEGIN;PRAGMA recursive_triggers=ON;ROLLBACK;PRAGMA recursive_triggers;',
 'savepoint':'SAVEPOINT s;PRAGMA recursive_triggers=ON;ROLLBACK TO s;RELEASE s;PRAGMA recursive_triggers;',
 'after_update_on':"PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER UPDATE ON t WHEN new.n<5 BEGIN UPDATE log SET v=v||new.n,n=n+1;UPDATE t SET n=n+1 WHERE id=new.id;END;UPDATE t SET n=2 WHERE id=1;"+TAIL,
 'after_update_off':"PRAGMA recursive_triggers=OFF;CREATE TRIGGER a AFTER UPDATE ON t WHEN new.n<5 BEGIN UPDATE log SET v=v||new.n,n=n+1;UPDATE t SET n=n+1 WHERE id=new.id;END;UPDATE t SET n=2 WHERE id=1;"+TAIL,
 'before_update_on':"PRAGMA recursive_triggers=ON;CREATE TRIGGER b BEFORE UPDATE ON t WHEN new.n<5 BEGIN UPDATE log SET v=v||new.n,n=n+1;UPDATE t SET n=new.n+1 WHERE id=old.id;END;UPDATE t SET n=2 WHERE id=1 RETURNING n;"+TAIL,
 'insert_on':"PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER INSERT ON t WHEN new.n<3 BEGIN INSERT INTO t VALUES(new.id+10,new.v,new.n+1);END;INSERT INTO t VALUES(4,'d',1);"+TAIL,
 'delete_on':"PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER DELETE ON t WHEN old.id>1 BEGIN DELETE FROM t WHERE id=old.id-1;END;DELETE FROM t WHERE id=3;"+TAIL,
 'mutual_on':"PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER UPDATE ON t WHEN new.n<5 BEGIN UPDATE log SET n=new.n;END;CREATE TRIGGER b AFTER UPDATE ON log BEGIN UPDATE t SET n=new.n+1 WHERE id=1;END;UPDATE t SET n=2 WHERE id=1;"+TAIL,
 'replace_delete_on':"PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER DELETE ON t BEGIN UPDATE log SET v=v||old.id,n=n+1;END;INSERT OR REPLACE INTO t VALUES(2,'replacement',9);"+TAIL,
 'replace_delete_off':"PRAGMA recursive_triggers=OFF;CREATE TRIGGER a AFTER DELETE ON t BEGIN UPDATE log SET v=v||old.id,n=n+1;END;INSERT OR REPLACE INTO t VALUES(2,'replacement',9);"+TAIL,
 'update_replace_on':"PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER DELETE ON t BEGIN UPDATE log SET v=v||old.id,n=n+1;END;UPDATE OR REPLACE t SET id=2,n=9 WHERE id=3;"+TAIL,
}
Q.update({
 'returning_before_counter':"PRAGMA recursive_triggers=ON;CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES(4,'d',4) RETURNING id,total_changes(),changes(),last_insert_rowid();"+TAIL,
 'returning_after_counter':"PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES(4,'d',4) RETURNING id,total_changes(),changes(),last_insert_rowid();"+TAIL,
 'returning_select_counter':"PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t SELECT 4,'d',4 RETURNING id,total_changes(),changes(),last_insert_rowid();"+TAIL,
})
rng=random.Random(int(os.environ.get('SQLEANITE_RECURSIVE_TRIGGER_SEED','1815001')))
for i in range(12):
 limit=rng.randrange(3,12);start=rng.randrange(-3,2)
 Q[f'fresh_{i}']=f"PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER UPDATE ON t WHEN new.n<{limit} BEGIN UPDATE log SET n=n+1;UPDATE t SET n=n+1 WHERE id=new.id;END;UPDATE t SET n={start} WHERE id=1;"+TAIL
for name,q in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(RecursiveTriggers,'test_'+name+'_'+suffix,case(q,mode,SETUP))
DEPTH_SETUP='CREATE TABLE t(id INTEGER PRIMARY KEY,n);INSERT INTO t VALUES(1,0);CREATE TABLE log(n);'
for limit in [1000,1001]:
 sql=f'PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(new.n);UPDATE t SET n=n+1 WHERE n<{limit};END;UPDATE t SET n=1;SELECT n FROM t;SELECT count(*) FROM log;SELECT changes(),total_changes();'
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(RecursiveTriggers,f'test_depth_{limit}_'+suffix,case(sql,mode,DEPTH_SETUP))
EXTRA={
 'replace_phases':(SETUP,"PRAGMA recursive_triggers=ON;CREATE TRIGGER b BEFORE DELETE ON t BEGIN UPDATE log SET v=v||'b'||old.id,n=n+1;END;CREATE TRIGGER d AFTER DELETE ON t BEGIN UPDATE log SET v=v||'d'||old.id,n=n+1;END;CREATE TRIGGER a AFTER INSERT ON t BEGIN UPDATE log SET v=v||'i'||new.id,n=n+1;END;INSERT OR REPLACE INTO t VALUES(2,'replacement',9) RETURNING id,v,n,total_changes();"+TAIL),
 'default_replace':("CREATE TABLE t(id INTEGER PRIMARY KEY ON CONFLICT REPLACE,v,n);INSERT INTO t VALUES(1,'a',1),(2,'b',2);CREATE TABLE log(id INTEGER PRIMARY KEY,v,n);INSERT INTO log VALUES(1,'',0);","PRAGMA recursive_triggers=ON;CREATE TRIGGER d AFTER DELETE ON t BEGIN UPDATE log SET v=v||old.id,n=n+1;END;INSERT INTO t VALUES(2,'new',9);"+TAIL),
 'two_unique_order':("CREATE TABLE t(id INTEGER PRIMARY KEY,v UNIQUE,n UNIQUE);INSERT INTO t VALUES(1,'a',1),(2,'b',2),(3,'c',3);CREATE TABLE log(id INTEGER PRIMARY KEY,v,n);INSERT INTO log VALUES(1,'',0);","PRAGMA recursive_triggers=ON;CREATE TRIGGER d AFTER DELETE ON t BEGIN UPDATE log SET v=v||old.id,n=n+1;END;INSERT OR REPLACE INTO t VALUES(4,'a',2);"+TAIL),
 'three_victim_order':("CREATE TABLE t(id INTEGER PRIMARY KEY,v UNIQUE,n UNIQUE);INSERT INTO t VALUES(1,'a',1),(2,'b',2),(3,'c',3);CREATE TABLE log(id INTEGER PRIMARY KEY,v,n);INSERT INTO log VALUES(1,'',0);","PRAGMA recursive_triggers=ON;CREATE TRIGGER d AFTER DELETE ON t BEGIN UPDATE log SET v=v||old.id,n=n+1;END;INSERT OR REPLACE INTO t VALUES(1,'c',2);"+TAIL),
 'automatic_key_frozen':("CREATE TABLE t(id INTEGER PRIMARY KEY,v UNIQUE,n);INSERT INTO t VALUES(1,'a',1),(2,'b',2),(3,'c',3);CREATE TABLE log(id INTEGER PRIMARY KEY,v,n);INSERT INTO log VALUES(1,'',0);","PRAGMA recursive_triggers=ON;CREATE TRIGGER d AFTER DELETE ON t BEGIN INSERT INTO t VALUES(100,'body',100);UPDATE log SET n=old.id;END;INSERT OR REPLACE INTO t(v,n) VALUES('b',9) RETURNING id;"+TAIL),
 'update_rhs_frozen':(SETUP,"PRAGMA recursive_triggers=ON;CREATE TRIGGER d AFTER DELETE ON t BEGIN UPDATE log SET n=n+1;END;UPDATE OR REPLACE t SET id=2,n=total_changes() WHERE id=3 RETURNING n,total_changes();"+TAIL),
 'update_unassigned_frozen':(SETUP,"PRAGMA recursive_triggers=ON;CREATE TRIGGER d AFTER DELETE ON t BEGIN UPDATE t SET v='body' WHERE id=3;END;UPDATE OR REPLACE t SET id=2,n=9 WHERE id=3 RETURNING *;"+TAIL),
 'returning_error_priority':(SETUP,"PRAGMA recursive_triggers=ON;CREATE TRIGGER d BEFORE DELETE ON t BEGIN SELECT json('bad');END;INSERT OR REPLACE INTO t VALUES(2,'replacement',9) RETURNING abs(-9223372036854775808);"),
 'implicit_prepare_empty':(SETUP,"PRAGMA recursive_triggers=ON;CREATE TRIGGER d AFTER DELETE ON t BEGIN SELECT old.missing;END;INSERT OR REPLACE INTO t SELECT 4,'d',4 WHERE 0;"),
 'delete_old_fixed':(SETUP,"PRAGMA recursive_triggers=ON;CREATE TRIGGER b BEFORE DELETE ON t BEGIN UPDATE t SET n=40 WHERE id=old.id;END;CREATE TRIGGER d AFTER DELETE ON t BEGIN UPDATE log SET n=old.n;END;INSERT OR REPLACE INTO t VALUES(2,'replacement',9);"+TAIL),
}
FK_SETUP='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1),(2);CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));INSERT INTO c VALUES(1,2);CREATE TABLE log(n);INSERT INTO log VALUES(0);'
EXTRA['fk_replace_parent']=(FK_SETUP,'PRAGMA recursive_triggers=ON;PRAGMA foreign_keys=ON;CREATE TRIGGER d AFTER DELETE ON p BEGIN UPDATE log SET n=n+1;END;INSERT OR REPLACE INTO p VALUES(2);SELECT * FROM p;SELECT * FROM c;SELECT * FROM log;SELECT changes(),total_changes(),last_insert_rowid();')
for name,(setup,q) in EXTRA.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(RecursiveTriggers,'test_'+name+'_'+suffix,case(q,mode,setup))
if __name__=='__main__':unittest.main()
