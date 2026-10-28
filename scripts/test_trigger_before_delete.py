#!/usr/bin/env python3
"""BEFORE DELETE timing, fixed OLD registers and preselected key semantics."""
import os,random,unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class BeforeDelete(unittest.TestCase):pass
QUERIES={
 'basic':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN UPDATE log SET n=n+old.n,v=v||old.v;END;DELETE FROM t WHERE id=2;"+TAIL,
 'before_after':"CREATE TRIGGER before_tr BEFORE DELETE ON t BEGIN UPDATE log SET v=v||'before',n=n+old.n;END;CREATE TRIGGER after_tr AFTER DELETE ON t BEGIN UPDATE log SET v=v||'after',n=n+old.n;END;DELETE FROM t WHERE id<3 RETURNING id,n;"+TAIL,
 'phase_order':"CREATE TRIGGER a1 AFTER DELETE ON t BEGIN UPDATE log SET v=v||'a1';END;CREATE TRIGGER b1 BEFORE DELETE ON t BEGIN UPDATE log SET v=v||'b1';END;CREATE TRIGGER a2 AFTER DELETE ON t BEGIN UPDATE log SET v=v||'a2';END;CREATE TRIGGER b2 BEFORE DELETE ON t BEGIN UPDATE log SET v=v||'b2';END;DELETE FROM t WHERE id=1;"+TAIL,
 'fixed_old_image':"CREATE TRIGGER before_tr BEFORE DELETE ON t BEGIN UPDATE t SET v='changed',n=100 WHERE id=old.id;END;CREATE TRIGGER after_tr AFTER DELETE ON t BEGIN INSERT INTO log VALUES(old.id+10,old.v,old.n);END;DELETE FROM t WHERE id<3 RETURNING id,v,n;"+TAIL,
 'delete_self':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN DELETE FROM t WHERE id=old.id;END;DELETE FROM t RETURNING id,n;"+TAIL,
 'move_self':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN UPDATE t SET id=id+10 WHERE id=old.id;END;DELETE FROM t RETURNING id,n;"+TAIL,
 'delete_next':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN DELETE FROM t WHERE id=old.id+1;END;DELETE FROM t RETURNING id,n;"+TAIL,
 'update_next':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN UPDATE t SET n=99 WHERE id=old.id+1;END;DELETE FROM t WHERE n<3 RETURNING id,n;"+TAIL,
 'when_false':"CREATE TRIGGER tr BEFORE DELETE ON t WHEN 0 BEGIN UPDATE log SET n=n+1;END;DELETE FROM t RETURNING id;"+TAIL,
 'when_partial':"CREATE TRIGGER tr BEFORE DELETE ON t WHEN old.id<>2 BEGIN UPDATE log SET v=v||old.id,n=n+1;END;DELETE FROM t RETURNING id;"+TAIL,
 'zero_rows':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN UPDATE log SET n=n+1;END;DELETE FROM t WHERE 0;"+TAIL,
 'body_subqueries':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN UPDATE log SET n=(SELECT log.n+old.n),v=(SELECT old.v);END;DELETE FROM t WHERE id<3;"+TAIL,
 'new_rows_not_selected':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN INSERT INTO t SELECT old.id+10,old.v,old.n;END;DELETE FROM t RETURNING id;"+TAIL,
 'returning_counters':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN UPDATE log SET n=n+1;END;DELETE FROM t RETURNING id,n,changes(),total_changes(),last_insert_rowid();"+TAIL,
 'atomic_error':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN INSERT INTO log VALUES(1,'conflict',old.n);END;DELETE FROM t;",
 'missing_new_prepare':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN SELECT new.id;END;DELETE FROM t WHERE 0;",
 'multiple_before_fixed':"CREATE TRIGGER first BEFORE DELETE ON t BEGIN UPDATE log SET v=v||old.v;END;CREATE TRIGGER second BEFORE DELETE ON t BEGIN UPDATE t SET v='changed' WHERE id=old.id;END;DELETE FROM t WHERE id=2 RETURNING v;"+TAIL,
 'unrelated_target':"CREATE TRIGGER tr BEFORE DELETE ON t BEGIN UPDATE log SET n=n+1;END;DELETE FROM log WHERE 0;"+TAIL,
}
rng=random.Random(int(os.environ.get('SQLEANITE_BEFORE_DELETE_SEED','1512001')))
for i in range(14):
 maximum=rng.randrange(1,4);delta=rng.randrange(-80,81)
 QUERIES[f'fresh_{i}']=f"CREATE TRIGGER before_tr BEFORE DELETE ON t WHEN old.id<={maximum} BEGIN UPDATE log SET n=n+old.n,v=v||old.v;UPDATE t SET n=n+({delta}),v=v||'changed' WHERE id=old.id;END;CREATE TRIGGER after_tr AFTER DELETE ON t BEGIN INSERT INTO log SELECT old.id+10,old.v,old.n;END;DELETE FROM t WHERE id<={maximum} RETURNING id,v,n;"+TAIL
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(BeforeDelete,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
FK_SETUP='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1),(2),(3);CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));INSERT INTO c VALUES(1,1),(2,2),(3,3);'
FK_TAIL='SELECT * FROM p ORDER BY id;SELECT * FROM c ORDER BY id;SELECT changes(),total_changes(),last_insert_rowid();'
EXTRA={
 'changed_child_fk_before':(FK_SETUP,"PRAGMA foreign_keys=ON;CREATE TRIGGER tr BEFORE DELETE ON c BEGIN UPDATE c SET pid=90 WHERE id=old.id;END;DELETE FROM c WHERE id=1;"+FK_TAIL),
 'valid_changed_child_fk_before':(FK_SETUP,"PRAGMA foreign_keys=ON;CREATE TRIGGER tr BEFORE DELETE ON c BEGIN UPDATE c SET pid=3 WHERE id=old.id;END;DELETE FROM c WHERE id=1;"+FK_TAIL),
 'parent_fk_before':(FK_SETUP,"PRAGMA foreign_keys=ON;CREATE TRIGGER tr BEFORE DELETE ON p BEGIN DELETE FROM c WHERE pid=old.id;END;DELETE FROM p WHERE id<3 RETURNING id;"+FK_TAIL),
 'child_fk_before':(FK_SETUP,"PRAGMA foreign_keys=ON;CREATE TRIGGER tr BEFORE DELETE ON c BEGIN DELETE FROM p WHERE id=old.pid;END;DELETE FROM c WHERE id<3 RETURNING id,pid;"+FK_TAIL),
 'before_fk_failure':(FK_SETUP,"PRAGMA foreign_keys=ON;CREATE TRIGGER tr BEFORE DELETE ON p BEGIN INSERT INTO c VALUES(old.id+10,old.id);END;DELETE FROM p WHERE id<3;"),
 'hidden_rowid':("CREATE TABLE t(v TEXT,n INTEGER);INSERT INTO t VALUES('a',1),('b',2),('c',3);CREATE TABLE log(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);", "CREATE TRIGGER b BEFORE DELETE ON t BEGIN UPDATE t SET n=n+10 WHERE rowid=old.rowid;END;CREATE TRIGGER a AFTER DELETE ON t BEGIN INSERT INTO log VALUES(old.rowid,old.v,old.n);END;DELETE FROM t WHERE rowid<3 RETURNING rowid,*;SELECT rowid,* FROM t;SELECT * FROM log;"),
 'shadowed_rowid':("CREATE TABLE t(rowid TEXT,v TEXT);INSERT INTO t VALUES('x','a'),('y','b');CREATE TABLE log(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);", "CREATE TRIGGER b BEFORE DELETE ON t BEGIN UPDATE t SET v='changed' WHERE _rowid_=old._rowid_;END;CREATE TRIGGER a AFTER DELETE ON t BEGIN INSERT INTO log VALUES(old._rowid_,old.rowid,0);END;DELETE FROM t RETURNING rowid,_rowid_,v;SELECT * FROM log;"),
 'old_collation':("CREATE TABLE t(v TEXT COLLATE NOCASE,n NUMERIC);INSERT INTO t VALUES('A','02'),('b','03');CREATE TABLE log(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);", "CREATE TRIGGER b BEFORE DELETE ON t BEGIN UPDATE t SET v='changed' WHERE rowid=old.rowid;END;CREATE TRIGGER a AFTER DELETE ON t WHEN old.v='a' BEGIN INSERT INTO log VALUES(old.rowid,old.v,old.n);END;DELETE FROM t RETURNING v,n,v='a';SELECT * FROM log;"),
 'delete_alias':(SETUP,"CREATE TRIGGER b BEFORE DELETE ON t BEGIN UPDATE t SET n=n+10 WHERE id=old.id;END;DELETE FROM t AS x WHERE x.id<3 RETURNING t.id,t.n;"+TAIL),
 'returning_star':(SETUP,"CREATE TRIGGER b BEFORE DELETE ON t BEGIN UPDATE t SET n=n+10,v='changed' WHERE id=old.id;END;DELETE FROM t WHERE id=2 RETURNING *;"+TAIL),
}
for name,(setup,sql) in EXTRA.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(BeforeDelete,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
