#!/usr/bin/env python3
"""BEFORE INSERT register image, rowid allocation and constraint timing."""
import os,random,unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class BeforeInsert(unittest.TestCase):pass
QUERIES={
 'basic':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET v=new.v,n=new.n;END;INSERT INTO t VALUES(4,'d',4) RETURNING *;"+TAIL,
 'auto_rowid':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET v=typeof(new.id),n=new.id;END;INSERT INTO t(v,n) VALUES('d',4) RETURNING *;"+TAIL,
 'null_rowid':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;END;INSERT INTO t VALUES(NULL,'d',4) RETURNING *;"+TAIL,
 'zero_rowid':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;END;INSERT INTO t VALUES(0,'d',4) RETURNING *;"+TAIL,
 'text_rowid':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET v=typeof(new.id),n=new.id;END;INSERT INTO t VALUES('004','d',4) RETURNING *;"+TAIL,
 'bad_rowid':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES('bad','d',4);",
 'before_after':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET v=v||'before',n=new.id;END;CREATE TRIGGER a AFTER INSERT ON t BEGIN UPDATE log SET v=v||'after',n=n+new.id;END;INSERT INTO t(v,n) VALUES('d',4) RETURNING id;"+TAIL,
 'auto_after_body_insert':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO t VALUES(10,'body',10);UPDATE log SET n=new.id;END;INSERT INTO t(v,n) VALUES('d',4) RETURNING id;"+TAIL,
 'before_delete_max':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN DELETE FROM t WHERE id=3;END;INSERT INTO t(v,n) VALUES('d',4) RETURNING id;"+TAIL,
 'before_replaces_target':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO t VALUES(new.id,'body',0);END;INSERT OR REPLACE INTO t VALUES(4,'d',4) RETURNING *;"+TAIL,
 'ignore_runs_before':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT OR IGNORE INTO t VALUES(1,'duplicate',4);"+TAIL,
 'constraint_after_before':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES(1,'duplicate',4);",
 'multiple_values':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET v=v||new.id,n=n+new.n;END;INSERT INTO t VALUES(4,'d',4),(5,'e',5) RETURNING id,n;"+TAIL,
 'insert_select':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET v=v||new.id,n=n+new.n;END;INSERT INTO t SELECT id+10,v,n+10 FROM t WHERE id<3 RETURNING id,n;"+TAIL,
 'when_false':"CREATE TRIGGER b BEFORE INSERT ON t WHEN 0 BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES(4,'d',4);"+TAIL,
 'when_new':"CREATE TRIGGER b BEFORE INSERT ON t WHEN new.n>3 BEGIN UPDATE log SET n=new.n;END;INSERT INTO t VALUES(4,'d',4);"+TAIL,
 'old_missing':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN SELECT old.id;END;INSERT INTO t SELECT 4,'d',4 WHERE 0;",
 'new_subtype':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=subtype(new.v);END;INSERT INTO t VALUES(4,json('[1]'),4) RETURNING subtype(v);"+TAIL,
 'new_affinity':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET v=typeof(new.n)||'/'||typeof(new.v),n=new.n='04';END;INSERT INTO t VALUES(4,23,'04') RETURNING typeof(v),typeof(n);"+TAIL,
 'single_rowid_counter':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;END;INSERT INTO t VALUES(total_changes()+10,'d',4) RETURNING id;"+TAIL,
 'multiple_counter_values':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES(10,'d',total_changes()),(11,'e',total_changes()) RETURNING id,n;"+TAIL,
 'single_value_counter':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES(4,'d',total_changes()) RETURNING n;"+TAIL,
}
rng=random.Random(int(os.environ.get('SQLEANITE_BEFORE_INSERT_SEED','1812001')))
for i in range(12):
 key=rng.randrange(4,100);value=rng.randrange(-100,101)
 QUERIES[f'fresh_{i}']=f"CREATE TRIGGER b BEFORE INSERT ON t WHEN new.n=({value}) BEGIN UPDATE log SET v=new.v,n=new.id;END;INSERT INTO t VALUES({key},'fresh',{value}) RETURNING id,v,n;"+TAIL
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(BeforeInsert,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
EXTRA={
 'defaults':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER DEFAULT '07',v TEXT DEFAULT 9);CREATE TABLE log(id,n,v);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.id,new.n,new.v);END;INSERT INTO t DEFAULT VALUES RETURNING *;SELECT * FROM log;"),
 'generated':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,g INTEGER GENERATED ALWAYS AS(n*2) STORED,v TEXT);CREATE TABLE log(id,n,g);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.id,new.n,new.g);END;INSERT INTO t VALUES(NULL,'04','v') RETURNING *;SELECT * FROM log;"),
 'generated_captured_body':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,g INTEGER GENERATED ALWAYS AS(n*2) STORED);CREATE TABLE log(id INTEGER PRIMARY KEY,n INTEGER);", "CREATE TRIGGER b BEFORE INSERT ON log BEGIN INSERT INTO t VALUES(new.id,(SELECT new.n));END;INSERT INTO log VALUES(4,5);SELECT * FROM t;"),
 'notnull_new':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER NOT NULL DEFAULT 7);CREATE TABLE log(n);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.n);END;INSERT OR REPLACE INTO t VALUES(1,NULL) RETURNING *;SELECT * FROM log;"),
 'ignore_notnull':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER NOT NULL);CREATE TABLE log(n);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.n);END;INSERT OR IGNORE INTO t VALUES(1,NULL) RETURNING *;SELECT * FROM t;SELECT * FROM log;SELECT changes(),total_changes();"),
 'check_after_body':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER CHECK(n>0));CREATE TABLE log(n);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.n);END;INSERT INTO t VALUES(1,-1);"),
 'strict_before':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER) STRICT;CREATE TABLE log(n);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN SELECT abs(-9223372036854775808);END;INSERT INTO t VALUES(1,'bad');"),
 'strict_affinity':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER) STRICT;CREATE TABLE log(n);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(typeof(new.n));END;INSERT INTO t VALUES(1,'04') RETURNING *;SELECT * FROM log;"),
 'strict_any':("CREATE TABLE t(id INTEGER PRIMARY KEY,n ANY) STRICT;CREATE TABLE log(n);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(typeof(new.n));END;INSERT INTO t VALUES(1,'04') RETURNING n,typeof(n);SELECT * FROM log;"),
 'hidden_rowid':("CREATE TABLE t(v TEXT);CREATE TABLE log(id,v);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.rowid,new.v);END;INSERT INTO t VALUES('a') RETURNING rowid,v;SELECT * FROM log;"),
 'hidden_explicit':("CREATE TABLE t(v TEXT);CREATE TABLE log(id,v);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.rowid,new.v);END;INSERT INTO t(rowid,v) VALUES(9,'a') RETURNING rowid,v;SELECT * FROM log;"),
 'autoincrement':("CREATE TABLE t(id INTEGER PRIMARY KEY AUTOINCREMENT,n);INSERT INTO t VALUES(40,1);DELETE FROM t;CREATE TABLE log(id);", "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.id);END;INSERT INTO t(n) VALUES(2) RETURNING id;SELECT * FROM log;SELECT * FROM sqlite_sequence;"),
 'before_after_subtype':(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=subtype(new.v);END;CREATE TRIGGER a AFTER INSERT ON t BEGIN UPDATE log SET v=subtype(new.v);END;INSERT INTO t VALUES(4,json('[1]'),4) RETURNING subtype(v);"+TAIL),
 'multiple_subtype':(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.id,typeof(new.v),subtype(new.v));END;INSERT INTO t VALUES(4,json('[1]'),4),(5,json('[2]'),5) RETURNING subtype(v);"+TAIL),
 'rowid_cached_subquery':(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;DELETE FROM t WHERE id=3;END;INSERT INTO t VALUES((SELECT max(id)+10 FROM t),'d',4) RETURNING id;"+TAIL),
 'rowid_mixed_cached_counter':(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;END;INSERT INTO t VALUES((SELECT max(id) FROM t)+total_changes()+10,'d',4) RETURNING id;"+TAIL),
 'ordinary_captured_frozen':(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN DELETE FROM t WHERE id=3;END;INSERT INTO t VALUES(4,'d',(SELECT max(n) FROM t)) RETURNING n;"+TAIL),
 'duplicate_ordinary_skipped':(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.n;END;INSERT INTO t(id,v,n,n) VALUES(4,'d',4,abs(-9223372036854775808)) RETURNING n;"+TAIL),
 'duplicate_rowid_skipped':(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;END;INSERT INTO t(id,rowid,v,n) VALUES(abs(-9223372036854775808),4,'d',4) RETURNING id;"+TAIL),
 'multiple_discarded_error':(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;END;INSERT INTO t(id,v,n,n) VALUES(4,'d',4,abs(-9223372036854775808)),(5,'e',5,5);"),
 'ordinary_before_rowid_error':(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN SELECT new.id;END;INSERT INTO t VALUES('bad',json('bad'),4);"),
}
for name,expr in {
 'case_cached_counter':"CASE WHEN total_changes()=0 THEN (SELECT max(id) FROM t) ELSE 10 END+total_changes()+10",
 'case_dormant_error':"CASE WHEN total_changes()=0 THEN 10 ELSE (SELECT abs(-9223372036854775808)) END",
 'case_cached_deleted':"CASE WHEN 1 THEN (SELECT max(id) FROM t) ELSE 1 END+total_changes()+10",
 'coalesce_cached':"coalesce((SELECT max(id) FROM t),1)+total_changes()+10",
 'coalesce_dormant_error':"coalesce(10,(SELECT abs(-9223372036854775808)))+total_changes()",
 'iif_cached':"iif(total_changes()=0,(SELECT max(id) FROM t),10)+total_changes()+10",
 'if_dormant_error':"if(1,10,(SELECT abs(-9223372036854775808)))+total_changes()",
}.items():
 EXTRA[name]=(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;DELETE FROM t WHERE id=3;END;INSERT INTO t VALUES("+expr+",'d',4) RETURNING id;"+TAIL)
EXTRA['physical_expression_order']=(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN SELECT new.id;END;INSERT INTO t(n,v,id) VALUES(abs(-9223372036854775808),json('bad'),4);")
for name,expr in {
 'in_cached_set':"(1 IN(SELECT id FROM t))+10+total_changes()",
 'in_cached_dynamic_left':"((total_changes()+1) IN(SELECT id FROM t))+10",
 'in_list_lazy':"(10 IN(10,(SELECT abs(-9223372036854775808))))+9+total_changes()",
 'in_empty_lazy':"((SELECT abs(-9223372036854775808)) IN())+10+total_changes()",
 'scalar_affinity':"((SELECT n FROM t WHERE id=3)='3')+10+total_changes()",
 'case_base_affinity':"CASE (SELECT n FROM t WHERE id=3) WHEN '3' THEN 10 ELSE 20 END+total_changes()",
}.items():
 EXTRA[name]=(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;DELETE FROM t;END;INSERT INTO t VALUES("+expr+",'d',4) RETURNING id;"+TAIL)
EXTRA['conditional_shortcircuit']=(SETUP,"CREATE TRIGGER b BEFORE INSERT ON t BEGIN SELECT json('bad');END;INSERT INTO t VALUES(CASE WHEN total_changes()>0 AND (SELECT abs(-9223372036854775808)) THEN 20 ELSE 10 END,'d',4);")
FK_SETUP='CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));'
EXTRA['fk_before_parent_repair']=(FK_SETUP,'PRAGMA foreign_keys=ON;CREATE TRIGGER b BEFORE INSERT ON c BEGIN INSERT INTO p VALUES(new.pid);END;INSERT INTO c VALUES(1,40) RETURNING *;SELECT * FROM p;SELECT * FROM c;SELECT changes(),total_changes(),last_insert_rowid();')
EXTRA['fk_before_child_orphan']=(FK_SETUP,'PRAGMA foreign_keys=ON;CREATE TRIGGER b BEFORE INSERT ON p BEGIN INSERT INTO c VALUES(1,new.id);END;INSERT INTO p VALUES(40) RETURNING *;SELECT * FROM p;SELECT * FROM c;SELECT changes(),total_changes(),last_insert_rowid();')
for name,(setup,sql) in EXTRA.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(BeforeInsert,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
