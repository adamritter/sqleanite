#!/usr/bin/env python3
"""BEFORE UPDATE candidate registers, reload and constraint timing."""
import os,random,unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class BeforeUpdate(unittest.TestCase):pass
QUERIES={
 'basic':"CREATE TRIGGER tr BEFORE UPDATE ON t BEGIN UPDATE log SET v=old.v||'/'||new.v,n=new.n-old.n;END;UPDATE t SET v=v||'!',n=n+10 WHERE id=2;"+TAIL,
 'unchanged_reload':"CREATE TRIGGER tr BEFORE UPDATE ON t BEGIN UPDATE t SET v='before',n=100 WHERE id=old.id;END;UPDATE t SET n=n+10 WHERE id=2 RETURNING id,v,n;"+TAIL,
 'assigned_frozen':"CREATE TRIGGER tr BEFORE UPDATE ON t BEGIN UPDATE t SET v='before',n=100 WHERE id=old.id;END;UPDATE t SET n=n+10,v=v||'!' WHERE id=2 RETURNING id,v,n;"+TAIL,
 'old_new_fixed':"CREATE TRIGGER b1 BEFORE UPDATE ON t BEGIN UPDATE log SET v=old.v||'/'||new.v,n=old.n+new.n;END;CREATE TRIGGER b2 BEFORE UPDATE ON t BEGIN UPDATE t SET v='changed',n=99 WHERE id=old.id;END;UPDATE t SET v=v||'!',n=n+10 WHERE id=2;"+TAIL,
 'before_after':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE t SET v='before' WHERE id=old.id;END;CREATE TRIGGER a AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(new.id+10,old.v||'/'||new.v,new.n);END;UPDATE t SET n=n+10 WHERE id=2 RETURNING id,v,n;"+TAIL,
 'delete_self':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN DELETE FROM t WHERE id=old.id;END;UPDATE t SET n=n+10 RETURNING id,n;"+TAIL,
 'move_self':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE t SET id=id+10 WHERE id=old.id;END;UPDATE t SET n=n+10 RETURNING id,n;"+TAIL,
 'delete_next':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN DELETE FROM t WHERE id=old.id+1;END;UPDATE t SET n=n+10 RETURNING id,n;"+TAIL,
 'rowid_change':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET v=old.id||'/'||new.id,n=new.n;END;UPDATE t SET id=20,n=n+10 WHERE id=2 RETURNING id,n;"+TAIL,
 'rowid_null':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;END;UPDATE t SET id=NULL WHERE id=2;",
 'rowid_text':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET v=typeof(new.id),n=new.id;END;UPDATE t SET id='020' WHERE id=2 RETURNING id;"+TAIL,
 'affinity_new':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET v=typeof(new.n)||'/'||new.v,n=new.n='03';END;UPDATE t SET n='03',v=23 WHERE id=2 RETURNING typeof(n),typeof(v);"+TAIL,
 'noop':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;END;UPDATE t SET n=n WHERE id=2;"+TAIL,
 'update_of_match':"CREATE TRIGGER b BEFORE UPDATE OF n ON t BEGIN UPDATE log SET n=n+1;END;UPDATE t SET n=n WHERE id=2;"+TAIL,
 'update_of_miss':"CREATE TRIGGER b BEFORE UPDATE OF n ON t BEGIN UPDATE log SET n=n+1;END;UPDATE t SET v='x' WHERE id=2;"+TAIL,
 'zero_rows_prepare':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN SELECT new.missing;END;UPDATE t SET n=n+1 WHERE 0;",
 'when_false':"CREATE TRIGGER b BEFORE UPDATE ON t WHEN new.n<old.n BEGIN UPDATE log SET n=n+1;END;UPDATE t SET n=n+1;"+TAIL,
 'when_partial':"CREATE TRIGGER b BEFORE UPDATE ON t WHEN new.id<>2 BEGIN UPDATE log SET n=n+1;END;UPDATE t SET n=n+1;"+TAIL,
 'total_candidate_frozen':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;END;UPDATE t SET n=total_changes() RETURNING id,n,total_changes();"+TAIL,
 'duplicate_assignments':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=new.n;END;UPDATE t SET n=abs(-9223372036854775808),n=n+10 WHERE id=2 RETURNING n;"+TAIL,
 'before_conflict_atomic':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES(1,new.v,new.n);END;UPDATE t SET n=n+1;",
 'subtype_candidate':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET v=typeof(new.v),n=subtype(new.v);END;UPDATE t SET v=json('{\"x\":1}') WHERE id=2 RETURNING v,subtype(v);"+TAIL,
 'subtype_returning':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN SELECT new.v;END;UPDATE t SET v=json('[1]') WHERE id=2 RETURNING subtype(v),json_array(v);"+TAIL,
}
rng=random.Random(int(os.environ.get('SQLEANITE_BEFORE_UPDATE_SEED','1712001')))
for i in range(12):
 maximum=rng.randrange(1,4);delta=rng.randrange(-80,81)
 QUERIES[f'fresh_{i}']=f"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET v=old.v||'/'||new.v,n=old.n+new.n;UPDATE t SET v='body',n=100 WHERE id=old.id;END;UPDATE t SET n=n+({delta}) WHERE id<={maximum} RETURNING id,v,n;"+TAIL
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(BeforeUpdate,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
EXTRA={
 'generated_new':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,g INTEGER GENERATED ALWAYS AS(n*2) STORED,v TEXT);INSERT INTO t(id,n,v) VALUES(1,2,'a');CREATE TABLE log(n INTEGER,g INTEGER);", "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES(new.n,new.g);UPDATE t SET n=100,v='body' WHERE id=old.id;END;UPDATE t SET n=n+3 RETURNING n,g,v;SELECT * FROM log;SELECT * FROM t;"),
 'generated_reload':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,v TEXT,g INTEGER GENERATED ALWAYS AS(length(v)) STORED);INSERT INTO t(id,n,v) VALUES(1,2,'a');CREATE TABLE log(n INTEGER,g INTEGER);", "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES(new.n,new.g);UPDATE t SET v='body' WHERE id=old.id;END;UPDATE t SET n=n+3 RETURNING n,g,v;SELECT * FROM log;SELECT * FROM t;"),
 'notnull_delete_skips':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER NOT NULL);INSERT INTO t VALUES(1,2);", "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN DELETE FROM t WHERE id=old.id;END;UPDATE t SET n=NULL RETURNING *;SELECT * FROM t;"),
 'notnull_replace':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER NOT NULL DEFAULT 7);INSERT INTO t VALUES(1,2);CREATE TABLE log(n INTEGER);", "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES(new.n);END;UPDATE OR REPLACE t SET n=NULL RETURNING *;SELECT * FROM log;"),
 'ignore_keeps_before':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER NOT NULL);INSERT INTO t VALUES(1,2);CREATE TABLE log(n INTEGER);", "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES(new.n);END;UPDATE OR IGNORE t SET n=NULL RETURNING *;SELECT * FROM t;SELECT * FROM log;SELECT changes(),total_changes();"),
 'check_repaired_column':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,v TEXT,CHECK(n>0 OR v='repair'));INSERT INTO t VALUES(1,2,'a');", "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE t SET v='repair' WHERE id=old.id;END;UPDATE t SET n=-1 RETURNING *;SELECT * FROM t;"),
 'strict_before_delete':("CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER) STRICT;INSERT INTO t VALUES(1,2);", "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN DELETE FROM t WHERE id=old.id;END;UPDATE t SET n='bad';"),
 'schema_expression_order':(SETUP,"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;END;UPDATE t SET n=abs(-9223372036854775808),v=json('bad') WHERE id=2;"),
 'rowid_error_first':(SETUP,"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;END;UPDATE t SET n=abs(-9223372036854775808),id=NULL WHERE id=2;"),
 'after_subtype':(SETUP,"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN SELECT new.v;END;CREATE TRIGGER a AFTER UPDATE ON t BEGIN UPDATE log SET n=subtype(new.v);END;UPDATE t SET v=json('[1]') WHERE id=2 RETURNING subtype(v);"+TAIL),
 'after_only_subtype':(SETUP,"CREATE TRIGGER a AFTER UPDATE ON t BEGIN UPDATE log SET n=subtype(new.v);END;UPDATE t SET v=json('[1]') WHERE id=2 RETURNING subtype(v);"+TAIL),
 'private_typed_call':(SETUP,"SELECT __sqlean_bound_value(1,'BLOB',74);"),
}
GEN_SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,v TEXT,g INTEGER GENERATED ALWAYS AS(length(v)) STORED);INSERT INTO t(id,n,v) VALUES(1,2,'a');CREATE TABLE log(n INTEGER,g INTEGER);"
for name,selection in {
 'local_new':'SELECT new.v FROM t AS new;',
 'scalar_new':'SELECT (SELECT new.v FROM t AS new);',
 'outer_new':'SELECT (SELECT new.v) FROM t AS new;',
 'derived_new':'SELECT new.v FROM (SELECT v FROM t) AS new;',
 'dead_projection':'SELECT new.v WHERE 0;',
}.items():
 EXTRA['mask_'+name]=(GEN_SETUP,"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN "+selection+"INSERT INTO log VALUES(new.n,new.g);UPDATE t SET v='body' WHERE id=old.id;END;UPDATE t SET n=n+3 RETURNING n,v,g;SELECT * FROM log;")
wide="CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,v TEXT,"+','.join(f'c{i}' for i in range(3,33))+",g INTEGER GENERATED ALWAYS AS(length(v)) STORED);INSERT INTO t(id,n,v) VALUES(1,2,'a');CREATE TABLE log(g INTEGER);"
EXTRA['mask_high_generated']=(wide,"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES(new.g);UPDATE t SET v='body' WHERE id=old.id;END;UPDATE t SET n=n+3;SELECT * FROM log;")
wide="CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,g INTEGER GENERATED ALWAYS AS(length(v)) STORED,"+','.join(f'c{i}' for i in range(3,35))+",v TEXT);INSERT INTO t(id,n,v) VALUES(1,2,'a');CREATE TABLE log(g INTEGER);"
EXTRA['mask_high_dependency']=(wide,"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES(new.g);UPDATE t SET v='body' WHERE id=old.id;END;UPDATE t SET n=n+3;SELECT * FROM log;")
wide='CREATE TABLE t('+','.join(f'c{i}' for i in range(1025))+');INSERT INTO t(c0) VALUES(1);CREATE TABLE log(n INTEGER);INSERT INTO log VALUES(0);'
EXTRA['internal_projection_wide']=(wide,"CREATE TRIGGER a AFTER UPDATE ON t BEGIN UPDATE log SET n=subtype(new.c0);END;UPDATE t SET c0=json('[1]');SELECT c0 FROM t;SELECT n FROM log;")
EXTRA['original_returning_limit']=(SETUP,"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT new.id;END;UPDATE t SET n=n+1 RETURNING "+','.join(['id']*2001)+';')
EXTRA['correlated_new_precedence']=(SETUP,"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log SELECT new.id+10,(SELECT new.v),new.n FROM t AS new WHERE new.id=old.id;END;UPDATE t SET v='candidate' WHERE id=2;"+TAIL)
FK_SETUP='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1),(2);CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));INSERT INTO c VALUES(1,1);'
FK_TAIL='SELECT * FROM p ORDER BY id;SELECT * FROM c ORDER BY id;SELECT changes(),total_changes(),last_insert_rowid();'
EXTRA['fk_before_parent_repair']=(FK_SETUP,'PRAGMA foreign_keys=ON;CREATE TRIGGER b BEFORE UPDATE ON c BEGIN INSERT INTO p VALUES(new.pid);END;UPDATE c SET pid=40 RETURNING id,pid;'+FK_TAIL)
EXTRA['fk_before_child_registers']=(FK_SETUP,'PRAGMA foreign_keys=ON;CREATE TRIGGER b BEFORE UPDATE ON c BEGIN UPDATE c SET pid=90 WHERE id=old.id;END;UPDATE c SET pid=2;'+FK_TAIL)
EXTRA['fk_delete_skips_candidate']=(FK_SETUP,'PRAGMA foreign_keys=ON;CREATE TRIGGER b BEFORE UPDATE ON c BEGIN DELETE FROM c WHERE id=old.id;END;UPDATE c SET pid=90 RETURNING id,pid;'+FK_TAIL)
for name,(setup,sql) in EXTRA.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(BeforeUpdate,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
