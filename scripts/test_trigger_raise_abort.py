#!/usr/bin/env python3
"""RAISE(ABORT, expression) context, lazy messages and statement atomicity."""
import os,random,unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class RaiseAbort(unittest.TestCase):pass
Q={
 'after_insert':"CREATE TRIGGER a AFTER INSERT ON t BEGIN SELECT RAISE(ABORT,'stopped');END;INSERT INTO t VALUES(4,'d',4);",
 'before_insert':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;SELECT RAISE(ABORT,'stopped');END;INSERT INTO t VALUES(4,'d',4);",
 'after_update_atomic':"CREATE TRIGGER a AFTER UPDATE ON t WHEN new.id=2 BEGIN SELECT RAISE(ABORT,'stop two');END;UPDATE t SET n=n+10;",
 'before_delete':"CREATE TRIGGER b BEFORE DELETE ON t BEGIN UPDATE log SET n=n+1;SELECT RAISE(ABORT,old.v||'/'||old.n);END;DELETE FROM t WHERE id=2;",
 'when_abort':"CREATE TRIGGER a AFTER UPDATE ON t WHEN RAISE(ABORT,new.v) BEGIN SELECT new.id;END;UPDATE t SET n=n+1;",
 'when_false':"CREATE TRIGGER a AFTER UPDATE ON t WHEN 0 BEGIN SELECT RAISE(ABORT,'unreached');END;UPDATE t SET n=n+1;"+TAIL,
 'case_lazy':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT CASE WHEN new.n<0 THEN RAISE(ABORT,'bad') ELSE 0 END;END;UPDATE t SET n=n+1;"+TAIL,
 'coalesce_lazy':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT coalesce(new.n,RAISE(ABORT,'bad'));END;UPDATE t SET n=n+1;"+TAIL,
 'conditional_abort':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT iif(new.n=3,RAISE(ABORT,new.v),0);END;UPDATE t SET n=n+1;",
 'captured_message':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,(SELECT new.v||'/'||max(n) FROM t));END;UPDATE t SET n=n+1 WHERE id=2;",
 'printf_message':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,printf('n=%d',new.n));END;UPDATE t SET n=n+1 WHERE id=2;",
 'null_message':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,NULL);END;UPDATE t SET n=n+1;",
 'integer_message':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,new.n);END;UPDATE t SET n=n+1;",
 'real_message':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,1.25);END;UPDATE t SET n=n+1;",
 'blob_message':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,x'616263');END;UPDATE t SET n=n+1;",
 'nul_message':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,'a'||char(0)||'b');END;UPDATE t SET n=n+1;",
 'unicode_message':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,'árvíztűrő');END;UPDATE t SET n=n+1;",
 'message_error':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,json('bad'));END;UPDATE t SET n=n+1;",
 'message_binding':"CREATE TRIGGER a AFTER UPDATE ON t WHEN 0 BEGIN SELECT RAISE(ABORT,absent(new.n));END;UPDATE t SET n=n+1 WHERE 0;",
 'outside':'SELECT RAISE(ABORT,\'outside\');',
 'private_call':"SELECT __sqlean_trigger_abort('private');",
 'body_update':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN UPDATE log SET n=RAISE(ABORT,new.v);END;UPDATE t SET n=n+1;",
 'body_insert':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(4,RAISE(ABORT,new.v),4);END;UPDATE t SET n=n+1;",
 'body_delete':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN DELETE FROM log WHERE RAISE(ABORT,new.v);END;UPDATE t SET n=n+1;",
}
Q.update({
 'outer_ignore':"CREATE TRIGGER a AFTER INSERT ON t BEGIN SELECT RAISE(ABORT,new.v);END;INSERT OR IGNORE INTO t VALUES(4,'stop',4);",
 'outer_replace':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT,new.v);END;UPDATE OR REPLACE t SET n=n+1;",
 'captured_raise':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT (SELECT RAISE(ABORT,new.v));END;UPDATE t SET n=n+1;",
 'body_captured_update':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN UPDATE log SET n=(SELECT RAISE(ABORT,new.v));END;UPDATE t SET n=n+1;",
 'view_in_program':"CREATE VIEW v AS SELECT RAISE(ABORT,'view stopped') AS n;CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT * FROM v;END;UPDATE t SET n=n+1;",
 'dead_missing_message':"CREATE TRIGGER a AFTER UPDATE ON t WHEN 0 BEGIN SELECT RAISE(ABORT,new.missing);END;UPDATE t SET n=n+1 WHERE 0;",
})
rng=random.Random(int(os.environ.get('SQLEANITE_RAISE_ABORT_SEED','1817001')))
for i in range(12):
 key=rng.randrange(1,4);delta=rng.randrange(-100,101)
 Q[f'fresh_{i}']=f"CREATE TRIGGER a AFTER UPDATE ON t WHEN new.id={key} BEGIN UPDATE log SET n=new.n;SELECT RAISE(ABORT,new.v||'/'||new.n);END;UPDATE t SET n=n+({delta});"
for name,q in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(RaiseAbort,'test_'+name+'_'+suffix,case(q,mode,SETUP))
if __name__=='__main__':unittest.main()
