#!/usr/bin/env python3
"""RETURNING source scopes, real captured queries and output context permissions."""
import os,random,unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class ReturningScopes(unittest.TestCase):pass
Q={
 'insert_subquery':"INSERT INTO t VALUES(4,'d',4) RETURNING id,(SELECT count(*) FROM t);"+TAIL,
 'multiple_subquery':"INSERT INTO t VALUES(4,'d',4),(5,'e',5) RETURNING id,(SELECT count(*) FROM t);"+TAIL,
 'update_subquery':"UPDATE t SET n=n+10 RETURNING id,n,(SELECT sum(n) FROM t);"+TAIL,
 'delete_subquery':"DELETE FROM t WHERE id<3 RETURNING id,n,(SELECT count(*) FROM t);"+TAIL,
 'correlated_field':"INSERT INTO t VALUES(4,'d',4) RETURNING id,(SELECT t.n),(SELECT n);"+TAIL,
 'local_scope':"INSERT INTO t VALUES(4,'d',4) RETURNING id,(SELECT n FROM log);"+TAIL,
 'membership':"INSERT INTO t VALUES(4,'d',4) RETURNING n IN(SELECT n FROM t),EXISTS(SELECT 1 FROM log WHERE n=0);"+TAIL,
 'before_counters':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES(4,'d',4) RETURNING (SELECT total_changes()),(SELECT last_insert_rowid());"+TAIL,
 'after_counters':"CREATE TRIGGER a AFTER INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES(4,'d',4) RETURNING (SELECT total_changes()),(SELECT last_insert_rowid());"+TAIL,
 'lazy_query':"INSERT INTO t VALUES(4,'d',4) RETURNING CASE WHEN 0 THEN (SELECT abs(-9223372036854775808)) ELSE n END;"+TAIL,
 'query_width':"INSERT INTO t VALUES(4,'d',4) RETURNING (SELECT id,n FROM t);",
 'dead_query_binding':"INSERT INTO t VALUES(4,'d',4) RETURNING CASE WHEN 0 THEN (SELECT absent(n)) ELSE n END;",
 'output_alias':"INSERT INTO t VALUES(4,'d',4) RETURNING n AS v,v,(SELECT t.n);"+TAIL,
 'table_star':"INSERT INTO t VALUES(4,'d',4) RETURNING t.*;",
 'pragma_query':"INSERT INTO t VALUES(4,'d',4) RETURNING (SELECT foreign_keys FROM pragma_foreign_keys);"+TAIL,
 'raise_output':"INSERT INTO t VALUES(4,'d',4) RETURNING RAISE(ABORT,'output stop');",
 'raise_query':"INSERT INTO t VALUES(4,'d',4) RETURNING (SELECT RAISE(ABORT,'query stop'));",
 'raise_input_illegal':"INSERT INTO t VALUES(4,RAISE(ABORT,'bad input'),4) RETURNING id;",
}
Q['function_arg_priority']="INSERT INTO t VALUES(4,'d',4) RETURNING absent(missing);"
rng=random.Random(int(os.environ.get('SQLEANITE_RETURNING_SCOPE_SEED','1821001')))
for i in range(12):
 key=rng.randrange(4,100);n=rng.randrange(-100,101)
 Q[f'fresh_{i}']=f"INSERT INTO t VALUES({key},'fresh',{n}) RETURNING id,n,(SELECT n),(SELECT max(id) FROM t),EXISTS(SELECT 1 FROM t WHERE id={key});"+TAIL
for name,q in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(ReturningScopes,'test_'+name+'_'+suffix,case(q,mode,SETUP))
if __name__=='__main__':unittest.main()
