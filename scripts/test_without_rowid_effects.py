#!/usr/bin/env python3
"""Continuing actual Core API effects for WITHOUT ROWID statements."""
import os,random,unittest
from test_error_effects import case
class WithoutRowidEffects(unittest.TestCase):pass
BASE="CREATE TABLE mx(k TEXT PRIMARY KEY,v,n) WITHOUT ROWID;INSERT INTO mx VALUES('b','bee',2),('a','aye',1);"
TAIL="SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM mx ORDER BY k;"
Q={
 'insert':BASE+"INSERT INTO mx VALUES('c','see',3);"+TAIL,
 'duplicate':BASE+"INSERT INTO mx VALUES('a','bad',9);"+TAIL,
 'ignore':BASE+"INSERT OR IGNORE INTO mx VALUES('a','bad',9);"+TAIL,
 'replace':BASE+"INSERT OR REPLACE INTO mx VALUES('a','new',9);"+TAIL,
 'multi_abort':BASE+"INSERT INTO mx VALUES('c','see',3),('a','bad',9);"+TAIL,
 'multi_ignore':BASE+"INSERT OR IGNORE INTO mx VALUES('c','see',3),('a','bad',9),('d','dee',4);"+TAIL,
 'update_key':BASE+"UPDATE mx SET k='c' WHERE k='a';"+TAIL,
 'update_ignore':BASE+"UPDATE OR IGNORE mx SET k='b' WHERE k='a';"+TAIL,
 'update_replace':BASE+"UPDATE OR REPLACE mx SET k='b' WHERE k='a';"+TAIL,
 'delete':BASE+"DELETE FROM mx WHERE k='a';"+TAIL,
 'null':BASE+"INSERT INTO mx VALUES(NULL,'bad',9);"+TAIL,
 'returning':BASE+"INSERT INTO mx VALUES('c','see',3) RETURNING k,v,n,last_insert_rowid();"+TAIL,
 'update_returning':BASE+"UPDATE mx SET n=n+1 RETURNING k,n;"+TAIL,
 'delete_returning':BASE+"DELETE FROM mx RETURNING k,n;"+TAIL,
 'rowid_error':BASE+'SELECT rowid FROM mx;'+TAIL,
 'transaction':BASE+"BEGIN;INSERT INTO mx VALUES('c','see',3);INSERT INTO mx VALUES('a','bad',9);"+TAIL+'ROLLBACK;'+TAIL,
 'last_id':BASE+"INSERT INTO t VALUES(42,'ordinary',42);INSERT INTO mx VALUES('c','see',3);"+TAIL,
 'after_program':BASE+"CREATE TRIGGER a AFTER INSERT ON mx BEGIN INSERT INTO log(v,n) VALUES(new.k,new.n);END;INSERT INTO mx VALUES('c','see',3);"+TAIL+'SELECT * FROM log ORDER BY id;',
 'before_program':BASE+"CREATE TRIGGER a BEFORE UPDATE ON mx BEGIN INSERT INTO log(v,n) VALUES(old.k,new.n);END;UPDATE mx SET n=n+1;"+TAIL+'SELECT * FROM log ORDER BY id;',
 'after_abort':BASE+"CREATE TRIGGER a AFTER INSERT ON mx BEGIN INSERT INTO log(v,n) VALUES(new.k,new.n);SELECT RAISE(ABORT,'stop');END;INSERT INTO mx VALUES('c','see',3);"+TAIL+'SELECT * FROM log ORDER BY id;',
}
rng=random.Random(int(os.environ.get('SQLEANITE_WITHOUT_ROWID_EFFECTS_SEED','1850001')))
for i in range(12):
 amount=rng.randrange(20,900);Q[f'fresh_{i}']=BASE+f"UPDATE mx SET n={amount} WHERE k='a';"+TAIL
for name,sql in Q.items():setattr(WithoutRowidEffects,'test_'+name,case(sql))
if __name__=='__main__':unittest.main()
