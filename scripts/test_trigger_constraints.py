#!/usr/bin/env python3
"""Statement-boundary foreign keys and captured UPDATE assignment semantics."""
import os
import random
import unittest
from test_check_add_column import case
from test_trigger_execution import SETUP,TAIL
class TriggerConstraints(unittest.TestCase):pass
FK_SETUP='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1),(2),(3);CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));INSERT INTO c VALUES(1,1),(2,2),(3,3);'
FK_TAIL='SELECT * FROM p ORDER BY id;SELECT * FROM c ORDER BY id;SELECT changes(),total_changes(),last_insert_rowid();'
FOREIGN={
 'child_insert_parent':"CREATE TRIGGER tr AFTER INSERT ON c BEGIN INSERT INTO p VALUES(new.pid);END;INSERT INTO c VALUES(4,40);"+FK_TAIL,
 'child_update_parent':"CREATE TRIGGER tr AFTER UPDATE OF pid ON c BEGIN INSERT OR IGNORE INTO p VALUES(new.pid);END;UPDATE c SET pid=pid+10;"+FK_TAIL,
 'child_insert_delete':"CREATE TRIGGER tr AFTER INSERT ON c BEGIN DELETE FROM c WHERE id=new.id;END;INSERT INTO c VALUES(4,40);"+FK_TAIL,
 'parent_delete_child':"CREATE TRIGGER tr AFTER DELETE ON p BEGIN DELETE FROM c WHERE pid=old.id;END;DELETE FROM p WHERE id<3;"+FK_TAIL,
 'parent_update_child':"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN UPDATE c SET pid=new.id WHERE pid=old.id;END;UPDATE p SET id=id+10;"+FK_TAIL,
 'body_repaired_delete':"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c VALUES(new.id+10,90);DELETE FROM c WHERE id=new.id+10;END;UPDATE p SET id=id WHERE id=1;"+FK_TAIL,
 'body_repaired_parent':"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c VALUES(9,90);INSERT INTO p VALUES(90);END;UPDATE p SET id=id WHERE id=1;"+FK_TAIL,
 'body_unrepaired':"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c VALUES(9,90);END;UPDATE p SET id=id WHERE id=1;",
 'late_failure_atomic':"CREATE TRIGGER tr AFTER UPDATE ON c BEGIN INSERT INTO p SELECT new.pid WHERE new.id=1;END;UPDATE c SET pid=pid+10;",
 'partial_parent_repair':"CREATE TRIGGER tr AFTER DELETE ON p BEGIN DELETE FROM c WHERE pid=old.id AND old.id=1;END;DELETE FROM p WHERE id<3;",
 'old_orphan_untouched':"PRAGMA foreign_keys=OFF;INSERT INTO c VALUES(9,99);PRAGMA foreign_keys=ON;CREATE TRIGGER tr AFTER UPDATE ON p BEGIN UPDATE c SET id=id WHERE 0;END;UPDATE p SET id=id WHERE id=1;"+FK_TAIL,
 'keys_disabled':"PRAGMA foreign_keys=OFF;CREATE TRIGGER tr AFTER INSERT ON c BEGIN INSERT INTO c VALUES(new.id+10,900);END;INSERT INTO c VALUES(4,40);"+FK_TAIL,
}
FOREIGN.update({
 'pragma_stays_enabled':"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c SELECT 9,90 WHERE (SELECT foreign_keys FROM pragma_foreign_keys)=1;INSERT INTO p VALUES(90);END;UPDATE p SET id=id WHERE id=1;"+FK_TAIL,
 'transient_check_visible':"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c VALUES(9,90);INSERT INTO p SELECT 90 WHERE EXISTS(SELECT 1 FROM pragma_foreign_key_check);END;UPDATE p SET id=id WHERE id=1;"+FK_TAIL,
 'unrepaired_body_other_edge':"CREATE TABLE q(id INTEGER PRIMARY KEY);CREATE TABLE d(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES q(id));CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO d VALUES(1,9);END;UPDATE p SET id=id WHERE id=1;",
})
FOREIGN.update({
 'physical_pragma_name':"CREATE TABLE pragma_foreign_keys(foreign_keys INTEGER);INSERT INTO pragma_foreign_keys VALUES(90);CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c VALUES(9,90);INSERT INTO p SELECT foreign_keys FROM pragma_foreign_keys;END;UPDATE p SET id=id WHERE id=1;"+FK_TAIL,
 'unsafe_through_view':"CREATE VIEW inspected AS SELECT * FROM pragma_foreign_key_check;CREATE TRIGGER tr AFTER UPDATE ON p BEGIN SELECT * FROM inspected;END;UPDATE p SET id=id WHERE 0;",
 'view_context_restored':"CREATE VIEW plain AS SELECT id FROM p;SELECT plain.id,foreign_keys FROM plain,pragma_foreign_keys ORDER BY plain.id;"+FK_TAIL,
 'innocuous_json_table':"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c SELECT 9,90 FROM json_each('[1]');INSERT INTO p VALUES(90);END;UPDATE p SET id=id WHERE id=1;"+FK_TAIL,
})
rng=random.Random(int(os.environ.get('SQLEANITE_TRIGGER_CONSTRAINT_SEED','1412001')))
for i in range(16):
 delta=rng.choice([-1,1])*rng.randrange(10,90)
 first=rng.randrange(1,4)
 last=rng.randrange(first,4)
 FOREIGN[f'fresh_{i}']=f"CREATE TRIGGER repair AFTER UPDATE OF pid ON c WHEN new.pid<>old.pid BEGIN INSERT OR IGNORE INTO p SELECT new.pid;END;UPDATE c SET pid=pid+({delta}) WHERE id>={first} AND id<={last};"+FK_TAIL
for name,sql in FOREIGN.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(TriggerConstraints,'test_fk_'+name+'_'+suffix,case('PRAGMA foreign_keys=ON;'+sql,mode,FK_SETUP))
CAPTURED={
 'duplicate_unevaluated':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=abs(-9223372036854775808),n=(SELECT new.n);END;UPDATE t SET n=n+10 WHERE id=2;"+TAIL,
 'duplicate_last_once':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=(SELECT 0),n=(SELECT log.n+new.n);END;UPDATE t SET n=n+10 WHERE id<3;"+TAIL,
 'duplicate_alias':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET id=abs(-9223372036854775808),rowid=(SELECT log.id);END;UPDATE t SET n=n+10 WHERE id=2;"+TAIL,
 'duplicate_subquery_unevaluated':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=(SELECT abs(-9223372036854775808)),n=(SELECT new.n);END;UPDATE t SET n=n+10 WHERE id=2;"+TAIL,
 'duplicate_keeps_update_of':"CREATE TRIGGER outer_tr AFTER UPDATE ON t BEGIN UPDATE log SET id=abs(-9223372036854775808),rowid=(SELECT log.id);END;CREATE TRIGGER watcher AFTER UPDATE OF id ON log BEGIN UPDATE t SET v='observed' WHERE id=2;END;UPDATE t SET n=n+1 WHERE id=2;"+TAIL,
 'duplicate_keeps_rowid_update_of':"CREATE TRIGGER outer_tr AFTER UPDATE ON t BEGIN UPDATE log SET id=abs(-9223372036854775808),rowid=(SELECT log.id);END;CREATE TRIGGER watcher AFTER UPDATE OF rowid ON log BEGIN UPDATE t SET v='observed' WHERE id=2;END;UPDATE t SET n=n+1 WHERE id=2;"+TAIL,
 'duplicate_invalid_still_prepare':"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN UPDATE log SET n=absent(new.n),n=(SELECT new.n);END;UPDATE t SET n=n+10 WHERE 0;",
}
for name,sql in CAPTURED.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(TriggerConstraints,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
if __name__=='__main__':unittest.main()
