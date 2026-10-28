#!/usr/bin/env python3
"""Immediate VDBE FK counter order, zero guards and signed scan decrements."""
import os,random,unittest
from test_check_add_column import case
class ForeignCounters(unittest.TestCase):pass
BASE='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1),(2),(3);CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));'
TAIL='SELECT * FROM p ORDER BY id;SELECT * FROM c ORDER BY id;SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM pragma_foreign_key_check;'
CASES={
 'cancel_old_orphan':(BASE+'INSERT INTO c VALUES(1,1),(2,90);',"CREATE TRIGGER tr AFTER UPDATE ON c BEGIN SELECT 1;END;UPDATE c SET pid=CASE id WHEN 1 THEN 91 ELSE 2 END;"+TAIL),
 'reverse_order_fails':(BASE+'INSERT INTO c VALUES(1,90),(2,1);',"CREATE TRIGGER tr AFTER UPDATE ON c BEGIN SELECT 1;END;UPDATE c SET pid=CASE id WHEN 1 THEN 2 ELSE 91 END;"+TAIL),
 'scan_goes_negative':(BASE+'INSERT INTO c VALUES(1,90),(2,90);',"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c VALUES(3,90);INSERT INTO p VALUES(90);END;UPDATE p SET id=id WHERE id=1;"+TAIL),
 'zero_guard_skips_old_orphans':(BASE+'INSERT INTO c VALUES(1,90),(2,90);',"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO p VALUES(90);END;UPDATE p SET id=id WHERE id=1;"+TAIL),
 'signed_counter_recovers':(BASE+'INSERT INTO c VALUES(1,90),(2,90);',"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c VALUES(3,90);INSERT INTO p VALUES(90);INSERT INTO c VALUES(4,91),(5,91);END;UPDATE p SET id=id WHERE id=1;"+TAIL),
 'delete_old_orphan_zero':(BASE+'INSERT INTO c VALUES(1,90);',"CREATE TRIGGER tr AFTER DELETE ON c BEGIN SELECT 1;END;DELETE FROM c;"+TAIL),
 'replace_child_repair':(BASE+'INSERT INTO c VALUES(1,90);',"CREATE TRIGGER tr AFTER INSERT ON c BEGIN SELECT 1;END;INSERT OR REPLACE INTO c VALUES(1,2);"+TAIL),
 'replace_child_same_orphan':(BASE+'INSERT INTO c VALUES(1,90);',"CREATE TRIGGER tr AFTER INSERT ON c BEGIN SELECT 1;END;INSERT OR REPLACE INTO c VALUES(1,90);"+TAIL),
 'replace_parent':(BASE+'INSERT INTO c VALUES(1,2);',"CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT OR REPLACE INTO p VALUES(2);END;UPDATE p SET id=id WHERE id=1;"+TAIL),
 'self_unchanged_fk':('CREATE TABLE s(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES s(id),v TEXT);INSERT INTO s VALUES(1,90,\'a\');',"UPDATE s SET v='b';SELECT * FROM s;"),
 'self_rekey_invalid':('CREATE TABLE s(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES s(id));INSERT INTO s VALUES(1,1);',"UPDATE s SET id=2;SELECT * FROM s;"),
 'self_rekey_both':('CREATE TABLE s(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES s(id));INSERT INTO s VALUES(1,1);',"UPDATE s SET id=id+10,pid=pid+10;SELECT * FROM s;"),
 'self_cycle_rekey':('CREATE TABLE s(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES s(id));INSERT INTO s VALUES(1,2),(2,1);',"UPDATE s SET id=id+10,pid=pid+10;SELECT * FROM s ORDER BY id;"),
}
for reverse in [False,True]:
 first='CREATE TABLE c1(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));'
 second='CREATE TABLE c2(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));'
 setup='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);'+(second+first if reverse else first+second)+'INSERT INTO c2 VALUES(1,90),(2,90);'
 sql='CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c1 VALUES(1,90);INSERT INTO p VALUES(90);END;UPDATE p SET id=id WHERE id=1;SELECT * FROM p ORDER BY id;SELECT * FROM c1;SELECT * FROM c2 ORDER BY id;'
 CASES['incoming_order_'+str(reverse)]=(setup,sql)
rng=random.Random(int(os.environ.get('SQLEANITE_FK_COUNTER_SEED','1612001')))
for i in range(8):
 old=rng.randrange(100,200);new=rng.randrange(200,300)
 setup=BASE+f'INSERT INTO c VALUES(1,1),(2,{old});'
 sql=f'CREATE TRIGGER tr AFTER UPDATE ON c BEGIN SELECT new.id;END;UPDATE c SET pid=CASE id WHEN 1 THEN {new} ELSE 2 END;'+TAIL
 CASES[f'fresh_{i}']=(setup,sql)
for name,(setup,sql) in CASES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(ForeignCounters,'test_'+name+'_'+suffix,case('PRAGMA foreign_keys=ON;'+sql,mode,setup))
if __name__=='__main__':unittest.main()
