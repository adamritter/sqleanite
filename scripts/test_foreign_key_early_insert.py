#!/usr/bin/env python3
"""Single-write immediate FK lookup ordering versus statement-counter paths."""
import os,random,unittest
from test_check_add_column import case
class EarlyForeignInsert(unittest.TestCase):pass
BASE='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));'
SELF='CREATE TABLE p(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));INSERT INTO p VALUES(1,4);'
Q={
 'single':(BASE,'INSERT INTO c VALUES(4,99);'),
 'returning':(BASE,'INSERT INTO c VALUES(4,99) RETURNING id;'),
 'select':(BASE,'INSERT INTO c SELECT 4,99;'),
 'multiple':(BASE,'INSERT INTO c VALUES(4,1),(5,99);'),
 'ignore_missing':(BASE,'INSERT OR IGNORE INTO c VALUES(4,99);'),
 'ignore_duplicate':(BASE+'INSERT INTO c VALUES(4,1);','INSERT OR IGNORE INTO c VALUES(4,99);SELECT * FROM c;'),
 'duplicate_first':(BASE+'INSERT INTO c VALUES(4,1);','INSERT INTO c VALUES(4,99);'),
 'null':(BASE,'INSERT INTO c VALUES(4,NULL);SELECT * FROM c;'),
 'check_first':('CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id),n CHECK(n>0));','INSERT INTO c VALUES(4,99,-1);'),
 'before_repair':(BASE,'CREATE TRIGGER b BEFORE INSERT ON c BEGIN INSERT INTO p VALUES(new.pid);END;INSERT INTO c VALUES(4,99);SELECT * FROM p;SELECT * FROM c;'),
 'self_old_orphan':(SELF,'INSERT INTO p VALUES(4,99);'),
 'self_match':(SELF,'INSERT INTO p VALUES(4,4);SELECT * FROM p;'),
}
rng=random.Random(int(os.environ.get('SQLEANITE_EARLY_FK_SEED','1824001')))
for i in range(12):
 key=rng.randrange(4,500);parent=rng.randrange(1000,5000)
 Q[f'fresh_{i}']=(BASE,f'INSERT INTO c VALUES({key},{parent});')
for name,(setup,sql) in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(EarlyForeignInsert,'test_'+name+'_'+suffix,case('PRAGMA foreign_keys=ON;'+sql,mode,setup))
if __name__=='__main__':unittest.main()
