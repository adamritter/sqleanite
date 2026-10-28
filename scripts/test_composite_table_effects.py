#!/usr/bin/env python3
"""Composite automatic-index effects through the actual continuing Core API."""
import os,random,unittest
from test_error_effects import case
class CompositeTableEffects(unittest.TestCase):pass
BASE="CREATE TABLE mx(a TEXT,b INTEGER,v,PRIMARY KEY(a,b));INSERT INTO mx VALUES('A',1,'one'),('A',2,'two'),(NULL,1,'nil');"
TAIL='SELECT changes(),total_changes(),last_insert_rowid();SELECT rowid,* FROM mx ORDER BY rowid;'
Q={
 'strict_integer_null':"CREATE TABLE mx(a TEXT,b INTEGER,v TEXT,PRIMARY KEY(a,b)) STRICT;INSERT INTO mx VALUES('A',1,'one');INSERT INTO mx VALUES('B',NULL,'bad');"+TAIL,
 'collated_unique':BASE.replace('PRIMARY KEY','UNIQUE').replace('a TEXT','a TEXT COLLATE NOCASE')+"INSERT OR REPLACE INTO mx VALUES('a',1,'new');"+TAIL,
 'duplicate':BASE+"INSERT INTO mx VALUES('A',1,'duplicate');"+TAIL,
 'prefix':BASE+"INSERT INTO mx VALUES('A',3,'new');"+TAIL,
 'ignore':BASE+"INSERT OR IGNORE INTO mx VALUES('A',1,'duplicate');"+TAIL,
 'replace':BASE+"INSERT OR REPLACE INTO mx VALUES('A',1,'replaced');"+TAIL,
 'update_ignore':BASE+'UPDATE OR IGNORE mx SET b=1 WHERE rowid=2;'+TAIL,
 'update_replace':BASE+'UPDATE OR REPLACE mx SET b=1 WHERE rowid=2;'+TAIL,
 'multi_abort':BASE+"INSERT INTO mx VALUES('d',4,'four'),('A',1,'duplicate');"+TAIL,
 'multi_ignore':BASE+"INSERT OR IGNORE INTO mx VALUES('d',4,'four'),('A',1,'duplicate'),('e',5,'five');"+TAIL,
 'multi_replace':BASE+"INSERT OR REPLACE INTO mx VALUES('A',1,'four'),('A',1,'five');"+TAIL,
 'nulls':BASE+"INSERT INTO mx VALUES(NULL,1,'null'),('A',NULL,'null2'),('A',NULL,'null3');"+TAIL,
 'affinity':BASE+"INSERT INTO mx VALUES('A','1','duplicate');"+TAIL,
 'transaction':BASE+"BEGIN;INSERT INTO mx VALUES('d',4,'four');INSERT INTO mx VALUES('A',1,'duplicate');"+TAIL+'COMMIT;'+TAIL,
 'savepoint':BASE+"SAVEPOINT s;INSERT INTO mx VALUES('d',4,'four');INSERT INTO mx VALUES('A',1,'duplicate');"+TAIL+'ROLLBACK TO s;RELEASE s;'+TAIL,
 'returning':BASE+"INSERT INTO mx VALUES('d',4,'four') RETURNING rowid,a,b;"+TAIL,
 'replace_returning':BASE+"INSERT OR REPLACE INTO mx VALUES('A',1,'new') RETURNING rowid,a,b;"+TAIL,
 'unique':BASE.replace('PRIMARY KEY','UNIQUE')+"INSERT INTO mx VALUES('A',1,'duplicate');"+TAIL,
 'mixed_unique':BASE.replace('KEY(a,b)','KEY(a,b),UNIQUE(v)')+"INSERT OR REPLACE INTO mx VALUES('A',1,'two');"+TAIL,
 'drop_error':BASE+'DROP INDEX sqlite_autoindex_mx_1;'+TAIL,
}
rng=random.Random(int(os.environ.get('SQLEANITE_COMPOSITE_TABLE_EFFECTS_SEED','1847001')))
for i in range(12):
 value=rng.randrange(10,900);policy=['',' OR IGNORE',' OR REPLACE'][i%3]
 Q[f'fresh_{i}']=BASE+f"INSERT{policy} INTO mx VALUES('A',1,'{value}');"+TAIL
for name,sql in Q.items():setattr(CompositeTableEffects,'test_'+name,case(sql))
if __name__=='__main__':unittest.main()
