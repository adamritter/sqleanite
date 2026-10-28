#!/usr/bin/env python3
"""Actual tuple uniqueness and later-key failures on the continuing Core API."""
import os,random,unittest
from test_error_effects import case
class CompositeIndexEffects(unittest.TestCase):pass
BASE="CREATE TABLE mx(id INTEGER PRIMARY KEY,a,b,n);INSERT INTO mx VALUES(1,'A',1,1),(2,'A',2,2),(3,NULL,1,3);"
UNIQUE='CREATE UNIQUE INDEX ux ON mx(a,b);'
TAIL='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM mx ORDER BY id;'
Q={
 'duplicate':BASE+UNIQUE+"INSERT INTO mx VALUES(4,'A',1,4);"+TAIL,
 'prefix':BASE+UNIQUE+"INSERT INTO mx VALUES(4,'A',3,4);"+TAIL,
 'ignore':BASE+UNIQUE+"INSERT OR IGNORE INTO mx VALUES(4,'A',1,4);"+TAIL,
 'replace':BASE+UNIQUE+"INSERT OR REPLACE INTO mx VALUES(4,'A',1,4);"+TAIL,
 'update_ignore':BASE+UNIQUE+'UPDATE OR IGNORE mx SET b=1 WHERE id=2;'+TAIL,
 'update_replace':BASE+UNIQUE+'UPDATE OR REPLACE mx SET b=1 WHERE id=2;'+TAIL,
 'multi_abort':BASE+UNIQUE+"INSERT INTO mx VALUES(4,'d',4,4),(5,'A',1,5);"+TAIL,
 'multi_ignore':BASE+UNIQUE+"INSERT OR IGNORE INTO mx VALUES(4,'d',4,4),(5,'A',1,5),(6,'e',6,6);"+TAIL,
 'multi_replace':BASE+UNIQUE+"INSERT OR REPLACE INTO mx VALUES(4,'A',1,4),(5,'A',1,5);"+TAIL,
 'nulls':BASE+UNIQUE+"INSERT INTO mx VALUES(4,NULL,1,4),(5,'A',NULL,5),(6,'A',NULL,6);"+TAIL,
 'second_error':BASE+"CREATE INDEX ux ON mx(a,abs(b));INSERT INTO mx VALUES(4,'d',-9223372036854775808,4);"+TAIL,
 'second_late_error':BASE+"CREATE INDEX ux ON mx(a,abs(b));INSERT INTO mx VALUES(4,'d',4,4),(5,'e',-9223372036854775808,5);"+TAIL,
 'second_update_error':BASE+"CREATE INDEX ux ON mx(a,abs(b));UPDATE mx SET b=-9223372036854775808 WHERE id=2;"+TAIL,
 'collated':BASE+"CREATE UNIQUE INDEX ux ON mx(a COLLATE NOCASE,b);INSERT OR REPLACE INTO mx VALUES(4,'a',1,4);"+TAIL,
 'expression':BASE+"CREATE UNIQUE INDEX ux ON mx(lower(a),b+1);INSERT INTO mx VALUES(4,'a',1,4);"+TAIL,
 'partial':BASE+"CREATE UNIQUE INDEX ux ON mx(a,b) WHERE n>1;INSERT OR IGNORE INTO mx VALUES(4,'A',2,4);"+TAIL,
 'multiple_victims':BASE+UNIQUE+"CREATE UNIQUE INDEX uy ON mx(a,n);INSERT OR REPLACE INTO mx VALUES(4,'A',1,2);"+TAIL,
 'transaction':BASE+UNIQUE+"BEGIN;INSERT INTO mx VALUES(4,'d',4,4);INSERT INTO mx VALUES(5,'A',1,5);"+TAIL+'COMMIT;'+TAIL,
}
rng=random.Random(int(os.environ.get('SQLEANITE_COMPOSITE_EFFECTS_SEED','1843001')))
for i in range(12):
 key=rng.randrange(10,500);policy=['',' OR IGNORE',' OR REPLACE'][i%3]
 Q[f'fresh_{i}']=BASE+UNIQUE+f"INSERT{policy} INTO mx VALUES({key},'A',1,9);"+TAIL
for name,sql in Q.items():setattr(CompositeIndexEffects,'test_'+name,case(sql))
if __name__=='__main__':unittest.main()
