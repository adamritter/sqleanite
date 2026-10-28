#!/usr/bin/env python3
"""Expression-index effects through the actual state-carrying Core API."""
import os,random,unittest
from test_error_effects import case
class ExpressionIndexEffects(unittest.TestCase):pass
BASE="CREATE TABLE ex(id INTEGER PRIMARY KEY,v TEXT,n);INSERT INTO ex VALUES(1,'A',1),(2,'b',2),(3,NULL,3);CREATE UNIQUE INDEX ux ON ex(lower(v));"
TAIL='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM ex ORDER BY id;'
Q={
 'abort':BASE+"INSERT INTO ex VALUES(4,'a',9);"+TAIL,
 'ignore':BASE+"INSERT OR IGNORE INTO ex VALUES(4,'a',9);"+TAIL,
 'replace':BASE+"INSERT OR REPLACE INTO ex VALUES(4,'a',9);"+TAIL,
 'update_ignore':BASE+"UPDATE OR IGNORE ex SET v='a' WHERE id=2;"+TAIL,
 'update_replace':BASE+"UPDATE OR REPLACE ex SET v='a' WHERE id=2;"+TAIL,
 'multi_abort':BASE+"INSERT INTO ex VALUES(4,'d',4),(5,'a',5);"+TAIL,
 'multi_ignore':BASE+"INSERT OR IGNORE INTO ex VALUES(4,'d',4),(5,'a',5),(6,'e',6);"+TAIL,
 'multi_replace':BASE+"INSERT OR REPLACE INTO ex VALUES(4,'a',4),(5,'A',5);"+TAIL,
 'nulls':BASE+'INSERT INTO ex VALUES(4,NULL,4);'+TAIL,
 'key_error':"CREATE TABLE ex(id INTEGER PRIMARY KEY,v,n);INSERT INTO ex VALUES(1,'A',1);CREATE INDEX ux ON ex(abs(n));INSERT INTO ex VALUES(2,'b',-9223372036854775808);"+TAIL,
 'late_key_error':"CREATE TABLE ex(id INTEGER PRIMARY KEY,v,n);CREATE INDEX ux ON ex(abs(n));INSERT INTO ex VALUES(1,'A',1),(2,'b',-9223372036854775808);"+TAIL,
 'date_runtime':"CREATE TABLE ex(id INTEGER PRIMARY KEY,v,n);CREATE INDEX ux ON ex(date(v));INSERT INTO ex VALUES(1,'2000-01-01',1),(2,'now',2);"+TAIL,
 'transaction':BASE+"BEGIN;INSERT INTO ex VALUES(4,'d',4);INSERT INTO ex VALUES(5,'a',5);"+TAIL+'COMMIT;'+TAIL,
}
AI="CREATE TABLE ai(id INTEGER PRIMARY KEY AUTOINCREMENT,v);INSERT INTO ai(v) VALUES('A');CREATE UNIQUE INDEX ax ON ai(lower(v));"
AT='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM ai;SELECT * FROM sqlite_sequence;'
Q['auto_ignore']=AI+"INSERT OR IGNORE INTO ai(v) VALUES('a');"+AT
Q['auto_replace']=AI+"INSERT OR REPLACE INTO ai(v) VALUES('a');"+AT
rng=random.Random(int(os.environ.get('SQLEANITE_EXPRESSION_EFFECTS_SEED','1832001')))
for i in range(12):
 key=rng.randrange(10,500);policy=['',' OR IGNORE',' OR REPLACE'][i%3]
 Q[f'fresh_{i}']=BASE+f"INSERT{policy} INTO ex VALUES({key},'a',9);"+TAIL
for name,sql in Q.items():setattr(ExpressionIndexEffects,'test_'+name,case(sql))
if __name__=='__main__':unittest.main()
