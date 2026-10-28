#!/usr/bin/env python3
"""Partial unique-index error effects through the real state-carrying API."""
import os,random,unittest
from test_error_effects import case
class PartialIndexEffects(unittest.TestCase):pass
BASE='CREATE TABLE ix(id INTEGER PRIMARY KEY,n);INSERT INTO ix VALUES(1,-2),(2,0),(3,2);CREATE UNIQUE INDEX px ON ix(n) WHERE n>0;'
TAIL='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM ix ORDER BY id;'
Q={
 'duplicate':BASE+'INSERT INTO ix VALUES(4,2);'+TAIL,
 'outside':BASE+'INSERT INTO ix VALUES(4,0);'+TAIL,
 'ignore':BASE+'INSERT OR IGNORE INTO ix VALUES(4,2);'+TAIL,
 'replace':BASE+'INSERT OR REPLACE INTO ix VALUES(4,2);'+TAIL,
 'update_ignore':BASE+'UPDATE OR IGNORE ix SET n=2 WHERE id=2;'+TAIL,
 'update_replace':BASE+'UPDATE OR REPLACE ix SET n=2 WHERE id=2;'+TAIL,
 'multi_abort':BASE+'INSERT INTO ix VALUES(4,4),(5,2);'+TAIL,
 'multi_ignore':BASE+'INSERT OR IGNORE INTO ix VALUES(4,4),(5,2),(6,6);'+TAIL,
 'multi_replace':BASE+'INSERT OR REPLACE INTO ix VALUES(4,2),(5,2);'+TAIL,
 'nulls':'CREATE TABLE ix(id INTEGER PRIMARY KEY,n);CREATE UNIQUE INDEX px ON ix(n) WHERE n IS NULL;INSERT INTO ix VALUES(1,NULL),(2,NULL);'+TAIL,
 'predicate_error':'CREATE TABLE ix(id INTEGER PRIMARY KEY,n);INSERT INTO ix VALUES(1,1);CREATE INDEX px ON ix(n) WHERE abs(n)>0;INSERT INTO ix VALUES(2,-9223372036854775808);'+TAIL,
}
AI='CREATE TABLE ai(id INTEGER PRIMARY KEY AUTOINCREMENT,n);INSERT INTO ai(n) VALUES(2);CREATE UNIQUE INDEX pa ON ai(n) WHERE n>0;'
AT='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM ai;SELECT * FROM sqlite_sequence;'
Q.update({
 'auto_ignore':AI+'INSERT OR IGNORE INTO ai(n) VALUES(2);'+AT,
 'auto_replace':AI+'INSERT OR REPLACE INTO ai(n) VALUES(2);'+AT,
 'auto_multi_ignore':AI+'INSERT OR IGNORE INTO ai(n) VALUES(2),(3),(3);'+AT,
})
FK='CREATE TABLE pp(id INTEGER PRIMARY KEY);INSERT INTO pp VALUES(1);CREATE TABLE cc(id INTEGER PRIMARY KEY,n,pid REFERENCES pp(id));INSERT INTO cc VALUES(10,2,1);CREATE UNIQUE INDEX pc ON cc(n) WHERE n>0;PRAGMA foreign_keys=ON;'
FT='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM cc;'
Q.update({
 'fk_ignore':FK+'INSERT OR IGNORE INTO cc(n,pid) VALUES(2,99);'+FT,
 'fk_replace_late':FK+'INSERT OR REPLACE INTO cc(n,pid) VALUES(2,99);'+FT,
 'fk_replace_valid':FK+'INSERT OR REPLACE INTO cc(n,pid) VALUES(2,1);'+FT,
})
rng=random.Random(int(os.environ.get('SQLEANITE_PARTIAL_EFFECTS_SEED','1829001')))
for i in range(12):
 key=rng.randrange(10,500);policy=['',' OR IGNORE',' OR REPLACE'][i%3]
 Q[f'fresh_{i}']=BASE+f'INSERT{policy} INTO ix VALUES({key},2);'+TAIL
for name,sql in Q.items():setattr(PartialIndexEffects,'test_'+name,case(sql))
if __name__=='__main__':unittest.main()
