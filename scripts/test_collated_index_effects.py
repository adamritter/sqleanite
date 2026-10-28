#!/usr/bin/env python3
"""Collated-index error effects on the actual continuing Core API."""
import os,random,unittest
from test_error_effects import case
class CollatedIndexEffects(unittest.TestCase):pass
BASE="CREATE TABLE cx(id INTEGER PRIMARY KEY,v TEXT,n);INSERT INTO cx VALUES(1,'A',1),(2,'b ',2),(3,NULL,3);"
TAIL='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM cx ORDER BY id;'
Q={}
for kind,value in [('NOCASE','a'),('RTRIM','b')]:
 setup=BASE+f'CREATE UNIQUE INDEX ux ON cx(v COLLATE {kind});'
 for name,command in {
  'abort':f"INSERT INTO cx VALUES(4,'{value}',4);",
  'ignore':f"INSERT OR IGNORE INTO cx VALUES(4,'{value}',4);",
  'replace':f"INSERT OR REPLACE INTO cx VALUES(4,'{value}',4);",
  'update_ignore':f"UPDATE OR IGNORE cx SET v='{value}' WHERE id=3;",
  'update_replace':f"UPDATE OR REPLACE cx SET v='{value}' WHERE id=3;",
  'multi_abort':f"INSERT INTO cx VALUES(4,'d',4),(5,'{value}',5);",
  'multi_replace':f"INSERT OR REPLACE INTO cx VALUES(4,'{value}',4),(5,'{value}',5);",
  'nulls':'INSERT INTO cx VALUES(4,NULL,4);',
 }.items():Q[kind+'_'+name]=setup+command+TAIL
Q['declared']=BASE.replace('v TEXT','v TEXT COLLATE NOCASE')+"CREATE UNIQUE INDEX ux ON cx(v);INSERT OR REPLACE INTO cx VALUES(4,'a',4);"+TAIL
Q['predicate']=BASE.replace('v TEXT','v TEXT COLLATE NOCASE')+"CREATE UNIQUE INDEX ux ON cx(n) WHERE v='a';INSERT OR IGNORE INTO cx VALUES(4,'a',1);"+TAIL
Q['partial_replace']=BASE.replace('v TEXT','v TEXT COLLATE NOCASE')+"CREATE UNIQUE INDEX ux ON cx(v) WHERE n>0;INSERT OR REPLACE INTO cx VALUES(4,'a',4);"+TAIL
rng=random.Random(int(os.environ.get('SQLEANITE_COLLATED_EFFECTS_SEED','1835001')))
for i in range(12):
 key=rng.randrange(10,500);policy=['',' OR IGNORE',' OR REPLACE'][i%3]
 Q[f'fresh_{i}']=BASE+'CREATE UNIQUE INDEX ux ON cx(v COLLATE NOCASE);'+f"INSERT{policy} INTO cx VALUES({key},'a',9);"+TAIL
for name,sql in Q.items():setattr(CollatedIndexEffects,'test_'+name,case(sql))
if __name__=='__main__':unittest.main()
