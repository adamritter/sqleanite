#!/usr/bin/env python3
"""Register SELECT producer plans compared in both persisted file modes."""
import os,random,unittest
from test_check_add_column import case
from test_error_effects import Q,REGISTER_PLAN_QUERIES,REGISTER_SETUP,REGISTER_TAIL
class RegisterInputPlans(unittest.TestCase):pass
CASES={}
for name,query in REGISTER_PLAN_QUERIES.items():
 if name=='rowid_alias':
  setup=REGISTER_SETUP+'CREATE TABLE out(id INTEGER PRIMARY KEY,key,n);INSERT INTO out VALUES(10,10,10);'
  sql='INSERT INTO out '+query+';SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM out ORDER BY id;'
 else:setup=REGISTER_SETUP;sql='INSERT INTO dst '+query+';'+REGISTER_TAIL
 CASES[name]=(setup,sql)
for name,sql in Q.items():
 if name.startswith('values_cursor_'):
  assert sql.startswith(REGISTER_SETUP)
  CASES[name]=(REGISTER_SETUP,sql[len(REGISTER_SETUP):])
CASES['empty_union_auto']=('',Q['register_plan_empty_union_auto'])
rng=random.Random(int(os.environ.get('SQLEANITE_REGISTER_PLAN_SEED','1827001')))
for i in range(12):
 amount=rng.randrange(10,500)
 query=f'SELECT NULL,id*{amount}+last_insert_rowid() FROM src ORDER BY id DESC' if i%2==0 else f'SELECT DISTINCT NULL,id*{amount}+last_insert_rowid() FROM src LIMIT 2 OFFSET 1'
 CASES[f'fresh_{i}']=(REGISTER_SETUP,'INSERT INTO dst '+query+';'+REGISTER_TAIL)
for name,(setup,sql) in CASES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(RegisterInputPlans,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
