#!/usr/bin/env python3
"""External plain SELECT coroutines, point effects and checked persistence."""
import os,random,unittest
from test_check_add_column import case
from test_error_effects import REGISTER_SETUP
class RegisterInputEffects(unittest.TestCase):pass
TAIL='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM dst ORDER BY id;'
Q={
 'counter':(REGISTER_SETUP,'INSERT INTO dst SELECT NULL,last_insert_rowid() FROM src;'+TAIL),
 'late_projection':(REGISTER_SETUP,'INSERT INTO dst SELECT id+10,CASE WHEN n=2 THEN abs(-9223372036854775808) ELSE n END FROM src;'),
 'late_predicate':(REGISTER_SETUP,'INSERT INTO dst SELECT id+10,n FROM src WHERE CASE WHEN n=2 THEN abs(-9223372036854775808) ELSE 1 END;'),
 'late_unique':(REGISTER_SETUP,'INSERT INTO dst SELECT CASE WHEN n=2 THEN 10 ELSE id+10 END,n FROM src;'),
 'predicate_counter':(REGISTER_SETUP,'INSERT INTO dst SELECT NULL,n FROM src WHERE last_insert_rowid()<12;'+TAIL),
 'offset':(REGISTER_SETUP,'INSERT INTO dst SELECT NULL,last_insert_rowid() FROM src LIMIT 2 OFFSET 1;'+TAIL),
 'skip_projection':(REGISTER_SETUP,'INSERT INTO dst SELECT NULL,CASE WHEN n=1 THEN abs(-9223372036854775808) ELSE n END FROM src LIMIT 2 OFFSET 1;'+TAIL),
 'bounded_error':(REGISTER_SETUP,'INSERT INTO dst SELECT id+10,CASE WHEN n=2 THEN abs(-9223372036854775808) ELSE n END FROM src LIMIT 1;'+TAIL),
 'ignore':(REGISTER_SETUP,'INSERT OR IGNORE INTO dst SELECT CASE WHEN n=2 THEN 10 ELSE id+10 END,last_insert_rowid() FROM src;'+TAIL),
 'replace':(REGISTER_SETUP,'INSERT OR REPLACE INTO dst SELECT CASE WHEN n=2 THEN 10 ELSE id+10 END,last_insert_rowid() FROM src;'+TAIL),
 'empty_auto':('CREATE TABLE src(id INTEGER PRIMARY KEY,n);CREATE TABLE dst(id INTEGER PRIMARY KEY AUTOINCREMENT,n);','INSERT INTO dst(id,n) SELECT id,n FROM src;SELECT * FROM sqlite_sequence;'),
 'empty_generated':('CREATE TABLE src(id INTEGER PRIMARY KEY,n);CREATE TABLE dst(id INTEGER PRIMARY KEY,n,g AS(g+1) STORED);','INSERT INTO dst(id,n) SELECT id,n FROM src;'),
 'empty_prepare':(REGISTER_SETUP,'INSERT INTO dst SELECT NULL,absent(n) FROM src WHERE 0;'),
 'self_read':(REGISTER_SETUP,'INSERT INTO dst SELECT NULL,last_insert_rowid() FROM dst;'+TAIL),
 'indexed_source':(REGISTER_SETUP+'CREATE INDEX si ON src(n);','INSERT INTO dst SELECT id+10,n FROM src WHERE n>0;'+TAIL),
 'foreign_flag':(REGISTER_SETUP,'PRAGMA foreign_keys=ON;INSERT INTO dst SELECT NULL,last_insert_rowid() FROM src;'+TAIL),
}
rng=random.Random(int(os.environ.get('SQLEANITE_REGISTER_INPUT_SEED','1826001')))
for i in range(12):
 key=rng.randrange(20,500);bad=rng.randrange(2,4)
 Q[f'fresh_{i}']=(REGISTER_SETUP,f'INSERT INTO dst SELECT id+{key},CASE WHEN n={bad} THEN abs(-9223372036854775808) ELSE n END FROM src;')
for name,(setup,sql) in Q.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:setattr(RegisterInputEffects,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__':unittest.main()
