#!/usr/bin/env python3
"""Window ordering/partition/frame regressions on both production file modes."""
import os, random, unittest
from test_pragma_tables import case
SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER); INSERT INTO t VALUES(1,'a',3),(2,'A',NULL),(3,'b',3),(4,'b',-2),(5,NULL,7);"
QUERIES={
 'uppercase':'SELECT id,ROW_NUMBER() OVER(ORDER BY id) FROM t ORDER BY id;',
 'constant_order':'SELECT id,row_number() OVER(ORDER BY 1) FROM t ORDER BY id;',
 'alias_collision':'SELECT n AS id,row_number() OVER(ORDER BY id) FROM t ORDER BY 2;',
 'mixed_storage':"SELECT id,sum(n) OVER(ORDER BY id ROWS BETWEEN 1 PRECEDING AND CURRENT ROW) FROM t ORDER BY id;",
 'empty_error':'SELECT sum(missing) OVER(ORDER BY id) FROM t WHERE 0;',
 'limit_zero':'SELECT sum(n) OVER(ROWS -1 PRECEDING) FROM t LIMIT 0;',
 'window_order':'SELECT id,row_number() OVER(ORDER BY n,id) FROM t;',
 'window_order_multiple':'SELECT id,row_number() OVER(ORDER BY n,id),row_number() OVER(ORDER BY id DESC) FROM t;',
 'partition_order':'SELECT id,sum(n) OVER(PARTITION BY v) FROM t;',
 'row_number':'SELECT id,row_number() OVER (ORDER BY n,id) FROM t ORDER BY id;',
 'partition':'SELECT id,row_number() OVER (PARTITION BY v COLLATE NOCASE ORDER BY id DESC) FROM t ORDER BY id;',
 'nulls':'SELECT id,row_number() OVER (ORDER BY n DESC NULLS LAST,id) FROM t ORDER BY id;',
 'filter_before':'SELECT id,row_number() OVER (ORDER BY id) FROM t WHERE id>2 ORDER BY id;',
 'empty':'SELECT sum(n) OVER(),row_number() OVER() FROM t WHERE id<0;',
 'no_source':'SELECT row_number() OVER(),sum(3) OVER();',
 'aliases':'SELECT id,row_number() OVER(ORDER BY n,id) AS r FROM t ORDER BY r DESC LIMIT 3 OFFSET 1;',
 'tied_multiple':'SELECT id,row_number() OVER(ORDER BY n),row_number() OVER(ORDER BY id DESC) FROM t ORDER BY id;',
 'multiple':'SELECT id,row_number() OVER(ORDER BY id),row_number() OVER(ORDER BY id DESC) FROM t ORDER BY id;',
 'wrapped':'SELECT id,100+row_number() OVER(ORDER BY id) FROM t ORDER BY id;',
 'star':'SELECT *,row_number() OVER(ORDER BY id) FROM t ORDER BY id;',
 'default_peers':'SELECT id,sum(n) OVER(ORDER BY n) FROM t ORDER BY id;',
 'all_partition':'SELECT id,sum(n) OVER(PARTITION BY v) FROM t ORDER BY id;',
 'filtered':'SELECT id,sum(n) FILTER(WHERE n>0) OVER(ORDER BY id ROWS BETWEEN 1 PRECEDING AND CURRENT ROW) FROM t ORDER BY id;',
 'derived':'SELECT id,r FROM (SELECT id,row_number() OVER(ORDER BY id DESC) r FROM t) ORDER BY id;',
 'cte':'WITH c AS (SELECT id,sum(n) OVER(ORDER BY id) s FROM t) SELECT * FROM c ORDER BY id;',
 'distinct':'SELECT DISTINCT sum(n) OVER() FROM t;',
 'bad_arity':'SELECT row_number(1) OVER() FROM t;',
 'bad_column':'SELECT sum(missing) OVER() FROM t WHERE 0;',
 'bad_where_sum':'SELECT id FROM t WHERE sum(n) OVER()>1;',
 'bad_where':'SELECT id FROM t WHERE row_number() OVER()>1;',
 'bad_offset':'SELECT sum(n) OVER(ROWS -1 PRECEDING) FROM t;',
}
for fn in ['sum(n)','count(*)','count(n)','avg(n)','min(n)','max(n)','total(n)','group_concat(v)']:
 for name,frame in [('whole','ROWS BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING'),('one','ROWS BETWEEN 1 PRECEDING AND CURRENT ROW'),('future','ROWS BETWEEN CURRENT ROW AND 1 FOLLOWING'),('empty','ROWS BETWEEN 3 FOLLOWING AND 4 FOLLOWING')]:
  QUERIES[fn.split('(')[0]+'_'+('star_' if '*' in fn else '')+name]=f'SELECT id,{fn} OVER(ORDER BY id {frame}) FROM t ORDER BY id;'
rng=random.Random(int(os.environ.get('SQLEANITE_WINDOW_SEED','357500')))
CASES=[(name,sql,SETUP if name != 'mixed_storage' else "CREATE TABLE t(id INTEGER PRIMARY KEY,n);INSERT INTO t VALUES(1,2.5),(2,'3'),(3,NULL),(4,x'34'),(5,'bad');") for name,sql in QUERIES.items()]
CASES.append(('hidden_rowid','SELECT rowid,n,row_number() OVER(ORDER BY n) FROM t ORDER BY rowid;', 'CREATE TABLE t(n);INSERT INTO t VALUES(3),(2),(7);'))
CASES.append(('integer_extremes','SELECT id,sum(n) OVER(ORDER BY id ROWS CURRENT ROW) FROM t ORDER BY id;', 'CREATE TABLE t(id INTEGER PRIMARY KEY,n);INSERT INTO t VALUES(1,9223372036854775807),(2,-9223372036854775808);'))
for i in range(10):
 rows=','.join(f"({j},'{rng.choice('abc')}',{rng.randrange(-50,50)})" for j in range(1,15))
 setup='CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES'+rows+';'
 sql=f'SELECT id,row_number() OVER(PARTITION BY v ORDER BY n,id),sum(n) OVER(PARTITION BY v ORDER BY id ROWS BETWEEN {rng.randrange(4)} PRECEDING AND {rng.randrange(3)} FOLLOWING) FROM t ORDER BY id;'
 CASES.append(('generated_'+str(i),sql,setup))
for j,values in enumerate(['2.5,3,NULL,4,0','1e16,1,-1e16,3.5,2','NULL,1.25,2,3,4','9e999,2,3,4,5']):
 setup='CREATE TABLE t(id INTEGER PRIMARY KEY,n);INSERT INTO t VALUES'+','.join(f'({i+1},{value})' for i,value in enumerate(values.split(',')))+';'
 for k,frame in enumerate(['ROWS BETWEEN 1 PRECEDING AND CURRENT ROW','ROWS BETWEEN 1 FOLLOWING AND 2 FOLLOWING','ROWS CURRENT ROW']):
  CASES.append((f'numeric_{j}_{k}',f'SELECT id,sum(n) OVER(ORDER BY id {frame}),avg(n) OVER(ORDER BY id {frame}),total(n) OVER(ORDER BY id {frame}) FROM t ORDER BY id;',setup))
class Windows(unittest.TestCase):pass
for name,sql,setup in CASES:
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(Windows,'test_'+name+'_'+suffix,case(sql,mode,setup))
if __name__=='__main__': unittest.main()
