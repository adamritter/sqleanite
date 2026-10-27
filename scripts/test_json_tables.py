#!/usr/bin/env python3
"""Differential JSON table regressions: values, byte-offset IDs, paths and subtype."""
import json
import os
import random
import unittest
from test_pragma_tables import case

def literal(value): return "'"+value.replace("'","''")+"'"
DOCS={
 'null':'null','true':'true','false':'false','integer':'-17','real':'1.25','text':'"hello"',
 'empty_array':'[]','empty_object':'{}','array':'[1,2,3]',
 'mixed':'[null,true,false,1,2.5,"x",[],{}]',
 'nested':'{"a":[1,2],"b":{"c":3}}',
 'duplicates':'{"a":1,"a":2}',
 'labels':'{"a_b":1,"0":2,"":3,"é":4,"ab":5}',
 'escapes':'{"a\\u0062":"x\\n\\u263a","a\\\"b":2}',
 'integer_bounds':'[9223372036854775807,-9223372036854775808,9223372036854775808]',
 'json5':"{unquoted: +1, hex: 0x12, fractional: .5, inf: Infinity, nan: NaN,}",
 'whitespace':' { "a" : [ 1, 2 ] } ',
 'header_size':json.dumps({'long key '+str(i):'x'*i for i in range(20)}),
}
QUERIES={}
projection='rowid,key,type,typeof(value),value,atom,id,parent,fullkey,path,json,root'
for name,doc in DOCS.items():
 for fn in ['json_each','json_tree']:
  QUERIES[name+'_'+fn]=f'SELECT {projection} FROM {fn}({literal(doc)}) ORDER BY rowid;'
pathdoc='{"a":[1,2,{"x":3}],"b":{"y":[4,5]},"a_b":6}'
for i,path in enumerate(['$','$.a','$.a[0]','$.a[1]','$.a[2]','$.a[2].x','$.b','$.b.y[1]','$."a_b"','$.missing','$.a[#-1]']):
 for fn in ['json_each','json_tree']:
  QUERIES['path_'+str(i)+'_'+fn]=f'SELECT {projection} FROM {fn}({literal(pathdoc)},{literal(path)}) ORDER BY rowid;'
QUERIES.update({
 'empty_args':'SELECT * FROM json_each();SELECT * FROM json_tree();',
 'null_args':'SELECT * FROM json_each(NULL);SELECT * FROM json_tree(NULL);',
 'null_path':"SELECT * FROM json_each('[1]',NULL);SELECT * FROM json_tree('[1]',NULL);",
 'numeric_input':'SELECT json,typeof(json),value,typeof(value) FROM json_each(12);',
 'jsonb':"SELECT rowid,key,value,type,id,parent,fullkey,path,hex(json),root FROM json_tree(jsonb('{\"a\":[1,2]}'));",
 'blob_text':"SELECT json,typeof(json),value FROM json_each(CAST('[1,2]' AS BLOB));",
 'subtype':"SELECT key,subtype(value),json_array(value),json_object('v',value) FROM json_each('[1,[2],{\"a\":3},\"x\"]') ORDER BY rowid;",
 'json_group':"SELECT json_group_array(value) FROM json_each('[[1],[2],3]');",
 'derived_mixed_expressions':"SELECT json_array(v),json_array(x) FROM (SELECT value AS v,json_array(value) AS x FROM json_each('[[1],[2]]'));",
 'derived_cast':"SELECT x='1',typeof(x) FROM (SELECT CAST(value AS INTEGER) AS x FROM json_each('[1,2]'));",
 'derived_computed':"SELECT json_array(x) FROM (SELECT json_array(value) AS x FROM json_each('[1,2]'));",
 'derived_constant':"SELECT json_array(x) FROM (SELECT json('[1]') AS x FROM json_each('[1,2]'));",
 'derived_mixed':"SELECT json_array(value) FROM (SELECT value FROM json_each('[\"[1]\",[2]]'));",
 'derived_nested':"SELECT json_array(value) FROM (SELECT value FROM (SELECT value FROM json_each('[[1],[2]]')));",
 'derived_star':"SELECT json_array(value) FROM (SELECT * FROM json_each('[[1],[2]]'));",
 'derived_alias':"SELECT json_array(q.x) FROM (SELECT value AS x FROM json_each('[[1],[2]]')) q;",
 'derived_filter':"SELECT json_array(value) FROM (SELECT value FROM json_each('[[1],[2]]') WHERE key>0);",
 'derived_materialized_limit':"SELECT json_array(value) FROM (SELECT value FROM json_each('[[1],[2]]') LIMIT 10 OFFSET 0);",
 'cte_default':"WITH j AS (SELECT value FROM json_each('[[1],[2]]')) SELECT json_array(value) FROM j;",
 'cte_not_materialized':"WITH j AS NOT MATERIALIZED (SELECT value FROM json_each('[[1],[2]]')) SELECT json_array(value) FROM j;",
 'cte_column_alias':"WITH j(x) AS (SELECT value FROM json_each('[[1],[2]]')) SELECT json_array(j.x) FROM j;",
 'cte_star':"WITH j AS (SELECT * FROM json_each('[[1],[2]]')) SELECT json_array(value) FROM j;",
 'cte_materialized':"WITH j AS MATERIALIZED (SELECT value FROM json_each('[[1],[2]]')) SELECT json_array(value) FROM j;",
 'derived_subtype':"SELECT json_array(value) FROM (SELECT value FROM json_each('[[1],[2]]'));",
 'filter':"SELECT fullkey,atom FROM json_tree('{\"a\":[1,2],\"b\":3}') WHERE type='integer' ORDER BY id DESC;",
 'aggregate':"SELECT count(*),sum(atom),max(id) FROM json_tree('[1,[2,3]]');",
 'join':"SELECT a.key,a.value,b.value FROM json_each('[1,2]') a JOIN json_each('[3,4]') b ON a.key=b.key ORDER BY a.key;",
 'left_join':"SELECT a.key,b.json,b.root,b.value FROM json_each('[1,2]') a LEFT JOIN json_each('[]') b ON a.key=b.key ORDER BY a.key;",
 'hidden_filter':"SELECT value FROM json_each('[1,2]') WHERE root='$' AND json='[1,2]' ORDER BY key;",
 'cte':"WITH j AS (SELECT * FROM json_each('[1,2]')) SELECT sum(value) FROM j;",
 'arity':"SELECT * FROM json_each('[1]','$',0);",
 'malformed':"SELECT * FROM json_each('[1,');",
 'malformed_null_path':"SELECT * FROM json_tree('[1,',NULL);",
 'bad_path':"SELECT * FROM json_each('[1]','bad');",
 'bad_index':"SELECT * FROM json_tree('[1]','$[x]');",
 'unknown_column':"SELECT * FROM json_each(missing);",
})
rng=random.Random(int(os.environ.get('SQLEANITE_JSON_TABLE_SEED','357001')))
for i in range(12):
 doc=json.dumps({f'field {k}':[rng.randrange(-100000,100000),rng.choice([None,True,False]),{'nested':str(rng.randrange(1000))}] for k in range(rng.randrange(1,7))},ensure_ascii=False)
 for fn in ['json_each','json_tree']:
  QUERIES['generated_'+str(i)+'_'+fn]=f'SELECT {projection} FROM {fn}({literal(doc)}) ORDER BY rowid;'
class JsonTables(unittest.TestCase):pass
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(JsonTables,'test_'+name+'_'+suffix,case(sql,mode,'CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT);'))
if __name__=='__main__':unittest.main()
