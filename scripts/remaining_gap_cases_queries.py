"""Query hypotheses with explicit ordering except tests of execution effects."""

def cases(seed):
    n=2+seed%9
    base=f"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n);INSERT INTO t VALUES(1,'a',{n}),(2,'a',{n}),(3,'b',{n+1}),(4,'c',NULL);"
    queries={
        'join_right':'SELECT a.id,b.id FROM t a RIGHT JOIN t b ON a.id=b.id+1 ORDER BY b.id;',
        'join_full':'SELECT a.id,b.id FROM t a FULL OUTER JOIN t b ON a.id=b.id+1 ORDER BY a.id,b.id;',
        'join_three':'SELECT a.id,b.id,c.id FROM t a JOIN t b ON a.id=b.id JOIN t c ON b.id=c.id ORDER BY a.id;',
        'join_natural':'SELECT * FROM t a NATURAL JOIN t b ORDER BY id;',
        'aggregate_bare_min':'SELECT id,v,min(n) FROM t;',
        'aggregate_bare_max':'SELECT id,v,max(n) FROM t;',
        'aggregate_bare_group':'SELECT v,id,sum(n) FROM t GROUP BY v ORDER BY v;',
        'aggregate_scalar_subquery':'SELECT sum(n),(SELECT max(id) FROM t) FROM t;',
        'aggregate_filter':'SELECT sum(n) FILTER(WHERE id>1),count(*) FILTER(WHERE n IS NULL) FROM t;',
        'aggregate_order':'SELECT group_concat(id ORDER BY id DESC) FROM t;',
        'aggregate_distinct':'SELECT group_concat(DISTINCT v) FROM t;',
        'aggregate_having_subquery':'SELECT v,sum(n) FROM t GROUP BY v HAVING sum(n)>(SELECT min(n) FROM t) ORDER BY v;',
        'window_range':'SELECT id,sum(n) OVER(ORDER BY n RANGE BETWEEN 1 PRECEDING AND CURRENT ROW) FROM t ORDER BY id;',
        'window_groups':'SELECT id,sum(n) OVER(ORDER BY n GROUPS BETWEEN 1 PRECEDING AND CURRENT ROW) FROM t ORDER BY id;',
        'window_exclude_current':'SELECT id,sum(n) OVER(ORDER BY id ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW EXCLUDE CURRENT ROW) FROM t ORDER BY id;',
        'window_exclude_ties':'SELECT id,sum(n) OVER(ORDER BY n ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW EXCLUDE TIES) FROM t ORDER BY id;',
        'window_named':'SELECT id,row_number() OVER win FROM t WINDOW win AS (ORDER BY n,id) ORDER BY id;',
        'window_chained':'SELECT id,sum(n) OVER(win ROWS BETWEEN 1 PRECEDING AND CURRENT ROW) FROM t WINDOW win AS (ORDER BY id) ORDER BY id;',
        'window_grouped':'SELECT v,sum(sum(n)) OVER(ORDER BY v) FROM t GROUP BY v ORDER BY v;',
        'window_join':'SELECT a.id,row_number() OVER(ORDER BY a.id) FROM t a JOIN t b ON a.id=b.id ORDER BY a.id;',
        'window_filter':'SELECT id,sum(n) FILTER(WHERE id>1) OVER(ORDER BY id) FROM t ORDER BY id;',
        'window_ntile':'SELECT id,ntile(3) OVER(ORDER BY id) FROM t ORDER BY id;',
        'window_nth':'SELECT id,nth_value(n,2) OVER(ORDER BY id ROWS BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING) FROM t ORDER BY id;',
        'recursive_order':'WITH RECURSIVE c(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM c WHERE x<5 ORDER BY 1 DESC) SELECT x FROM c;',
        'recursive_limit':'WITH RECURSIVE c(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM c LIMIT 5) SELECT x FROM c ORDER BY x;',
        'recursive_offset':'WITH RECURSIVE c(x) AS (VALUES(1) UNION ALL SELECT x+1 FROM c LIMIT 4 OFFSET 2) SELECT x FROM c ORDER BY x;',
        'cte_materialized':'WITH c AS MATERIALIZED (SELECT * FROM t) SELECT * FROM c ORDER BY id;',
        'cte_not_materialized':'WITH c AS NOT MATERIALIZED (SELECT * FROM t) SELECT * FROM c ORDER BY id;',
        'cte_insert':'WITH c AS (SELECT id+10,v,n FROM t) INSERT INTO t SELECT * FROM c;SELECT * FROM t ORDER BY id;',
        'cte_update':'WITH c AS (SELECT max(n) x FROM t) UPDATE t SET n=(SELECT x FROM c);SELECT * FROM t ORDER BY id;',
        'cte_delete':'WITH c AS (SELECT min(id) x FROM t) DELETE FROM t WHERE id=(SELECT x FROM c);SELECT * FROM t ORDER BY id;',
        'row_value_equal':"SELECT id FROM t WHERE (v,n)=('a',"+str(n)+') ORDER BY id;',
        'row_value_in':'SELECT id FROM t WHERE (v,n) IN (SELECT v,n FROM t WHERE id=1) ORDER BY id;',
        'row_value_update':'UPDATE t SET (v,n)=(SELECT v,n FROM t WHERE id=3) WHERE id=1;SELECT * FROM t ORDER BY id;',
        'update_from':'UPDATE t SET n=q.n+1 FROM (SELECT id,n FROM t) q WHERE t.id=q.id;SELECT * FROM t ORDER BY id;',
        'index_hint':'SELECT id FROM t INDEXED BY by_n WHERE n>0 ORDER BY id;',
        'not_indexed':'SELECT id FROM t NOT INDEXED WHERE n>0 ORDER BY id;',
        'sort_nulls_first':'SELECT id,n FROM t ORDER BY n DESC NULLS FIRST,id;',
        'sort_nulls_last':'SELECT id,n FROM t ORDER BY n ASC NULLS LAST,id;',
        'collation_using':"SELECT a.id,b.id FROM t a JOIN t b USING(v) ORDER BY a.id,b.id;",
        'correlated_group':'SELECT a.id,(SELECT sum(b.n) FROM t b GROUP BY b.v HAVING b.v=a.v) FROM t a ORDER BY a.id;',
        'correlated_compound':'SELECT a.id,(SELECT b.n FROM t b WHERE b.id=a.id UNION ALL SELECT 99 LIMIT 1) FROM t a ORDER BY a.id;',
        'json_each_lateral':"SELECT t.id,j.value FROM t,json_each(json_array(t.n,t.id)) j ORDER BY t.id,j.key;",
        'json_tree_lateral':"SELECT t.id,j.fullkey,j.atom FROM t JOIN json_tree(json_object('n',t.n)) j WHERE j.type<>'object' ORDER BY t.id,j.id;",
        'jsonb':'SELECT hex(jsonb(\'{"a":1}\'));',
        'jsonb_extract':'SELECT jsonb_extract(jsonb(\'{"a":1}\'),\'$.a\');',
        'json_error_position':"SELECT json_error_position('{bad}');",
        'json_valid_flags':"SELECT json_valid('{a:1}',2);",
        'string_concat':"SELECT concat('a',NULL,'b'),concat_ws('-',1,NULL,2);",
        'unhex':"SELECT hex(unhex('4142'));",
        'unistr':"SELECT unistr('\\0041'),unistr_quote(char(1));",
        'octet_length':"SELECT octet_length('árvíz');",
        'format':"SELECT format('%04d:%s',7,'x');",
        'likely':"SELECT likely(1),unlikely(0),likelihood(1,0.5);",
        'sqlite_offset':'SELECT sqlite_offset(n) IS NULL FROM t ORDER BY id;',
        'like_escape':"SELECT 'a_b' LIKE 'a!_b' ESCAPE '!';",
        'numeric_literals':'SELECT 1_000,0x10,1e309,-9223372036854775809;',
        'blob_cast':'SELECT hex(CAST(x\'80ff\' AS TEXT)),typeof(CAST(x\'80ff\' AS TEXT));',
    }
    result=[]
    for name,sql in queries.items():
        setup=base
        if name in ('collation_using',):setup=base.replace('v TEXT','v TEXT COLLATE NOCASE')
        if name=='index_hint':setup+='CREATE INDEX by_n ON t(n);'
        result.append(dict(name=name,area='query',setup=setup,sql=sql))
    return result
