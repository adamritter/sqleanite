"""Additional source-guard, index, SQL scalar and valid-file combinations."""

def cases(seed):
    n=10+seed%300
    base=f"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n);INSERT INTO t VALUES(1,'a',{n}),(2,'B',{n+1}),(3,'c',NULL);"
    result=[]
    def add(name,sql,setup=base):result.append(dict(name=name,area='extended',setup=setup,sql=sql))
    for name,expr in {
        'current_date':'current_date IS NOT NULL',
        'current_time':'current_time IS NOT NULL',
        'current_timestamp':'current_timestamp IS NOT NULL',
        'datetime_now':"datetime('now') IS NOT NULL",
        'datetime_empty':'datetime() IS NOT NULL',
        'datetime_localtime':"datetime('2001-02-03 04:05:06','localtime')",
        'datetime_utc':"datetime('2001-02-03 04:05:06','utc')",
        'random_capability':'typeof(random())',
        'randomblob_capability':'length(randomblob(12))',
        'zeroblob':'length(zeroblob(12))',
        'sqlite_compileoption':"sqlite_compileoption_used('ENABLE_COLUMN_METADATA')",
        'math_sqrt':'sqrt(4)',
        'math_pow':'pow(2,3)',
        'math_log':'log(100)',
        'math_trig':'sin(0)',
        'total_null':'total(NULL)',
    }.items(): add('scalar_'+name,'SELECT '+expr+';')
    for name,ddl in {
        'desc':'CREATE INDEX ix ON t(n DESC);',
        'compound_desc':'CREATE INDEX ix ON t(v DESC,n ASC);',
        'expression_desc':'CREATE INDEX ix ON t(lower(v) DESC);',
        'unique_desc':'CREATE UNIQUE INDEX ix ON t(n DESC);',
    }.items():
        add('index_create_'+name,ddl+'PRAGMA index_xinfo(ix);UPDATE t SET n=n+10;SELECT * FROM t ORDER BY id;')
        add('index_open_'+name,'PRAGMA index_xinfo(ix);SELECT * FROM t ORDER BY id;',base+ddl)
    for name,ddl in {
        'unique_desc':'CREATE TABLE t(id INTEGER PRIMARY KEY,v,n,UNIQUE(v DESC,n));',
        'unique_nocase':'CREATE TABLE t(id INTEGER PRIMARY KEY,v,n,UNIQUE(v COLLATE NOCASE));',
        'strict_any':'CREATE TABLE t(id INTEGER PRIMARY KEY,v ANY,n INT) STRICT;',
        'stored_generated':'CREATE TABLE t(id INTEGER PRIMARY KEY,v,n GENERATED ALWAYS AS (length(v)) STORED);',
    }.items():
        insert="INSERT INTO t(id,v) VALUES(1,'0003');"
        add('declaration_'+name,ddl+insert+'SELECT *,typeof(v) FROM t;','')
    add('limit_scalar_subquery','SELECT id FROM t ORDER BY id LIMIT (SELECT 2);')
    add('limit_cte','WITH lim AS(SELECT 2 n) SELECT id FROM t ORDER BY id LIMIT (SELECT n FROM lim);')
    add('recursive_multiple_arms','WITH RECURSIVE c(x) AS(VALUES(1) UNION ALL SELECT x+1 FROM c WHERE x<3 UNION ALL SELECT x+2 FROM c WHERE x<3) SELECT x FROM c ORDER BY x;')
    add('view_column_list','CREATE VIEW vv(a,b) AS SELECT id,n FROM t;SELECT * FROM vv ORDER BY a;')
    add('trigger_shadowed_rowids',"CREATE TRIGGER tr AFTER UPDATE ON w BEGIN INSERT INTO t VALUES(10,new.rowid,4);END;UPDATE w SET v=v+1;SELECT * FROM t ORDER BY id;",base+"CREATE TABLE w(rowid,oid,_rowid_,v);INSERT INTO w VALUES('a','b','c',1);")
    add('wr_foreign_key_parent',"PRAGMA foreign_keys=ON;CREATE TABLE c(id INTEGER PRIMARY KEY,k REFERENCES w(k));INSERT INTO c VALUES(1,'a');SELECT * FROM c;",base+"CREATE TABLE w(k TEXT PRIMARY KEY,v) WITHOUT ROWID;INSERT INTO w VALUES('a',1);")
    add('compound_foreign_key_parent',"PRAGMA foreign_keys=ON;CREATE TABLE c(id INTEGER PRIMARY KEY,k REFERENCES p(k));INSERT INTO c VALUES(1,'a');SELECT * FROM c;",base+"CREATE TABLE p(k TEXT COLLATE NOCASE UNIQUE,v);INSERT INTO p VALUES('A',1);")
    add('wr_alter_add','ALTER TABLE w ADD extra DEFAULT 4;SELECT * FROM w;',base+"CREATE TABLE w(k TEXT PRIMARY KEY,v) WITHOUT ROWID;INSERT INTO w VALUES('a',1);")
    add('wr_alter_rename','ALTER TABLE w RENAME COLUMN k TO key;SELECT * FROM w;',base+"CREATE TABLE w(k TEXT PRIMARY KEY,v) WITHOUT ROWID;INSERT INTO w VALUES('a',1);")
    for policy in ('FAIL','ROLLBACK'):
        add('notnull_'+policy.lower(),f'CREATE TABLE nn(x NOT NULL ON CONFLICT {policy});INSERT INTO nn VALUES(1);SELECT * FROM nn;')
    for name,ddl in {
        'rtree':'CREATE VIRTUAL TABLE rt USING rtree(id,minX,maxX,minY,maxY);',
    }.items():add('virtual_'+name,ddl)
    # Use an explicitly ordered indexed predicate to avoid treating an optional
    # optimizer's unordered row order as a language conformance obligation.
    add('wr_covering_predicate',"SELECT k,v FROM w WHERE v>=1 ORDER BY k;", "CREATE TABLE w(k TEXT PRIMARY KEY,v) WITHOUT ROWID;INSERT INTO w VALUES('b',1),('a',2);CREATE INDEX ix ON w(v);")
    return result
