"""Encoding, database-header and session SQL probes; no corruption oracle."""

def cases(seed):
    n=10+seed%1000
    base=f"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n);INSERT INTO t VALUES(1,'árvíz漢字',{n}),(2,'other',{n+1});"
    result=[]
    def add(name,setup,sql):result.append(dict(name=name,area='storage',setup=setup,sql=sql))
    for encoding in ('UTF-16le','UTF-16be'):
        prefix=f"PRAGMA encoding='{encoding}';"
        for op,sql in {
            'read':'SELECT id,hex(v),n FROM t ORDER BY id;',
            'insert':"INSERT INTO t VALUES(3,'é漢',3);SELECT id,hex(v),n FROM t ORDER BY id;",
            'update':"UPDATE t SET v='changed',n=n+1 WHERE id=1;SELECT id,hex(v),n FROM t ORDER BY id;",
            'delete':'DELETE FROM t WHERE id=1;SELECT * FROM t ORDER BY id;',
            'schema':'ALTER TABLE t ADD extra DEFAULT 3;SELECT * FROM t ORDER BY id;',
            'wr_read':'SELECT id,hex(v),n FROM t ORDER BY id;',
        }.items():
            setup=base.replace('n);','n) WITHOUT ROWID;') if op=='wr_read' else base
            add(encoding.lower().replace('-','')+'_'+op,prefix+setup,sql)
        add(encoding.lower().replace('-','')+'_create','',prefix+base+'PRAGMA encoding;SELECT id,hex(v),n FROM t ORDER BY id;')
    for name,sql in {
        'pragma_encoding':"PRAGMA encoding;",
        'pragma_application_id':'PRAGMA application_id=123456;PRAGMA application_id;',
        'pragma_schema_version':'PRAGMA schema_version=123;PRAGMA schema_version;',
        'pragma_page_size':'PRAGMA page_size;',
        'pragma_page_count':'PRAGMA page_count;',
        'pragma_freelist_count':'PRAGMA freelist_count;',
        'pragma_auto_vacuum':'PRAGMA auto_vacuum;',
        'pragma_database_list':'PRAGMA database_list;',
        'pragma_foreign_key_list':'PRAGMA foreign_key_list(t);',
        'pragma_function_list':"SELECT name,narg FROM pragma_function_list() WHERE name IN ('abs','sum','json') ORDER BY name,narg;",
        'pragma_collation_list':'PRAGMA collation_list;',
        'pragma_reverse_unordered':'PRAGMA reverse_unordered_selects=ON;SELECT id FROM t;',
        'pragma_query_only':'PRAGMA query_only=ON;SELECT * FROM t ORDER BY id;',
        'pragma_read_uncommitted':'PRAGMA read_uncommitted=ON;PRAGMA read_uncommitted;',
        'vacuum':'VACUUM;SELECT * FROM t ORDER BY id;',
        'analyze':'ANALYZE;SELECT tbl,idx,stat FROM sqlite_stat1 ORDER BY tbl,idx;',
        'reindex':'REINDEX;SELECT * FROM t ORDER BY id;',
        'attach':"ATTACH ':memory:' AS other;CREATE TABLE other.a(x);INSERT INTO other.a VALUES(1);SELECT * FROM other.a;DETACH other;",
    }.items():
        # database_list contains the temporary filename: test schema names only.
        if name=='pragma_database_list':sql='SELECT seq,name FROM pragma_database_list() ORDER BY seq;'
        add(name,base,sql)
    for size in (512,1024,8192,65536):
        add('geometry_'+str(size),f'PRAGMA page_size={size};'+base,'UPDATE t SET n=n+1;SELECT * FROM t ORDER BY id;')
    for vacuum in ('FULL','INCREMENTAL'):
        add('auto_vacuum_'+vacuum.lower(),f'PRAGMA auto_vacuum={vacuum};'+base,'DELETE FROM t WHERE id=1;SELECT * FROM t;')
    for reserve in (16,32):
        add('reserved_bytes_'+str(reserve), f'.filectrl reserve_bytes {reserve}\nVACUUM;'+base,
            'UPDATE t SET n=n+1;SELECT * FROM t ORDER BY id;')
    for encoding in ('UTF-8','UTF-16le','UTF-16be'):
        for wr in (False,True):
            for op in ('read','update'):
                setup=base.replace('n);','n) WITHOUT ROWID;') if wr else base
                name='wal_overlay_'+encoding.lower().replace('-','')+('_wr' if wr else '_rowid')+'_'+op
                sql=('UPDATE t SET n=n+1;' if op=='update' else '')+'SELECT id,hex(v),n FROM t ORDER BY id;'
                result.append(dict(name=name,area='storage',setup=setup,sql=sql,wal_fixture=True,encoding=encoding))
    return result
