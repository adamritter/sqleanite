"""Non-bailing connection/API probes: real errors followed by visible state."""

def cases(seed):
    n=20+seed%800
    setup=f"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE,n);INSERT INTO t VALUES(1,'a',{n}),(2,'b',{n+1}),(3,'c',{n+2});CREATE TABLE log(id INTEGER PRIMARY KEY,v,n);"
    tail='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM t ORDER BY id;SELECT * FROM log ORDER BY id;'
    result=[]
    def add(name,sql,reference_error=False,base=setup):
        result.append(dict(name='effects_'+name,area='effects',setup=base,sql=sql+tail,api=True,reference_error=reference_error))
    for action in ('ABORT','FAIL','ROLLBACK','IGNORE','REPLACE'):
        for context,prefix,suffix in (
            ('autocommit','',''),
            ('transaction',"BEGIN;INSERT INTO log VALUES(8,'prior',8);",'COMMIT;'),
            ('savepoint',"SAVEPOINT s;INSERT INTO log VALUES(8,'prior',8);",'RELEASE s;'),
        ):
            add('insert_'+action.lower()+'_'+context,prefix+f"INSERT OR {action} INTO t VALUES(4,'d',4),(5,'a',5),(6,'f',6);"+tail+suffix,action in ('ABORT','FAIL','ROLLBACK'))
        add('update_'+action.lower(),f"UPDATE OR {action} t SET v='same';",action in ('ABORT','FAIL','ROLLBACK'))
    for action in ('ABORT','FAIL','ROLLBACK','IGNORE'):
        args="'stop'" if action!='IGNORE' else ''
        raise_sql=f"RAISE({action}{',' if args else ''}{args})"
        add('raise_'+action.lower(),f'CREATE TRIGGER tr AFTER UPDATE ON t WHEN new.id=2 BEGIN INSERT INTO log VALUES(new.id,new.v,new.n);SELECT {raise_sql};END;UPDATE t SET n=n+1;',action!='IGNORE')
    add('query_only',"PRAGMA query_only=ON;INSERT INTO t VALUES(4,'d',4);",True)
    add('upsert_trigger',"CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(new.id,new.v,new.n);END;INSERT INTO t VALUES(1,'a',99) ON CONFLICT(id) DO UPDATE SET n=excluded.n;")
    add('upsert_update_abort',"INSERT INTO t VALUES(4,'d',4),(1,'a',5) ON CONFLICT(id) DO UPDATE SET v='b';",True)
    add('deferred_commit_failure',"PRAGMA foreign_keys=ON;CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(pid REFERENCES p(id) DEFERRABLE INITIALLY DEFERRED);BEGIN;INSERT INTO c VALUES(9);COMMIT;SELECT * FROM c;ROLLBACK;SELECT * FROM c;",True)
    add('foreign_key_check',"CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(pid REFERENCES p(id));INSERT INTO c VALUES(9);PRAGMA foreign_key_check;")
    for key in ('rowid','_rowid_','oid'):
        add('wr_hidden_'+key,"CREATE TABLE w(k TEXT PRIMARY KEY,v) WITHOUT ROWID;INSERT INTO w VALUES('a',1);SELECT "+key+' FROM w;SELECT * FROM w;',True)
    return result
