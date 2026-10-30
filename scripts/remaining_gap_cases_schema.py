"""Schema/write hypotheses; reference success is required for every probe."""

def cases(seed):
    n = 17 + seed % 700
    base = f"CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n);INSERT INTO t VALUES(1,'a',{n}),(2,'b',{n+1}),(3,'c',{n+2});"
    rows = 'SELECT * FROM t ORDER BY id;'
    result = []
    def add(name, setup, sql):
        result.append(dict(name=name, area='schema', setup=setup, sql=sql))
    for kind, ddl in {
        'inline_desc_integer': 'CREATE TABLE t(id INTEGER PRIMARY KEY DESC,v);',
        'inline_asc_integer': 'CREATE TABLE t(id INTEGER PRIMARY KEY ASC,v);',
        'inline_desc_text': 'CREATE TABLE t(id TEXT PRIMARY KEY DESC,v);',
        'table_desc_text': 'CREATE TABLE t(id TEXT,v,PRIMARY KEY(id DESC));',
        'composite_desc': 'CREATE TABLE t(id TEXT,v,PRIMARY KEY(id DESC,v));',
        'virtual_generated': 'CREATE TABLE t(id INTEGER PRIMARY KEY,v,g AS (v+1) VIRTUAL);',
        'default_expression': 'CREATE TABLE t(id INTEGER PRIMARY KEY,v DEFAULT (abs(-3)));',
        'named_column_constraint': 'CREATE TABLE t(id INTEGER CONSTRAINT pk PRIMARY KEY,v CONSTRAINT uq UNIQUE);',
    }.items():
        add('ddl_'+kind, '', ddl+'INSERT INTO t(id,v) VALUES(1,7),(2,8);SELECT * FROM t ORDER BY id;PRAGMA index_list(t);')
    for action in ('IGNORE','REPLACE','FAIL','ROLLBACK'):
        add('declared_unique_'+action.lower(), '',
            f'CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT UNIQUE ON CONFLICT {action});'
            + "INSERT INTO t VALUES(1,'a');SELECT * FROM t;")
        add('wr_primary_'+action.lower(), '',
            f'CREATE TABLE t(id TEXT PRIMARY KEY ON CONFLICT {action},v) WITHOUT ROWID;'
            + "INSERT INTO t VALUES('a',1);SELECT * FROM t;")
    for index, ddl in {
        'partial':'CREATE INDEX ix ON t(n) WHERE n>0;',
        'expression':'CREATE INDEX ix ON t(lower(v));',
        'compound':'CREATE INDEX ix ON t(v,n);',
        'unique':'CREATE UNIQUE INDEX ix ON t(v,n);',
    }.items():
        for op, sql in {
            'add':'ALTER TABLE t ADD extra DEFAULT 4;',
            'rename_table':'ALTER TABLE t RENAME TO renamed;SELECT * FROM renamed ORDER BY id;',
            'rename_column':'ALTER TABLE t RENAME COLUMN v TO value;',
            'drop_unreferenced':'ALTER TABLE t DROP COLUMN id;',
        }.items():
            # A primary-key column cannot be dropped in native SQLite.
            if op == 'drop_unreferenced':
                add('alter_'+index+'_drop_unreferenced',base.replace('n);','n,extra);').replace(f"{n})",f"{n},0)").replace(f"{n+1})",f"{n+1},0)").replace(f"{n+2})",f"{n+2},0)")+ddl,'ALTER TABLE t DROP COLUMN extra;')
            else: add('alter_'+index+'_'+op,base+ddl,sql)
    trigger='CREATE TABLE log(x);CREATE TRIGGER tr AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(new.n);END;'
    for name,sql in {
        'rename_table':'ALTER TABLE t RENAME TO renamed;UPDATE renamed SET n=n+1;SELECT * FROM log ORDER BY x;',
        'rename_column':'ALTER TABLE t RENAME COLUMN n TO num;UPDATE t SET num=num+1;SELECT * FROM log ORDER BY x;',
        'add_column':'ALTER TABLE t ADD extra DEFAULT 4;UPDATE t SET n=n+1;SELECT * FROM log ORDER BY x;',
        'drop_column':'ALTER TABLE t DROP COLUMN v;UPDATE t SET n=n+1;SELECT * FROM log ORDER BY x;',
    }.items(): add('alter_trigger_'+name,base+trigger,sql)
    for name,extra,sql in [
        ('compound','CREATE UNIQUE INDEX ux ON t(v,n);',f"INSERT INTO t VALUES(4,'a',{n}) ON CONFLICT(v,n) DO UPDATE SET n=excluded.n+20;"),
        ('partial','CREATE UNIQUE INDEX ux ON t(v) WHERE n>0;',"INSERT INTO t VALUES(4,'a',2) ON CONFLICT(v) WHERE n>0 DO UPDATE SET n=excluded.n;"),
        ('expression','CREATE UNIQUE INDEX ux ON t(lower(v));',"INSERT INTO t VALUES(4,'A',2) ON CONFLICT(lower(v)) DO UPDATE SET n=excluded.n;"),
        ('collated','CREATE UNIQUE INDEX ux ON t(v COLLATE NOCASE);',"INSERT INTO t VALUES(4,'A',2) ON CONFLICT(v COLLATE NOCASE) DO UPDATE SET n=excluded.n;"),
        ('select','',"INSERT INTO t SELECT 1,'z',99 WHERE 1 ON CONFLICT(id) DO UPDATE SET n=excluded.n;"),
        ('trigger',trigger,"INSERT INTO t VALUES(1,'z',99) ON CONFLICT(id) DO UPDATE SET n=excluded.n;SELECT * FROM log;"),
    ]: add('upsert_'+name,base+extra,sql+rows)
    add('upsert_without_rowid',"CREATE TABLE t(id TEXT PRIMARY KEY,v,n) WITHOUT ROWID;INSERT INTO t VALUES('a','b',1);","INSERT INTO t VALUES('a','c',2) ON CONFLICT(id) DO UPDATE SET n=excluded.n;SELECT * FROM t;")
    for action in ('FAIL','ROLLBACK'):
        add('insert_or_'+action.lower(),base,f"INSERT OR {action} INTO t VALUES(4,'d',4);"+rows)
        add('update_or_'+action.lower(),base,f'UPDATE OR {action} t SET n=n+1;'+rows)
    add('recursive_replace_auxiliary',base+"CREATE UNIQUE INDEX ux ON t(v,n);CREATE TABLE log(x);CREATE TRIGGER tr AFTER DELETE ON t BEGIN INSERT INTO log VALUES(old.id);END;",f"PRAGMA recursive_triggers=ON;INSERT OR REPLACE INTO t VALUES(4,'a',{n});SELECT * FROM log;"+rows)
    add('instead_of_insert',base+'CREATE VIEW vw AS SELECT * FROM t;',"CREATE TRIGGER tr INSTEAD OF INSERT ON vw BEGIN INSERT INTO t VALUES(new.id,new.v,new.n);END;INSERT INTO vw VALUES(4,'d',4);"+rows)
    add('instead_of_update',base+'CREATE VIEW vw AS SELECT * FROM t;',"CREATE TRIGGER tr INSTEAD OF UPDATE ON vw BEGIN UPDATE t SET n=new.n WHERE id=old.id;END;UPDATE vw SET n=n+1;"+rows)
    add('temp_trigger',base,"CREATE TEMP TRIGGER tr AFTER UPDATE ON main.t BEGIN UPDATE t SET v='changed' WHERE id=new.id;END;UPDATE t SET n=n+1;"+rows)
    add('temp_table',base,'CREATE TEMP TABLE tt(x);INSERT INTO tt VALUES(7);SELECT * FROM tt;')
    add('temp_view',base,'CREATE TEMP VIEW tv AS SELECT * FROM t;SELECT * FROM tv ORDER BY id;')
    add('fk_composite',"CREATE TABLE p(a,b,PRIMARY KEY(a,b));INSERT INTO p VALUES(1,2);",'PRAGMA foreign_keys=ON;CREATE TABLE c(a,b,FOREIGN KEY(a,b) REFERENCES p(a,b));INSERT INTO c VALUES(1,2);SELECT * FROM c;')
    for action in ('CASCADE','SET NULL','SET DEFAULT','RESTRICT','NO ACTION'):
        event='UPDATE' if action in ('RESTRICT','NO ACTION') else 'DELETE'
        command='UPDATE p SET id=2;' if event=='UPDATE' else 'DELETE FROM p;'
        # Successful action cases; RESTRICT/NO ACTION are tested with no child.
        child='' if event=='UPDATE' else 'INSERT INTO c VALUES(1,1);'
        add('fk_'+action.lower().replace(' ','_'), 'CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);',
            f'PRAGMA foreign_keys=ON;CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id) ON {event} {action});'+child+command+'SELECT * FROM c;SELECT * FROM p;')
    for name,sql in {
        'deferred':'BEGIN;INSERT INTO c VALUES(1,9);INSERT INTO p VALUES(9);COMMIT;',
        'defer_pragma':'PRAGMA defer_foreign_keys=ON;BEGIN;INSERT INTO c VALUES(1,9);INSERT INTO p VALUES(9);COMMIT;',
    }.items():
        fk='DEFERRABLE INITIALLY DEFERRED' if name=='deferred' else ''
        add('fk_'+name,f'CREATE TABLE p(id INTEGER PRIMARY KEY);CREATE TABLE c(id INTEGER PRIMARY KEY,pid REFERENCES p(id) {fk});','PRAGMA foreign_keys=ON;'+sql+'SELECT * FROM c;')
    for op in ('UPDATE','DELETE'):
        body='UPDATE w SET n=(SELECT new.n) WHERE k=(SELECT old.v);' if op=='UPDATE' else 'DELETE FROM w WHERE k=(SELECT old.v);'
        add('wr_captured_trigger_'+op.lower(),base+"CREATE TABLE w(k TEXT PRIMARY KEY,n) WITHOUT ROWID;INSERT INTO w VALUES('a',10),('b',20);"+f'CREATE TRIGGER tr AFTER UPDATE ON t BEGIN {body} END;', 'UPDATE t SET n=n+1 WHERE id=1;SELECT * FROM w ORDER BY k;')
    return result
