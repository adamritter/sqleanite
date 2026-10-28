#!/usr/bin/env python3
"""Persistent trigger declarations and catalog transactions in public modes.
Trigger firing has its own feature regressions; these compare actual source,
identity, schema cookie, rollback, reopen and physical integrity for the catalog.
"""
import os,random,unittest
from test_check_add_column import case
class TriggerCatalog(unittest.TestCase):pass
SETUP="CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);INSERT INTO t VALUES(1,'a',2);CREATE TABLE log(x);CREATE VIEW q AS SELECT id,v,n FROM t;"
TAIL="SELECT name,tbl_name,rootpage,sql FROM sqlite_schema WHERE type='trigger' ORDER BY rowid;PRAGMA schema_version;"
UPDATE="CREATE TRIGGER note AFTER UPDATE ON t BEGIN UPDATE t SET v='triggered' WHERE id=new.id; END;"
QUERIES={
 'after_update':UPDATE+TAIL,
 'visible_create_transaction':"BEGIN;"+UPDATE+"SELECT name FROM sqlite_schema WHERE type='trigger';ROLLBACK;"+TAIL,
 'visible_drop_transaction':UPDATE+"BEGIN;DROP TRIGGER note;SELECT count(*) FROM sqlite_schema WHERE type='trigger';ROLLBACK;"+TAIL,
 'visible_savepoint':"SAVEPOINT s;"+UPDATE+"SELECT name FROM sqlite_schema WHERE type='trigger';ROLLBACK TO s;SELECT count(*) FROM sqlite_schema WHERE type='trigger';RELEASE s;"+TAIL,
 'visible_owner_drop':UPDATE+"BEGIN;DROP TABLE t;SELECT count(*) FROM sqlite_schema WHERE type='trigger';ROLLBACK;"+TAIL,
 'if_not_exists_wrong_timing':UPDATE+"CREATE TRIGGER IF NOT EXISTS note BEFORE UPDATE ON q BEGIN SELECT new.id; END;"+TAIL,
 'reserved_missing_owner':"CREATE TRIGGER sqlite_bad AFTER UPDATE ON missing BEGIN SELECT new.id; END;",
 'reserved_name':"CREATE TRIGGER sqlite_bad AFTER UPDATE ON t BEGIN SELECT new.id; END;",
 'owner_case':"CREATE TRIGGER note AFTER UPDATE ON T BEGIN SELECT new.id; END;"+TAIL,
 'view_owner_case':"CREATE TRIGGER note INSTEAD OF DELETE ON Q BEGIN SELECT old.id; END;"+TAIL,
 'quoted_dot':"CREATE TRIGGER \"odd.name\" AFTER UPDATE ON t BEGIN SELECT new.id; END;"+TAIL,
 'drop_quoted_dot':"CREATE TRIGGER \"odd.name\" AFTER UPDATE ON t BEGIN SELECT new.id; END;DROP TRIGGER \"odd.name\";"+TAIL,
 'view_name_namespace':"CREATE TRIGGER q AFTER UPDATE ON t BEGIN SELECT new.id; END;"+TAIL,
 'duplicate_case':UPDATE+"CREATE TRIGGER NOTE AFTER INSERT ON t BEGIN SELECT new.id; END;",
 'after_insert':"CREATE TRIGGER note AFTER INSERT ON t BEGIN INSERT INTO log VALUES(new.id); END;"+TAIL,
 'after_delete':"CREATE TRIGGER note AFTER DELETE ON t BEGIN INSERT INTO log VALUES(old.id); END;"+TAIL,
 'default_before':"CREATE TRIGGER note INSERT ON t BEGIN SELECT new.id; END;"+TAIL,
 'explicit_before':"CREATE TRIGGER note BEFORE DELETE ON t BEGIN SELECT old.id; END;"+TAIL,
 'instead_view':"CREATE TRIGGER note INSTEAD OF UPDATE ON q BEGIN UPDATE t SET v=new.v WHERE id=old.id; END;"+TAIL,
 'when':"CREATE TRIGGER note AFTER UPDATE ON t WHEN old.n<>new.n BEGIN SELECT new.n; END;"+TAIL,
 'update_of':"CREATE TRIGGER note AFTER UPDATE OF n,v ON t BEGIN SELECT new.n; END;"+TAIL,
 'update_of_unknown':"CREATE TRIGGER note AFTER UPDATE OF missing,n ON t BEGIN SELECT new.n; END;"+TAIL,
 'each_row':"CREATE TRIGGER note AFTER UPDATE ON t FOR EACH ROW BEGIN SELECT new.id; END;"+TAIL,
 'multiple_body':"CREATE TRIGGER note AFTER UPDATE ON t BEGIN INSERT INTO log VALUES(old.id);INSERT INTO log VALUES(new.id); END;"+TAIL,
 'quoted':"CREATE TRIGGER \"odd trigger\" AFTER UPDATE ON t BEGIN SELECT new.\"v\"; END;"+TAIL,
 'main_name':"CREATE TRIGGER main.note AFTER UPDATE ON t BEGIN SELECT new.id; END;"+TAIL,
 'main_owner':"CREATE TRIGGER note AFTER UPDATE ON main.t BEGIN SELECT new.id; END;"+TAIL,
 'source_trivia':"create /*keep*/ trigger if not exists note after update on t begin select ';',new.id; --body\n end;"+TAIL,
 'if_not_exists':UPDATE+"CREATE TRIGGER IF NOT EXISTS note AFTER DELETE ON t BEGIN SELECT old.id; END;"+TAIL,
 'if_not_exists_missing_owner':UPDATE+"CREATE TRIGGER IF NOT EXISTS note AFTER DELETE ON missing BEGIN SELECT old.id; END;"+TAIL,
 'table_name_namespace':"CREATE TRIGGER t AFTER UPDATE ON t BEGIN SELECT new.id; END;"+TAIL,
 'index_name_namespace':"CREATE INDEX note ON t(n);"+UPDATE+TAIL,
 'drop':UPDATE+"DROP TRIGGER note;UPDATE t SET n=3;"+TAIL,
 'drop_qualified':UPDATE+"DROP TRIGGER main.note;"+TAIL,
 'drop_absent':"DROP TRIGGER IF EXISTS absent;"+TAIL,
 'drop_table':UPDATE+"DROP TABLE t;"+TAIL,
 'drop_view':"CREATE TRIGGER note INSTEAD OF DELETE ON q BEGIN DELETE FROM t WHERE id=old.id; END;DROP VIEW q;"+TAIL,
 'rollback_create':"BEGIN;"+UPDATE+"ROLLBACK;"+TAIL,
 'rollback_drop':UPDATE+"BEGIN;DROP TRIGGER note;ROLLBACK;"+TAIL,
 'savepoint':"SAVEPOINT s;"+UPDATE+"ROLLBACK TO s;RELEASE s;"+TAIL,
 'release':"SAVEPOINT s;"+UPDATE+"RELEASE s;"+TAIL,
 'catalog_identity':UPDATE+"CREATE VIEW r AS SELECT * FROM t;DROP TRIGGER note;CREATE TRIGGER other AFTER INSERT ON t BEGIN SELECT new.id; END;"+TAIL,
 'deferred_invalid_body':"CREATE TRIGGER note AFTER INSERT ON t BEGIN SELECT new.missing,absent(new.id); END;"+TAIL,
 'missing_owner':"CREATE TRIGGER note AFTER UPDATE ON missing BEGIN SELECT new.id; END;",
 'before_view_error':"CREATE TRIGGER note BEFORE UPDATE ON q BEGIN SELECT new.id; END;",
 'instead_table_error':"CREATE TRIGGER note INSTEAD OF UPDATE ON t BEGIN SELECT new.id; END;",
 'duplicate':UPDATE+UPDATE,
 'missing_drop_error':"DROP TRIGGER absent;",
}
for name,sql in QUERIES.items():
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(TriggerCatalog,'test_'+name+'_'+suffix,case(sql,mode,SETUP))
rng=random.Random(int(os.environ.get('SQLEANITE_TRIGGER_CATALOG_SEED','1103701')))
for index in range(4):
 name='fresh_'+str(rng.randrange(1000000000));number=rng.randrange(1000000)
 text='Árvíztűrő_'+str(rng.randrange(1000000))
 sql=f"CREATE TRIGGER {name} AFTER UPDATE OF n ON t WHEN new.n>{number} BEGIN SELECT '{text}',old.id; END;"+TAIL
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(TriggerCatalog,f'test_fresh_{index}_{suffix}',case(sql,mode,SETUP))
for value in [-1,2147483647,-2147483648]:
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setattr(TriggerCatalog,f'test_cookie_{value}_{suffix}',case(UPDATE+TAIL+"PRAGMA temp.schema_version;",mode,SETUP+f'PRAGMA schema_version={value};'))
for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
 setup=SETUP+"CREATE TRIGGER gate BEFORE INSERT ON T BEGIN SELECT RAISE(ABORT,'blocked'); END;"
 setattr(TriggerCatalog,'test_existing_raise_'+suffix,case('SELECT id,v,n FROM t;',mode,setup))
 setattr(TriggerCatalog,'test_cookie_unknown_schema_'+suffix,case('PRAGMA absent.schema_version;',mode,SETUP))
for action in ['ABORT','FAIL','ROLLBACK']:
 for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
  setup=SETUP+f"CREATE TRIGGER action_gate BEFORE INSERT ON t BEGIN SELECT RAISE({action},'blocked '||new.id); END;"
  setattr(TriggerCatalog,f'test_existing_raise_{action}_{suffix}',case('SELECT id,v,n FROM t;',mode,setup))
for suffix,mode in [('rollback','--verified-file'),('wal','--verified-wal-file')]:
 setup=SETUP+"CREATE TRIGGER ignore_gate BEFORE INSERT ON t BEGIN SELECT RAISE(IGNORE); END;"
 setattr(TriggerCatalog,'test_existing_raise_IGNORE_'+suffix,case('SELECT id,v,n FROM t;',mode,setup))
 setattr(TriggerCatalog,'test_raise_outside_'+suffix,case("SELECT RAISE(ABORT,'blocked');",mode,SETUP))
 setattr(TriggerCatalog,'test_private_raise_'+suffix,case("SELECT __SQLEAN_RAISE_ABORT('blocked');",mode,SETUP))
 payload='payload_'+str(rng.randrange(1000000))+'_'+'Árvíztűrő;END;'*600
 sql="CREATE TRIGGER overflow_note AFTER UPDATE ON t BEGIN SELECT '"+payload+"'; END;SELECT name,length(sql) FROM sqlite_schema WHERE type='trigger';PRAGMA schema_version;"
 setattr(TriggerCatalog,'test_overflow_'+suffix,case(sql,mode,SETUP))
if __name__=='__main__':unittest.main()
