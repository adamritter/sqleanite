#!/usr/bin/env python3
"""Same-connection Core API continuation against the pinned non-bailing shell."""
import os,random,re,subprocess,unittest
from pathlib import Path
from test_pragma_tables import SQLITE,ROOT
from test_check_add_column import statement_lines
from test_trigger_execution import SETUP
BINARY=ROOT/'.lake/build/bin/sqleanite_tests'
TAIL='SELECT changes(),total_changes(),last_insert_rowid();SELECT * FROM t ORDER BY id;SELECT * FROM log ORDER BY id;'
class ErrorEffects(unittest.TestCase):pass
Q={
 'before_update':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;SELECT RAISE(ABORT,'stop');END;UPDATE t SET n=n+1;"+TAIL,
 'after_update':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1;SELECT RAISE(ABORT,'stop');END;UPDATE t SET n=n+1;"+TAIL,
 'before_insert_rowid':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(9,'body',9);SELECT RAISE(ABORT,'stop');END;INSERT INTO t VALUES(4,'d',4);"+TAIL,
 'after_insert_rowid':"CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO log VALUES(9,'body',9);SELECT RAISE(ABORT,'stop');END;INSERT INTO t VALUES(4,'d',4);"+TAIL,
 'multiple_rows':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1;SELECT CASE WHEN new.id=2 THEN RAISE(ABORT,'stop') END;END;UPDATE t SET n=n+10;"+TAIL,
 'nested_abort':"CREATE TABLE detail(n);CREATE TRIGGER b AFTER UPDATE ON log BEGIN INSERT INTO detail VALUES(new.n);SELECT RAISE(ABORT,'nested');END;CREATE TRIGGER a AFTER UPDATE ON t BEGIN UPDATE log SET n=n+1;END;UPDATE t SET n=n+1;"+TAIL+'SELECT * FROM detail;',
 'transaction':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;SELECT RAISE(ABORT,'stop');END;BEGIN;INSERT INTO t VALUES(4,'d',4);UPDATE t SET n=n+1 WHERE id=1;"+TAIL+'COMMIT;'+TAIL,
 'savepoint':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;SELECT RAISE(ABORT,'stop');END;SAVEPOINT s;INSERT INTO t VALUES(4,'d',4);UPDATE t SET n=n+1 WHERE id=1;"+TAIL+'ROLLBACK TO s;RELEASE s;'+TAIL,
 'preparation':"CREATE TRIGGER a AFTER UPDATE ON t BEGIN SELECT absent(new.n);END;UPDATE t SET n=n+1 WHERE 0;"+TAIL,
 'when_error':"CREATE TRIGGER b BEFORE UPDATE ON t WHEN RAISE(ABORT,'when') BEGIN SELECT new.id;END;UPDATE t SET n=n+1;"+TAIL,
 'replace_delete':"PRAGMA recursive_triggers=ON;CREATE TRIGGER b BEFORE DELETE ON t BEGIN UPDATE log SET n=n+1;SELECT RAISE(ABORT,'delete');END;INSERT OR REPLACE INTO t VALUES(2,'d',4);"+TAIL,
 'lazy_success':"CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;SELECT CASE WHEN new.n<0 THEN RAISE(ABORT,'stop') END;END;UPDATE t SET n=n+1;"+TAIL,
}
Q.update({
 'after_insert_returning_error':"CREATE TRIGGER a AFTER INSERT ON t BEGIN SELECT new.id;END;INSERT INTO t VALUES(4,'d',4) RETURNING abs(-9223372036854775808);"+TAIL,
 'before_insert_returning_error':"CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=n+1;END;INSERT INTO t VALUES(4,'d',4) RETURNING abs(-9223372036854775808);"+TAIL,
})
Q['depth_failure_effects']="PRAGMA recursive_triggers=ON;CREATE TRIGGER a AFTER UPDATE ON t WHEN new.n<1001 BEGIN INSERT INTO log(v,n) VALUES(new.v,new.n);UPDATE t SET n=n+1 WHERE id=new.id;END;UPDATE t SET n=1 WHERE id=1;"+TAIL+'PRAGMA recursive_triggers;'
Q.update({
 'ordinary_constraint':"INSERT INTO t VALUES(1,'duplicate',4);"+TAIL,
 'ordinary_returning':"INSERT INTO t VALUES(4,'d',4) RETURNING abs(-9223372036854775808);"+TAIL,
 'ordinary_update_error':"UPDATE t SET n=abs(-9223372036854775808);"+TAIL,
 'ordinary_delete_error':"DELETE FROM t WHERE abs(-9223372036854775808);"+TAIL,
 'ordinary_insert_error':"INSERT INTO t VALUES(4,'d',abs(-9223372036854775808));"+TAIL,
 'ordinary_preparation':"UPDATE t SET n=absent(n) WHERE 0;"+TAIL,
 'ordinary_missing_table':"INSERT INTO absent VALUES(1);"+TAIL,
 'ordinary_missing_column':"UPDATE t SET absent=4;"+TAIL,
 'ordinary_values_source':"INSERT INTO t(v,n) VALUES(last_insert_rowid(),10),(last_insert_rowid(),11) RETURNING id,v;"+TAIL,
 'ordinary_select_source':"INSERT INTO t(v,n) SELECT * FROM(VALUES(last_insert_rowid(),10),(last_insert_rowid(),11)) RETURNING id,v;"+TAIL,
 'ordinary_multi_metadata':"INSERT INTO t VALUES(4,json('[1]'),4),(5,json('[2]'),5) RETURNING subtype(v),(SELECT count(*) FROM t);"+TAIL,
 'ordinary_select_error':"SELECT abs(-9223372036854775808);"+TAIL,
 'ordinary_check':"CREATE TABLE checked(id INTEGER PRIMARY KEY,n CHECK(n>0));INSERT INTO checked VALUES(1,1);INSERT INTO checked VALUES(2,-1);SELECT * FROM checked;"+TAIL,
})
Q['ordinary_where_preparation']="DELETE FROM t WHERE absent(n);"+TAIL
Q['ordinary_prepare_arg_priority']="UPDATE t SET n=absent(missing) WHERE 0;"+TAIL
Q['ordinary_window_insert']="CREATE TABLE dst(id INTEGER PRIMARY KEY,v);INSERT INTO dst SELECT row_number() OVER(ORDER BY id),v FROM (SELECT * FROM t);SELECT * FROM dst;"+TAIL
FK_SETUP='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));PRAGMA foreign_keys=ON;'
Q.update({
 'fk_single':FK_SETUP+'INSERT INTO c VALUES(4,99);'+TAIL+'SELECT * FROM c;',
 'fk_returning':FK_SETUP+'INSERT INTO c VALUES(4,99) RETURNING id;'+TAIL+'SELECT * FROM c;',
 'fk_multiple':FK_SETUP+'INSERT INTO c VALUES(4,1),(5,99);'+TAIL+'SELECT * FROM c;',
 'fk_with_program':FK_SETUP+'CREATE TRIGGER a AFTER INSERT ON c BEGIN SELECT new.id;END;INSERT INTO c VALUES(4,99);'+TAIL+'SELECT * FROM c;',
 'fk_self_old_orphan':'CREATE TABLE p(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));INSERT INTO p VALUES(1,4);PRAGMA foreign_keys=ON;INSERT INTO p VALUES(4,99);'+TAIL+'SELECT * FROM p;',
 'fk_autoincrement':'CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(id INTEGER PRIMARY KEY AUTOINCREMENT,pid INTEGER REFERENCES p(id));PRAGMA foreign_keys=ON;INSERT INTO c(pid) VALUES(99);'+TAIL+'SELECT * FROM c;',
 'fk_replace':FK_SETUP+'INSERT OR REPLACE INTO c VALUES(4,99);'+TAIL+'SELECT * FROM c;',
 'fk_ignore':FK_SETUP+'INSERT INTO c VALUES(4,1);INSERT OR IGNORE INTO c VALUES(4,99);'+TAIL+'SELECT * FROM c;',
})
Q['fk_replace_generated']=FK_SETUP+'INSERT INTO c VALUES(10,1);INSERT OR REPLACE INTO c(pid) VALUES(99);'+TAIL+'SELECT * FROM c;'
Q['fk_autoincrement_retained']='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);CREATE TABLE c(id INTEGER PRIMARY KEY AUTOINCREMENT,pid INTEGER REFERENCES p(id));INSERT INTO c VALUES(10,1);DELETE FROM c;PRAGMA foreign_keys=ON;INSERT INTO c(pid) VALUES(99);'+TAIL+'SELECT * FROM c;'
for name,command in {
 'replace_explicit_null':'INSERT OR REPLACE INTO c VALUES(NULL,99);',
 'replace_computed_null':'INSERT OR REPLACE INTO c VALUES(nullif(0,0),99);',
 'replace_rowid_null':'INSERT OR REPLACE INTO c(rowid,pid) VALUES(NULL,99);',
 'abort_explicit_null':'INSERT OR ABORT INTO c VALUES(NULL,99);',
 'ignore_explicit_null':'INSERT OR IGNORE INTO c VALUES(NULL,99);',
}.items():
 Q['fk_'+name]=FK_SETUP+'INSERT INTO c VALUES(10,1);'+command+TAIL+'SELECT * FROM c;'
for name,schema,command in [
 ('replace_unique','CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id),v UNIQUE);','INSERT OR REPLACE INTO c(pid) VALUES(99);'),
 ('replace_nonunique','CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));CREATE INDEX ci ON c(pid);','INSERT OR REPLACE INTO c(pid) VALUES(99);'),
 ('schema_replace_omitted','CREATE TABLE c(id INTEGER PRIMARY KEY ON CONFLICT REPLACE,pid INTEGER REFERENCES p(id));','INSERT INTO c(pid) VALUES(99);'),
 ('schema_replace_null','CREATE TABLE c(id INTEGER PRIMARY KEY ON CONFLICT REPLACE,pid INTEGER REFERENCES p(id));','INSERT INTO c VALUES(NULL,99);'),
]:
 Q['fk_'+name]='CREATE TABLE p(id INTEGER PRIMARY KEY);INSERT INTO p VALUES(1);'+schema+'INSERT INTO c(id,pid) VALUES(10,1);PRAGMA foreign_keys=ON;'+command+TAIL+'SELECT * FROM c;'
rng=random.Random(int(os.environ.get('SQLEANITE_ERROR_EFFECTS_SEED','1819001')))
for i in range(12):
 key=rng.randrange(1,4);amount=rng.randrange(1,10)
 Q[f'fresh_{i}']=f"CREATE TRIGGER a AFTER UPDATE ON t BEGIN UPDATE log SET n=n+{amount};SELECT CASE WHEN new.id={key} THEN RAISE(ABORT,new.v) END;END;UPDATE t SET n=n+10;"+TAIL

def case(sql):
 def test(self):
  script=statement_lines(SETUP+sql)
  lean=subprocess.run([str(BINARY),'--error-effects-script'],input=script,text=True,capture_output=True,timeout=30)
  native=subprocess.run([SQLITE,'-batch',':memory:'],input=script,text=True,capture_output=True,timeout=30)
  self.assertEqual(lean.returncode,native.returncode,lean.stderr+' / '+native.stderr)
  self.assertEqual(lean.stdout,native.stdout,lean.stderr+' / '+native.stderr)
  def errors(output):return [re.sub(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?: ?','',line) for line in output.splitlines() if re.match(r'^(?:Parse error|Runtime error|Error)(?: near line [0-9]+)?:',line)]
  self.assertEqual(errors(lean.stderr),errors(native.stderr))
 return test
for name,sql in Q.items():setattr(ErrorEffects,'test_'+name,case(sql))
if __name__=='__main__':unittest.main()
