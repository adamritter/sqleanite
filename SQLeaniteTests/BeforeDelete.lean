import SQLeaniteTests.TriggerConstraints

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectBeforeDelete : IO Unit := do
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER);",
      "INSERT INTO t VALUES(1,4);",
      "CREATE TABLE log(id INTEGER PRIMARY KEY,n INTEGER);",
      "CREATE TRIGGER before_tr BEFORE DELETE ON t BEGIN UPDATE t SET n=99 WHERE id=old.id;END;",
      "CREATE TRIGGER after_tr AFTER DELETE ON t BEGIN INSERT INTO log VALUES(old.id,old.n);END;"] do
    state := (← foreignStatement state sql).1
  let (begun,_) ← foreignStatement state "BEGIN;"
  let (deleted,outputs) ← foreignStatement begun "DELETE FROM t RETURNING id,n;"
  let expected ← match [[Value.integer 1,.integer 4]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless outputs.flatMap (·.rows) == expected && deleted.lastChanges == 1 &&
      deleted.totalChanges == state.totalChanges+3 do
    fail "BEFORE mutation replaced DELETE's original OLD/RETURNING registers or direct change count"
  let (_,logged) ← foreignStatement deleted "SELECT id,n FROM log;"
  unless logged.flatMap (·.rows) == expected do fail "AFTER DELETE did not retain the pre-BEFORE OLD image"
  let (restored,_) ← foreignStatement deleted "ROLLBACK;"
  unless restored.database.contents == state.database.contents && restored.totalChanges == deleted.totalChanges do
    fail "rollback lost BEFORE body changes or reset connection totals"
  let (invalid,_) ← foreignStatement restored "CREATE TRIGGER invalid BEFORE DELETE ON t BEGIN SELECT new.id;END;"
  let parsed ← match CoreTokenGrammar.parseCertified "DELETE FROM t WHERE 0;" with
    | .ok value => pure value | .error message => fail message
  let some command := parsed.statements[0]? | fail "missing BEFORE preparation fixture"
  match CoreDerivedSQL.executeStatement invalid command "DELETE FROM t WHERE 0;" with
  | .error message => unless message == "no such column: new.id" do fail message
  | .ok _ => fail "empty DELETE input hid an invalid BEFORE pseudo-row reference"

end SQLeanite.Tests
