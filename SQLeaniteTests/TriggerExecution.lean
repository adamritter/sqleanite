import SQLeaniteTests.TriggerCatalog
import SQLeanite.CoreTriggerProgram.Rows

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectTriggerExecution : IO Unit := do
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER);",
      "INSERT INTO t VALUES(1,1),(2,2),(3,3);",
      "CREATE TABLE log(id INTEGER PRIMARY KEY,n INTEGER);",
      "INSERT INTO log VALUES(1,0);",
      "CREATE TRIGGER tr AFTER UPDATE OF n ON t WHEN new.n>old.n BEGIN UPDATE log SET n=n+new.n-old.n WHERE id=1;END;"] do
    state := (← foreignStatement state sql).1
  let (next,results) ← foreignStatement state "UPDATE t SET n=n+10 WHERE id<3 RETURNING id,n;"
  let expected ← match [[Value.integer 1,.integer 11],[.integer 2,.integer 12]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless results.flatMap (·.rows) == expected && next.lastChanges == 2 &&
      next.totalChanges == state.totalChanges+4 && next.lastInsertRowid == state.lastInsertRowid do
    fail "AFTER row program lost its fixed images, RETURNING rows or connection registers"
  let (_,logged) ← foreignStatement next "SELECT n FROM log;"
  let value ← match SQLSurface.value (.integer 20) with
    | .ok value => pure value | .error message => fail message
  unless logged.flatMap (·.rows) == [[value]] do fail "AFTER trigger body did not accumulate both row deltas"
  let (begun,_) ← foreignStatement next "BEGIN;"
  let (updated,_) ← foreignStatement begun "UPDATE t SET n=n+1;"
  let (rolled,_) ← foreignStatement updated "ROLLBACK;"
  unless rolled.database.contents == next.database.contents && rolled.totalChanges == updated.totalChanges do
    fail "trigger rollback did not restore rows while retaining connection totals"
  let (bad,_) ← foreignStatement next "CREATE TRIGGER bad AFTER DELETE ON t WHEN 0 BEGIN SELECT new.id; END;"
  let parsed ← match CoreTokenGrammar.parseCertified "DELETE FROM t WHERE 0;" with
    | .ok value => pure value | .error message => fail message
  let some command := parsed.statements[0]? | fail "missing trigger preparation fixture"
  match CoreDerivedSQL.executeStatement bad command "DELETE FROM t WHERE 0;" with
  | .error message => unless message == "no such column: new.id" do fail message
  | .ok _ => fail "zero selected rows hid a trigger preparation error"

end SQLeanite.Tests
