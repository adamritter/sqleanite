import SQLeaniteTests.NestedInsert
import SQLeanite.CoreTriggerControl

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectRecursiveTriggers : IO Unit := do
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,n);",
      "INSERT INTO t VALUES(1,0);",
      "CREATE TABLE log(n);",
      "PRAGMA recursive_triggers=ON;",
      "CREATE TRIGGER a AFTER UPDATE ON t WHEN new.n<5 BEGIN INSERT INTO log VALUES(new.n);UPDATE t SET n=n+1 WHERE id=new.id;END;"] do
    state := (← foreignStatement state sql).1
  let (updated,_) ← foreignStatement state "UPDATE t SET n=1;"
  unless updated.recursiveTriggers && updated.triggerDepth == 0 && updated.lastChanges == 1 &&
      updated.totalChanges == 10 && updated.lastInsertRowid == 1 do
    fail "recursive programs lost actual frame depth or caller connection registers"
  let (_,rows) ← foreignStatement updated "SELECT n FROM t;"
  let five ← match SQLSurface.value (.integer 5) with | .ok value => pure value | .error message => fail message
  unless rows.flatMap (·.rows) == [[five]] do fail "recursive_triggers did not permit repeated program entry"
  let begun := (← foreignStatement updated "BEGIN;").1
  let disabled := (← foreignStatement begun "PRAGMA recursive_triggers=OFF;").1
  let restored := (← foreignStatement disabled "ROLLBACK;").1
  unless !restored.recursiveTriggers && restored.triggerDepth == 0 do
    fail "transaction rollback reverted the live recursive_triggers connection setting"
  let mut replaced := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);",
      "INSERT INTO t VALUES(1,'a',1),(2,'b',2),(3,'c',3);",
      "PRAGMA recursive_triggers=ON;",
      "CREATE TRIGGER d AFTER DELETE ON t BEGIN UPDATE t SET v='body' WHERE id=3;END;"] do
    replaced := (← foreignStatement replaced sql).1
  let (finished,output) ← foreignStatement replaced "UPDATE OR REPLACE t SET id=2,n=9 WHERE id=3 RETURNING id,v,n;"
  let expected ← match [[Value.integer 2,.text "c",.integer 9]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless output.flatMap (·.rows) == expected && finished.totalChanges == 5 && finished.lastChanges == 1 &&
      finished.lastInsertRowid == 3 && finished.triggerDepth == 0 do
    fail "REPLACE lost frozen ordinary registers or counted auxiliary deletions as direct changes"

end SQLeanite.Tests
