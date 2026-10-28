import SQLeaniteTests.BeforeUpdate
import SQLeanite.CoreTriggerProgram.InsertBefore

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectBeforeInsert : IO Unit := do
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,g INTEGER GENERATED ALWAYS AS(n*2) STORED,v TEXT);",
      "CREATE TABLE log(stage TEXT,id INTEGER,n INTEGER,g INTEGER);",
      "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log VALUES('before',new.id,new.n,new.g);INSERT INTO t(id,n,v) VALUES(10,1,'body');END;",
      "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO log VALUES('after',new.id,new.n,new.g);END;"] do
    state := (← foreignStatement state sql).1
  let (inserted,output) ← foreignStatement state "INSERT INTO t(n,v) VALUES('04','a') RETURNING id,n,g,v;"
  let expected ← match [[Value.integer 11,.integer 4,.integer 8,.text "a"]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless output.flatMap (·.rows) == expected && inserted.lastChanges == 1 && inserted.totalChanges == 5 &&
      inserted.lastInsertRowid == 11 && !inserted.internalReturning && !inserted.schemaProgram do
    fail "BEFORE INSERT lost provisional rowid, generated registers, actual allocation or connection restoration"
  let (_,logged) ← foreignStatement inserted "SELECT stage,id,n,g FROM log ORDER BY rowid;"
  let expectedLog ← match [[Value.text "before",.integer (-1),.integer 4,.integer 8],
      [.text "after",.integer 10,.integer 1,.integer 2],[.text "after",.integer 11,.integer 4,.integer 8]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless logged.flatMap (·.rows) == expectedLog do fail "BEFORE/AFTER INSERT frames did not retain their actual row images"
  let mut counted := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v,n);",
      "INSERT INTO t VALUES(3,'a',3);",
      "CREATE TABLE log(n);",
      "INSERT INTO log VALUES(0);",
      "CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=new.id;DELETE FROM t WHERE id=3;END;"] do
    counted := (← foreignStatement counted sql).1
  let (finished,result) ← foreignStatement counted "INSERT INTO t VALUES((SELECT max(id) FROM t)+total_changes()+10,'d',4) RETURNING id;"
  -- Two setup writes and two trigger writes: the cached max is 3, while the
  -- second total_changes() reads 4. NEW.id was 15 before those trigger writes.
  let expectedKey ← match SQLSurface.value (.integer 17) with | .ok value => pure value | .error message => fail message
  unless result.flatMap (·.rows) == [[expectedKey]] && finished.lastInsertRowid == 17 do
    fail "INSERT cached the complete rowid expression instead of its subquery register"
  let (_,snapshot) ← foreignStatement finished "SELECT n FROM log;"
  let expectedBefore ← match SQLSurface.value (.integer 15) with | .ok value => pure value | .error message => fail message
  unless snapshot.flatMap (·.rows) == [[expectedBefore]] do fail "BEFORE INSERT observed a post-trigger counter"

end SQLeanite.Tests
