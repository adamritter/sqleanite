import SQLeaniteTests.ForeignCounters
import SQLeanite.CoreTriggerProgram.UpdateBefore

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectBeforeUpdate : IO Unit := do
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER,v TEXT,g INTEGER GENERATED ALWAYS AS(length(v)) STORED);",
      "INSERT INTO t(id,n,v) VALUES(1,2,'a');",
      "CREATE TABLE log(stage TEXT,n INTEGER,g INTEGER);",
      "CREATE TRIGGER before_tr BEFORE UPDATE ON t BEGIN INSERT INTO log VALUES('before',new.n,new.g);UPDATE t SET v='body' WHERE id=old.id;END;",
      "CREATE TRIGGER after_tr AFTER UPDATE OF n ON t BEGIN INSERT INTO log VALUES('after',new.n,new.g);END;"] do
    state := (← foreignStatement state sql).1
  let (updated,output) ← foreignStatement state "UPDATE t SET n=n+3 RETURNING id,n,v,g;"
  let expected ← match [[Value.integer 1,.integer 5,.text "body",.integer 4]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless output.flatMap (·.rows) == expected && !updated.internalReturning && !updated.schemaProgram do
    fail "BEFORE UPDATE lost frozen SET values, current unassigned columns or private context restoration"
  let (_,logged) ← foreignStatement updated "SELECT stage,n,g FROM log ORDER BY rowid;"
  let expectedLog ← match [[Value.text "before",.integer 5,.null],[.text "after",.integer 5,.integer 4]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless logged.flatMap (·.rows) == expectedLog do fail "generated NEW registers did not follow actual requested-column initialization and reload"
  let mut tagged := (← foreignStatement updated "DROP TRIGGER before_tr;").1
  for sql in [
      "CREATE TABLE tags(stage TEXT,n INTEGER);",
      "CREATE TRIGGER before_tag BEFORE UPDATE ON t BEGIN INSERT INTO tags VALUES('before',subtype(new.v));END;",
      "CREATE TRIGGER after_tag AFTER UPDATE ON t BEGIN INSERT INTO tags VALUES('after',subtype(new.v));END;"] do
    tagged := (← foreignStatement tagged sql).1
  let (finalTagged,_) ← foreignStatement tagged "UPDATE t SET v=json('[1]');"
  let (_,tags) ← foreignStatement finalTagged "SELECT stage,n FROM tags ORDER BY rowid;"
  let expectedTags ← match [[Value.text "before",.integer 74],[.text "after",.integer 74]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless tags.flatMap (·.rows) == expectedTags do fail "actual BEFORE/AFTER register subtypes were erased or reevaluated"

end SQLeanite.Tests
