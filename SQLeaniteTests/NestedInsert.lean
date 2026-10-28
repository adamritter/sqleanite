import SQLeaniteTests.BeforeInsert

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectNestedInsert : IO Unit := do
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER,g INTEGER GENERATED ALWAYS AS(n*2) STORED);",
      "CREATE TABLE log(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);",
      "INSERT INTO log VALUES(1,'',0);",
      "CREATE TRIGGER b BEFORE INSERT ON t BEGIN UPDATE log SET n=subtype(new.v);END;",
      "CREATE TRIGGER a AFTER UPDATE ON log BEGIN INSERT INTO t(id,v,n,n) VALUES((SELECT new.n)+10,json('[1]'),new.n,abs(-9223372036854775808));END;"] do
    state := (← foreignStatement state sql).1
  let (inserted,_) ← foreignStatement state "UPDATE log SET v='outer',n=4;"
  unless inserted.lastChanges == 1 && inserted.totalChanges == 4 && inserted.lastInsertRowid == 1 &&
      !inserted.internalReturning && !inserted.schemaProgram do
    fail "nested INSERT lost actual body totals or caller connection/context restoration"
  let (_,rows) ← foreignStatement inserted "SELECT id,v,n,g FROM t;"
  let expected ← match [[Value.integer 14,.text "[1]",.integer 4,.integer 8]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless rows.flatMap (·.rows) == expected do
    fail "nested INSERT lost fixed caller NEW values, typed selected inputs or discarded-expression laziness"
  let (_,tags) ← foreignStatement inserted "SELECT n FROM log;"
  let tag ← match SQLSurface.value (.integer 74) with | .ok value => pure value | .error message => fail message
  unless tags.flatMap (·.rows) == [[tag]] do fail "nested INSERT erased a real JSON register subtype"

end SQLeanite.Tests
