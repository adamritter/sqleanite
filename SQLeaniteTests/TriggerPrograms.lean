import SQLeaniteTests.TriggerExecution

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectTriggerPrograms : IO Unit := do
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,n INTEGER);",
      "CREATE TABLE log(id INTEGER PRIMARY KEY,n INTEGER);",
      "INSERT INTO t VALUES(1,2),(2,3);",
      "CREATE TRIGGER outer_tr AFTER UPDATE ON t BEGIN INSERT INTO log SELECT new.id,(SELECT old.n+new.n);END;"] do
    state := (← foreignStatement state sql).1
  let (next,_) ← foreignStatement state "UPDATE t SET n=n+4;"
  let (_,outputs) ← foreignStatement next "SELECT id,n FROM log ORDER BY id;"
  let expected ← match [[Value.integer 1,.integer 8],[.integer 2,.integer 10]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless outputs.flatMap (·.rows) == expected && next.lastChanges == 2 &&
      next.totalChanges == state.totalChanges+4 do
    fail "INSERT SELECT trigger body lost its actual lexical parent values or counter effects"
  let (same,_) ← foreignStatement next "UPDATE OR IGNORE t SET n=n+1;"
  let (_,retained) ← foreignStatement same "SELECT id,n FROM log ORDER BY id;"
  unless retained.flatMap (·.rows) == expected && same.totalChanges == next.totalChanges+2 do
    fail "outer OR IGNORE failed to override the body INSERT conflict policy"
  let (bad,_) ← foreignStatement same "CREATE TRIGGER inner_tr AFTER INSERT ON log BEGIN SELECT new.missing;END;"
  let parsed ← match CoreTokenGrammar.parseCertified "UPDATE t SET n=n+1 WHERE 0;" with
    | .ok value => pure value | .error message => fail message
  let some command := parsed.statements[0]? | fail "missing nested trigger preparation fixture"
  match CoreDerivedSQL.executeStatement bad command "UPDATE t SET n=n+1 WHERE 0;" with
  | .error message => unless message == "no such column: new.missing" do fail message
  | .ok _ => fail "empty outer input hid a nested trigger program preparation error"
  match CoreTokenGrammar.parseCertified "CREATE TRIGGER illegal AFTER INSERT ON t BEGIN INSERT INTO log DEFAULT VALUES;END;" with
  | .error message => unless message == "near \"DEFAULT\": syntax error" do fail message
  | .ok _ => fail "trigger grammar admitted forbidden DEFAULT VALUES"

end SQLeanite.Tests
