import SQLeaniteTests.BeforeDelete

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectForeignCounters : IO Unit := do
  unless CoreTriggerProgram.ForeignCounter.decrement 1 3 == -2 &&
      CoreTriggerProgram.ForeignCounter.decrement 0 3 == 0 &&
      (!(CoreTriggerProgram.ForeignCounter.require (-2)).isOk) do
    fail "FK scan decrement saturated, ignored the zero guard or admitted a nonzero signed counter"
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE p(id INTEGER PRIMARY KEY);",
      "INSERT INTO p VALUES(1),(2);",
      "CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));",
      "INSERT INTO c VALUES(1,1),(2,90);",
      "PRAGMA foreign_keys=ON;",
      "CREATE TRIGGER tr AFTER UPDATE ON c BEGIN SELECT new.id;END;"] do
    state := (← foreignStatement state sql).1
  let (accepted,_) ← foreignStatement state "UPDATE c SET pid=CASE id WHEN 1 THEN 91 ELSE 2 END;"
  unless accepted.foreignCounter == 0 && accepted.foreignWrites.isEmpty &&
      accepted.foreignKeys && accepted.lastChanges == 2 do
    fail "signed FK counter did not close at the outer statement boundary"
  let (_,orphans) ← foreignStatement accepted "PRAGMA foreign_key_check;"
  unless (orphans.flatMap (·.rows)).length == 1 do
    fail "old-orphan counter cancellation was replaced by a final-table validity filter"
  let mut negative := Core.State.empty
  for sql in [
      "CREATE TABLE p(id INTEGER PRIMARY KEY);",
      "INSERT INTO p VALUES(1);",
      "CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));",
      "INSERT INTO c VALUES(1,90),(2,90);",
      "PRAGMA foreign_keys=ON;",
      "CREATE TRIGGER tr AFTER UPDATE ON p BEGIN INSERT INTO c VALUES(3,90);INSERT INTO p VALUES(90);END;"] do
    negative := (← foreignStatement negative sql).1
  let parsed ← match CoreTokenGrammar.parseCertified "UPDATE p SET id=id;" with
    | .ok value => pure value | .error message => fail message
  let some command := parsed.statements[0]? | fail "missing negative FK counter fixture"
  match CoreDerivedSQL.executeStatement negative command "UPDATE p SET id=id;" with
  | .error message => unless message == "FOREIGN KEY constraint failed" do fail message
  | .ok _ => fail "negative FK counter was hidden by repaired final table contents"

end SQLeanite.Tests
