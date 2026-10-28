import SQLeaniteTests.ErrorEffects

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

private def earlyEffect (state : Core.State) (source : String) : IO CoreTriggerProgram.ExecutionOutcome := do
  let parsed ← match CoreTokenGrammar.parseCertified source with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing early FK statement"
  return CoreDerivedSQL.executeStatementEffects state statement source

def expectEarlyForeignInsert : IO Unit := do
  let mut state := Core.State.empty
  for source in [
      "CREATE TABLE p(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));",
      "INSERT INTO p VALUES(1,4);",
      "PRAGMA foreign_keys=ON;"] do
    state := (← foreignStatement state source).1
  let failed ← match ← earlyEffect state "INSERT INTO p VALUES(4,99);" with
    | .success .. => fail "single-write FK lookup was incorrectly canceled by an old orphan parent scan"
    | .failure next message =>
        unless message == "FOREIGN KEY constraint failed" do fail "early FK lookup changed its diagnostic"
        pure next
  unless failed.database.contents == state.database.contents && failed.lastInsertRowid == 1 &&
      failed.lastChanges == 0 && failed.totalChanges == 1 do
    fail "early FK failure executed a point or lost native connection counts"
  let accepted ← match ← earlyEffect failed "INSERT INTO p VALUES(4,4);" with
    | .failure _ message => fail message
    | .success next _ => pure next
  unless accepted.lastInsertRowid == 4 && accepted.foreignCounter == 0 do
    fail "early FK lookup rejected a real self-referencing NEW parent key"
  let child := (← foreignStatement accepted "CREATE TABLE c(id INTEGER PRIMARY KEY,pid INTEGER REFERENCES p(id));").1
  let rejected ← match ← earlyEffect child "INSERT INTO c VALUES(20,99);" with
    | .success .. => fail "missing parent accepted"
    | .failure next _ => pure next
  unless rejected.lastInsertRowid == 4 && rejected.database.contents == child.database.contents do
    fail "plain child FK failure retained a rowid for an insertion that never executed"
  let automatic ← match ← earlyEffect rejected "INSERT OR REPLACE INTO c(pid) VALUES(99);" with
    | .success .. => fail "generated-rowid REPLACE accepted a missing parent"
    | .failure next _ => pure next
  unless automatic.lastInsertRowid == 4 do
    fail "omitted REPLACE rowid incorrectly compiled an explicit-key replacement write"
  let explicitNull ← match ← earlyEffect automatic "INSERT OR REPLACE INTO c VALUES(NULL,99);" with
    | .success .. => fail "explicit-NULL REPLACE accepted a missing parent"
    | .failure next _ => pure next
  unless explicitNull.lastInsertRowid == 1 do
    fail "explicit-NULL REPLACE lost its post-point rowid on statement rollback"

end SQLeanite.Tests
