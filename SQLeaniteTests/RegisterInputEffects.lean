import SQLeaniteTests.MultipleErrorEffects

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

private def registerEffect (state : Core.State) (source : String) : IO CoreTriggerProgram.ExecutionOutcome := do
  let parsed ← match CoreTokenGrammar.parseCertified source with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing register-input statement"
  return CoreDerivedSQL.executeStatementEffects state statement source

def expectRegisterInputEffects : IO Unit := do
  let mut state := Core.State.empty
  for source in [
      "CREATE TABLE src(id INTEGER PRIMARY KEY,n);",
      "INSERT INTO src VALUES(1,1),(2,2),(3,3);",
      "CREATE TABLE dst(id INTEGER PRIMARY KEY,n);",
      "INSERT INTO dst VALUES(10,10);"] do
    state := (← foreignStatement state source).1
  for source in [
      "INSERT INTO dst SELECT id+10,CASE WHEN n=2 THEN abs(-9223372036854775808) ELSE n END FROM src;",
      "INSERT INTO dst SELECT id+10,n FROM src WHERE CASE WHEN n=2 THEN abs(-9223372036854775808) ELSE 1 END;",
      "INSERT INTO dst SELECT CASE WHEN n=2 THEN 10 ELSE id+10 END,n FROM src;"] do
    let failed ← match ← registerEffect state source with
      | .success .. => fail "late register source/constraint failure returned success"
      | .failure next _ => pure next
    unless failed.database.contents == state.database.contents && failed.lastChanges == 0 &&
        failed.totalChanges == 4 && failed.lastInsertRowid == 11 do
      fail "register coroutine failed to retain actual earlier point effects while rolling back rows"
  let accepted ← match ← registerEffect state "INSERT INTO dst SELECT NULL,last_insert_rowid() FROM src;" with
    | .failure _ message => fail message
    | .success next _ => pure next
  let (_,observed) ← foreignStatement accepted "SELECT * FROM dst ORDER BY id;"
  let expected ← match [[Value.integer 10,.integer 10],[.integer 11,.integer 10],
      [.integer 12,.integer 11],[.integer 13,.integer 12]].mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows | .error message => fail message
  unless observed.flatMap (·.rows) == expected && accepted.lastChanges == 3 && accepted.totalChanges == 7 do
    fail "register coroutine lost yielded connection values or statement-level counts"

end SQLeanite.Tests
