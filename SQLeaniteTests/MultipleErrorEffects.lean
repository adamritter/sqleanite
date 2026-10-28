import SQLeaniteTests.EarlyForeignInsert

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

private def multipleEffect (state : Core.State) (source : String) : IO CoreTriggerProgram.ExecutionOutcome := do
  let parsed ← match CoreTokenGrammar.parseCertified source with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing multiple-input statement"
  return CoreDerivedSQL.executeStatementEffects state statement source

def expectMultipleErrorEffects : IO Unit := do
  let created := (← foreignStatement Core.State.empty "CREATE TABLE t(id INTEGER PRIMARY KEY,n);").1
  let state := (← foreignStatement created "INSERT INTO t VALUES(10,1);").1
  for source in [
      "INSERT INTO t VALUES(11,2),(12,abs(-9223372036854775808));",
      "INSERT INTO t VALUES(11,2),(10,3);",
      "INSERT INTO t SELECT * FROM(VALUES(11,2),(12,abs(-9223372036854775808)));",
      "INSERT INTO t SELECT * FROM(VALUES(11,2),(10,3));"] do
    let failed ← match ← multipleEffect state source with
      | .success .. => fail "later input failure returned success"
      | .failure next _ => pure next
    unless failed.database.contents == state.database.contents && failed.lastChanges == 0 &&
        failed.totalChanges == 1 && failed.lastInsertRowid == 11 do
      fail "later input failure lost an actual earlier point's rowid or published failed data"
  for source in [
      "INSERT INTO t VALUES(11,2),(12,absent(1));",
      "INSERT INTO t SELECT * FROM(VALUES(11,2),(12,absent(1)));"] do
    let failedPreparation ← match ← multipleEffect state source with
      | .success .. => fail "unknown function prepared successfully"
      | .failure next message =>
          unless message == "no such function: absent" do fail "VALUES input preparation lost its concrete function diagnostic"
          pure next
    unless failedPreparation.lastInsertRowid == 10 && failedPreparation.lastChanges == 1 do
      fail "multiple-input preparation executed an input or changed preceding connection counts"

end SQLeanite.Tests
