import SQLeaniteTests.RaiseAbort

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

private def effectStatement (state : Core.State) (source : String) : IO CoreTriggerProgram.ExecutionOutcome := do
  let parsed ← match CoreTokenGrammar.parseCertified source with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing state-carrying statement"
  return CoreDerivedSQL.executeStatementEffects state statement source

def expectErrorEffects : IO Unit := do
  let mut state := Core.State.empty
  for source in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,n);",
      "INSERT INTO t VALUES(1,1);",
      "CREATE TABLE log(id INTEGER PRIMARY KEY,n);",
      "INSERT INTO log VALUES(1,0);",
      "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;SELECT RAISE(ABORT,'stop');END;"] do
    state := (← foreignStatement state source).1
  let failed ← match ← effectStatement state "UPDATE t SET n=2;" with
    | .success .. => fail "ABORT returned success"
    | .failure next message =>
        unless message == "stop" do fail "state-carrying ABORT changed its message"
        pure next
  unless failed.database.contents == state.database.contents && failed.lastChanges == 0 &&
      failed.totalChanges == 3 && failed.lastInsertRowid == 1 && failed.triggerDepth == 0 do
    fail "ABORT failed to restore data while retaining actual body counters and caller frame"
  let (_,observed) ← foreignStatement failed "SELECT changes(),total_changes(),last_insert_rowid();"
  let expected ← match [[Value.integer 0,.integer 3,.integer 1]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless observed.flatMap (·.rows) == expected do fail "post-error SQL could not observe retained connection counters"
  let mut afterInsert := (← foreignStatement failed "DROP TRIGGER b;").1
  afterInsert := (← foreignStatement afterInsert "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO log VALUES(9,9);SELECT RAISE(ABORT,'after');END;").1
  let inserted ← match ← effectStatement afterInsert "INSERT INTO t VALUES(4,4);" with
    | .success .. => fail "AFTER INSERT ABORT returned success"
    | .failure next _ => pure next
  unless inserted.database.contents == afterInsert.database.contents && inserted.totalChanges == 4 &&
      inserted.lastInsertRowid == 4 && inserted.triggerDepth == 0 do
    fail "AFTER INSERT failure lost body totals or the actual outer insertion rowid"
  let returningFailure ← match ← effectStatement inserted "INSERT INTO t VALUES(7,7) RETURNING abs(-9223372036854775808);" with
    | .success .. => fail "RETURNING overflow returned success"
    | .failure next message =>
        unless message == "integer overflow" do fail "RETURNING failure changed its diagnostic"
        pure next
  unless returningFailure.database.contents == inserted.database.contents && returningFailure.totalChanges == 4 &&
      returningFailure.lastInsertRowid == 7 do
    fail "RETURNING error ran AFTER programs or lost the already executed point's rowid"

end SQLeanite.Tests
