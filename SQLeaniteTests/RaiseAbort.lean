import SQLeaniteTests.RecursiveTriggers
import SQLeanite.SQLite.TriggerRaise

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectRaiseAbort : IO Unit := do
  let mut state := Core.State.empty
  for sql in [
      "CREATE TABLE t(id INTEGER PRIMARY KEY,n);",
      "INSERT INTO t VALUES(1,1);",
      "CREATE TABLE log(n);",
      "INSERT INTO log VALUES(0);",
      "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN UPDATE log SET n=n+1;SELECT CASE WHEN new.n=3 THEN RAISE(ABORT,'n='||new.n) ELSE 0 END;END;"] do
    state := (← foreignStatement state sql).1
  let source := "UPDATE t SET n=3;"
  let parsed ← match CoreTokenGrammar.parseCertified source with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing ABORT statement"
  match CoreDerivedSQL.executeStatement state statement source with
  | .error message => unless message == "n=3" do fail "RAISE ABORT lost its actual message expression"
  | .ok _ => fail "RAISE ABORT accepted its failing statement"
  let (_,original) ← foreignStatement state "SELECT n FROM t UNION ALL SELECT n FROM log;"
  let expected ← match [[Value.integer 1],[.integer 0]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless original.flatMap (·.rows) == expected do fail "a failed ABORT published a pending body write"
  -- This API returns Except String on failure. Retaining the native counters
  -- on same-connection error continuation is a separately recorded open gap.
  let (accepted,_) ← foreignStatement state "UPDATE t SET n=2;"
  let (_,logged) ← foreignStatement accepted "SELECT n FROM log;"
  let one ← match SQLSurface.value (.integer 1) with | .ok value => pure value | .error message => fail message
  unless logged.flatMap (·.rows) == [[one]] && accepted.triggerDepth == 0 && !accepted.schemaProgram do
    fail "an unreached ABORT executed or leaked its program context"

end SQLeanite.Tests
