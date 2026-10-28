import SQLeaniteTests.WithoutRowidKeys

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectWithoutRowidReseek : IO Unit := do
  let mut state := Core.State.empty
  for sql in ["CREATE TABLE t(k TEXT PRIMARY KEY,v,n) WITHOUT ROWID;",
      "INSERT INTO t VALUES('a','old',1),('b','later',2);",
      "CREATE TRIGGER b BEFORE UPDATE ON t WHEN old.k='a' BEGIN DELETE FROM t WHERE k=old.k;INSERT INTO t VALUES(old.k,'replacement',20);END;",
      "UPDATE t SET n=n+10 WHERE k='a';"] do
    state := (← foreignStatement state sql).1
  let (_,results) ← foreignStatement state "SELECT * FROM t ORDER BY k;"
  let expected ← match [[Value.text "a",.text "replacement",.integer 11],
      [.text "b",.text "later",.integer 2]].mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows | .error message => fail message
  unless results.flatMap (·.rows) == expected && state.lastChanges == 1 && state.totalChanges == 5 do
    fail "BEFORE deletion/reinsertion was followed by a private-ordinal lookup instead of the real PK"

end SQLeanite.Tests
