import SQLeaniteTests.RegisterInputEffects

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

private def planEffect (state : Core.State) (source : String) : IO CoreTriggerProgram.ExecutionOutcome := do
  let parsed ← match CoreTokenGrammar.parseCertified source with
    | .ok parsed => pure parsed | .error message => fail message
  let some statement := parsed.statements[0]? | fail "missing register plan statement"
  return CoreDerivedSQL.executeStatementEffects state statement source

def expectRegisterInputPlans : IO Unit := do
  let mut state := Core.State.empty
  for source in ["CREATE TABLE src(id INTEGER PRIMARY KEY,n);",
      "INSERT INTO src VALUES(1,1),(2,2),(3,3);",
      "CREATE TABLE dst(id INTEGER PRIMARY KEY,n);", "INSERT INTO dst VALUES(10,10);"] do
    state := (← foreignStatement state source).1
  for (query,values) in [
      ("SELECT NULL,id*100+last_insert_rowid() FROM src ORDER BY id DESC", [310,211,112]),
      ("SELECT DISTINCT NULL,last_insert_rowid() FROM src", [10,11,12]),
      ("SELECT NULL,last_insert_rowid() FROM src ORDER BY n DESC", [10,10,10]),
      ("SELECT NULL,last_insert_rowid() UNION ALL SELECT NULL,last_insert_rowid()", [10,11]),
      ("SELECT NULL,last_insert_rowid() FROM(SELECT * FROM src)", [10,11,12]),
      ("SELECT NULL,column1 FROM(VALUES(last_insert_rowid()),(last_insert_rowid()))", [10,11]),
      ("SELECT NULL,column1+column1 FROM(VALUES(last_insert_rowid()),(last_insert_rowid()))", [20,22]),
      ("SELECT NULL,column1='1' FROM(VALUES(CAST('1' AS INTEGER)),('1'))", [0,1]),
      ("SELECT NULL,subtype(column1) FROM(VALUES(json('{}')),(json('{}')))", [0,0])] do
    let accepted ← match ← planEffect state ("INSERT INTO dst " ++ query ++ ";") with
      | .failure _ message => fail message
      | .success next _ => pure next
    let (_,observed) ← foreignStatement accepted "SELECT n FROM dst WHERE id>10 ORDER BY id;"
    let expected ← match values.mapM (fun value => do return [← SQLSurface.value (.integer value)]) with
      | .ok rows => pure rows | .error message => fail message
    unless observed.flatMap (·.rows) == expected do
      fail "register input plan confused cursor order, DISTINCT, sorter materialization or source flattening"
  let failed ← match ← planEffect state "INSERT INTO dst SELECT CASE WHEN n=2 THEN 10 ELSE id+10 END,n FROM src ORDER BY n DESC;" with
    | .success .. => fail "sorted source target conflict returned success"
    | .failure next _ => pure next
  unless failed.database.contents == state.database.contents && failed.lastInsertRowid == 13 do
    fail "sorter input lost an actual earlier accepted point on a later target conflict"

end SQLeanite.Tests
