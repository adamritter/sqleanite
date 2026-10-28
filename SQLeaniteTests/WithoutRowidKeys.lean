import SQLeaniteTests.WithoutRowid

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectWithoutRowidKeys : IO Unit := do
  let mut state := Core.State.empty
  for sql in ["CREATE TABLE t(a TEXT COLLATE NOCASE,b TEXT,n,PRIMARY KEY(a DESC,a COLLATE BINARY,b)) WITHOUT ROWID;",
      "INSERT INTO t VALUES('A','a',1),('a','b',2),('B','a',3);", "CREATE INDEX x ON t(a,n);",
      "UPDATE t SET n=n+10;"] do
    state := (← foreignStatement state sql).1
  let (_,results) ← foreignStatement state "SELECT * FROM t ORDER BY a DESC,a COLLATE BINARY,b;"
  let expected ← match [[Value.text "B",.text "a",.integer 13],
      [.text "A",.text "a",.integer 11],[.text "a",.text "b",.integer 12]].mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows | .error message => fail message
  unless results.flatMap (·.rows) == expected do fail "actual primary direction/duplicate collation storage order differs"
  let some table := CoreNames.table? state.database "t" | fail "missing key-layout table"
  let some physical := CoreWithoutRowidTable.physicalRows table | fail "missing repeated key records"
  unless physical.all (fun row => row.length == 4) do fail "distinct primary collation fields were collapsed"
  let some layout := CoreWithoutRowidData.layout table.catalogSQL | fail "missing actual primary layout"
  let some record := physical.head? | fail "missing physical primary record"
  unless (CoreWithoutRowidData.logicalValues table.schema layout record).isSome do
    fail "valid repeated-column record was rejected"
  let changed ← match SQLSurface.value (.text "different") with
    | .ok value => pure value | .error message => fail message
  if (CoreWithoutRowidData.logicalValues table.schema layout (record.set 1 changed)).isSome then
    fail "a disagreeing repeated primary field was silently discarded"
  let (_,metadata) ← foreignStatement state "PRAGMA index_xinfo(x);"
  unless (metadata.flatMap (·.rows)).length == 4 do fail "secondary suffix lost a distinct collation or key column"

end SQLeanite.Tests
