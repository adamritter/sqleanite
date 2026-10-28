import SQLeaniteTests.CompositeTableKeys
import SQLeanite.CoreWithoutRowidTable
import SQLeanite.CoreWithoutRowidIndex

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectWithoutRowid : IO Unit := do
  let mut state := Core.State.empty
  for sql in ["CREATE TABLE ordinary(id INTEGER PRIMARY KEY);", "INSERT INTO ordinary VALUES(42);",
      "CREATE TABLE t(v TEXT,id TEXT,n UNIQUE,PRIMARY KEY(id,v)) WITHOUT ROWID;",
      "INSERT INTO t VALUES('b','a',1),('a','b',2),('a','a',3);",
      "CREATE INDEX by_v ON t(v);", "UPDATE t SET n=n+10 WHERE id='a';"] do
    state := (← foreignStatement state sql).1
  unless state.lastInsertRowid == 42 do fail "WITHOUT ROWID changed the user insertion register"
  let some table := CoreNames.table? state.database "t" | fail "missing WITHOUT ROWID table"
  unless table.withoutRowid do fail "lost actual WITHOUT ROWID source"
  let context : CoreExpr.Context := { schema := table.schema, sourceName := "t", rowidAliases := false }
  unless (context.column? none "rowid").isNone && (context.column? none "oid").isNone do
    fail "private ordinal escaped through an implicit SQL alias"
  let some physical := CoreWithoutRowidTable.physicalRows table | fail "missing physical table records"
  unless physical.all (fun row => row.length == 3) do fail "private ordinal entered physical table records"
  let expected ← match [[Value.text "a",.text "a",.integer 13],
      [.text "a",.text "b",.integer 11],[.text "b",.text "a",.integer 2]].mapM (List.mapM SQLSurface.value) with
    | .ok values => pure values | .error message => fail message
  unless physical == expected do fail "table records lost primary-key order or column permutation"
  let some source := state.catalog.current.filteredIndexes.find? (fun index => index.definition.name == "by_v")
    | fail "missing secondary index"
  let compiled ← match CorePartialIndex.prepare state.database source with
    | .ok value => pure value | .error message => fail message
  let records ← match CoreWithoutRowidIndex.records compiled with
    | .ok value => pure value | .error message => fail message
  unless records.all (fun row => row.length == 2) do fail "secondary record failed to suppress the shared primary column"
  state := (← foreignStatement state "INSERT OR REPLACE INTO t VALUES('new','c',2);").1
  let (_,results) ← foreignStatement state "SELECT * FROM t ORDER BY id,v;"
  unless (results.flatMap (·.rows)).length == 3 && state.lastInsertRowid == 42 do
    fail "unique secondary replacement lost its actual victim or insertion register"
  let (shadowed,_) ← foreignStatement Core.State.empty
    "CREATE TABLE t(rowid TEXT PRIMARY KEY,oid,_rowid_) WITHOUT ROWID;"
  let (shadowed,_) ← foreignStatement shadowed "INSERT INTO t VALUES('a','b','c');"
  let (_,results) ← foreignStatement shadowed "UPDATE t SET rowid='d' RETURNING rowid,oid,_rowid_;"
  unless (results.flatMap (·.rows)).length == 1 do fail "declared rowid spellings shadowed private capture"

end SQLeanite.Tests
