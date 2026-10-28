import SQLeaniteTests.RegisterInputPlans

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

private def partialRows (state : Core.State) : IO (List Int) := do
  let some source := state.catalog.current.filteredIndexes.head? | fail "partial index source is missing"
  let prepared ← match CorePartialIndex.prepare state.database source with
    | .ok prepared => pure prepared | .error message => fail message
  let rows ← match CorePartialIndex.sortedRows prepared with
    | .ok rows => pure rows | .error message => fail message
  return rows.map (·.rowid.value)

def expectPartialIndexes : IO Unit := do
  let mut state := Core.State.empty
  for source in ["CREATE TABLE t(id INTEGER PRIMARY KEY,n);",
      "INSERT INTO t VALUES(1,-2),(2,0),(3,2),(4,3),(5,NULL);",
      "CREATE INDEX pi ON t(n) WHERE n>0;"] do
    state := (← foreignStatement state source).1
  unless (← partialRows state) == [3,4] do fail "partial index included false/NULL predicate rows"
  let (_,metadata) ← foreignStatement state "PRAGMA index_list(t);"
  let expected ← match [[Value.integer 0,.text "pi",.integer 0,.text "c",.integer 1]].mapM (List.mapM SQLSurface.value) with
    | .ok rows => pure rows | .error message => fail message
  unless metadata.flatMap (·.rows) == expected do fail "partial index pragma omitted the actual partial flag"
  state := (← foreignStatement state "INSERT INTO t VALUES(6,7);").1
  state := (← foreignStatement state "UPDATE t SET n=-8 WHERE id=3;").1
  unless (← partialRows state) == [4,6] do fail "partial index missed entered/left keys"
  state := (← foreignStatement state "BEGIN;").1
  state := (← foreignStatement state "DELETE FROM t WHERE id=4;").1
  state := (← foreignStatement state "ROLLBACK;").1
  unless (← partialRows state) == [4,6] do fail "partial index lost transaction rollback data"
  state := (← foreignStatement state "DROP INDEX IF EXISTS pi;").1
  unless state.catalog.current.filteredIndexes.isEmpty do fail "partial index DROP left a source object"
  state := (← foreignStatement state "CREATE UNIQUE INDEX uq ON t(n) WHERE n>0;").1
  let before := state
  state := (← foreignStatement state "INSERT OR IGNORE INTO t VALUES(7,3);").1
  unless state.database.contents == before.database.contents && state.lastChanges == 0 &&
      state.lastInsertRowid == before.lastInsertRowid do
    fail "partial unique IGNORE published a candidate or changed its insertion register"
  state := (← foreignStatement state "INSERT OR REPLACE INTO t VALUES(7,3);").1
  unless (← partialRows state) == [7,6] && state.lastChanges == 1 && state.lastInsertRowid == 7 do
    fail "partial unique REPLACE retained a victim or lost its actual accepted point"

end SQLeanite.Tests
