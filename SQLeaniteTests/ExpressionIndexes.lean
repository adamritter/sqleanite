import SQLeaniteTests.PartialIndexes

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectExpressionIndexes : IO Unit := do
  let mut state := Core.State.empty
  for sql in ["CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n INTEGER);",
      "INSERT INTO t VALUES(1,'A',-2),(2,'b',0),(3,NULL,2);",
      "CREATE UNIQUE INDEX ei ON t(lower(v));"] do
    state := (← foreignStatement state sql).1
  let some source := state.catalog.current.filteredIndexes.head? | fail "missing expression source"
  unless source.definition.column.isNone && !source.definition.partialIndex do
    fail "expression source was classified as a partial column index"
  let prepared ← match CorePartialIndex.prepare state.database source with
    | .ok value => pure value | .error message => fail message
  let keys ← match CorePartialIndex.sortedRows prepared with
    | .ok value => pure value | .error message => fail message
  let expected ← match [Value.null,.text "a",.text "b"].mapM SQLSurface.value with
    | .ok value => pure value | .error message => fail message
  unless keys.map (·.rowid.value) == [3,1,2] && keys.map (·.value 0) == expected do
    fail "expression keys lost scalar values, NULL ordering or actual rowids"
  let (_,clock) ← match CoreTokenGrammar.parseCertified "CREATE INDEX cx ON t(current_date);" with
    | .error message => fail message
    | .ok parsed => pure (parsed.tokens, parsed.statements)
  unless clock.size == 1 do fail "current-time keyword did not retain a checked statement"
  let before := state
  state := (← foreignStatement state "INSERT OR IGNORE INTO t VALUES(4,'a',9);").1
  unless state.database.contents == before.database.contents && state.lastChanges == 0 do
    fail "expression IGNORE published a duplicate"
  state := (← foreignStatement state "INSERT OR REPLACE INTO t VALUES(4,'a',9);").1
  let some table := CoreNames.table? state.database "t" | fail "missing expression owner"
  unless table.rows.map (·.rowid.value) == [2,3,4] do
    fail "expression REPLACE did not remove the actual victim"
  let (_,metadata) ← foreignStatement state "PRAGMA index_xinfo(ei);"
  let expected ← match [[Value.integer 0,.integer (-2),.null,.integer 0,.text "BINARY",.integer 1],
      [.integer 1,.integer (-1),.null,.integer 0,.text "BINARY",.integer 0]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless metadata.flatMap (·.rows) == expected do fail "expression metadata lost cid=-2"

end SQLeanite.Tests
