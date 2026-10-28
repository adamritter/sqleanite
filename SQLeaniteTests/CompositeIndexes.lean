import SQLeaniteTests.CollatedIndexes

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectCompositeIndexes : IO Unit := do
  let mut state := Core.State.empty
  for sql in ["CREATE TABLE t(id INTEGER PRIMARY KEY,a,b,n);",
      "INSERT INTO t VALUES(1,'A',1,1),(2,'A',2,2),(3,'b',1,3),(4,NULL,1,4),(5,'A',NULL,5);",
      "CREATE UNIQUE INDEX ci ON t(a,b);"] do
    state := (← foreignStatement state sql).1
  let some source := state.catalog.current.filteredIndexes.head? | fail "missing composite index source"
  let prepared ← match CorePartialIndex.prepare state.database source with
    | .ok value => pure value | .error message => fail message
  let entries ← match CorePartialIndex.sortedKeys prepared with
    | .ok value => pure value | .error message => fail message
  unless entries.map (·.rowid.value) == [4,5,1,2,3] && entries.all (fun entry => entry.values.length == 2) do
    fail "tuple ordering, key widths or actual rowids were lost"
  for entry in entries do
    unless CoreIndexKey.fromValues entry.recordValues == some entry do fail "physical key tuple lost its record roundtrip"
  state := (← foreignStatement state "INSERT INTO t VALUES(6,'A',3,6),(7,'A',NULL,7);").1
  state := (← foreignStatement state "INSERT OR IGNORE INTO t VALUES(8,'A',1,8);").1
  unless state.lastChanges == 0 do fail "tuple duplicate was not skipped"
  state := (← foreignStatement state "INSERT OR REPLACE INTO t VALUES(8,'A',1,8);").1
  let some table := CoreNames.table? state.database "t" | fail "missing tuple owner"
  unless (table.rows.map (·.rowid.value)) == [2,3,4,5,6,7,8] do fail "tuple REPLACE removed a prefix-only neighbor or retained its victim"
  let (_,metadata) ← foreignStatement state "PRAGMA index_xinfo(ci);"
  let expected ← match [[Value.integer 0,.integer 1,.text "a",.integer 0,.text "BINARY",.integer 1],
      [.integer 1,.integer 2,.text "b",.integer 0,.text "BINARY",.integer 1],
      [.integer 2,.integer (-1),.null,.integer 0,.text "BINARY",.integer 0]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless metadata.flatMap (·.rows) == expected do fail "composite metadata omitted a key or its rowid suffix"

end SQLeanite.Tests
