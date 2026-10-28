import SQLeaniteTests.ExpressionIndexes

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectCollatedIndexes : IO Unit := do
  let mut state := Core.State.empty
  for sql in ["CREATE TABLE t(id INTEGER PRIMARY KEY,v TEXT,n);",
      "INSERT INTO t VALUES(1,'A',1),(2,'b',2),(3,NULL,3);",
      "CREATE UNIQUE INDEX ci ON t(v COLLATE NOCASE);"] do
    state := (← foreignStatement state sql).1
  let some source := state.catalog.current.filteredIndexes.head? | fail "missing collated index source"
  let prepared ← match CorePartialIndex.prepare state.database source with
    | .ok value => pure value | .error message => fail message
  unless prepared.collation == .nocase && prepared.collationName == "NOCASE" &&
      source.definition.column == some "v" do fail "wrong key collation or column identity"
  state := (← foreignStatement state "INSERT OR IGNORE INTO t VALUES(4,'a',4);").1
  unless state.lastChanges == 0 do fail "NOCASE duplicate was not skipped"
  state := (← foreignStatement state "INSERT OR REPLACE INTO t VALUES(4,'a',4);").1
  let some table := CoreNames.table? state.database "t" | fail "missing collated owner"
  unless table.rows.map (·.rowid.value) == [2,3,4] do fail "NOCASE victim was not removed"
  let (_,metadata) ← foreignStatement state "PRAGMA index_xinfo(ci);"
  let expected ← match [[Value.integer 0,.integer 1,.text "v",.integer 0,.text "NOCASE",.integer 1],
      [.integer 1,.integer (-1),.null,.integer 0,.text "BINARY",.integer 0]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless metadata.flatMap (·.rows) == expected do fail "collation metadata does not match the physical key"
  for sql in ["CREATE TABLE d(id INTEGER PRIMARY KEY,v TEXT COLLATE NOCASE);",
      "INSERT INTO d VALUES(1,'A'),(2,'b');", "CREATE INDEX di ON d(v) WHERE v='a';"] do
    state := (← foreignStatement state sql).1
  let some source := state.catalog.current.filteredIndexes.find? (fun source => source.definition.name == "di") |
    fail "missing declared-collation source"
  let prepared ← match CorePartialIndex.prepare state.database source with
    | .ok value => pure value | .error message => fail message
  let rows ← match CorePartialIndex.sortedRows prepared with
    | .ok value => pure value | .error message => fail message
  unless rows.map (·.rowid.value) == [1] do fail "partial predicate ignored the declared NOCASE collation"

end SQLeanite.Tests
