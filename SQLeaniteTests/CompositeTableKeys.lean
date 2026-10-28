import SQLeaniteTests.CompositeIndexes

namespace SQLeanite.Tests
open SQLeanite SQLeanite.TestData

def expectCompositeTableKeys : IO Unit := do
  if (CoreSQL.execute Core.State.empty "CREATE TABLE x(a,b,PRIMARY KEY(a,b));").isOk then
    fail "the source-free AST model admitted an unenforced compound constraint"
  let mut state := Core.State.empty
  for sql in ["CREATE TABLE t(a TEXT,b INTEGER,v,PRIMARY KEY(a,b));",
      "INSERT INTO t VALUES('A',1,'one'),('A',2,'two'),('b',1,'three'),(NULL,1,'nil'),('A',NULL,'nil2');"] do
    state := (← foreignStatement state sql).1
  let some table := CoreNames.table? state.database "t" | fail "missing compound-key table"
  let some source := state.catalog.current.filteredIndexes.head? | fail "missing automatic compound key"
  unless source.automaticTable? == some table.catalogSQL && source.automaticPrimary &&
      source.definition.keys.size == 2 && table.schema.hasHiddenRowid do
    fail "automatic key is not tied to its actual rowid-table declaration"
  let (_,metadata) ← foreignStatement state "PRAGMA table_info(t);"
  unless (metadata.flatMap (·.rows)).map (fun row => row[5]?) ==
      [some (PhysicalCodec.Value.integer ⟨1,by decide,by decide⟩),
       some (.integer ⟨2,by decide,by decide⟩),some (.integer ⟨0,by decide,by decide⟩)] do
    fail "compound primary-key ordinals were not exposed"
  state := (← foreignStatement state "INSERT OR IGNORE INTO t VALUES('A',1,'ignored');").1
  unless state.lastChanges == 0 do fail "automatic tuple conflict was not skipped"
  state := (← foreignStatement state "INSERT OR REPLACE INTO t VALUES('A',1,'replaced');").1
  let some table := CoreNames.table? state.database "t" | fail "lost automatic key owner"
  unless table.rows.map (·.rowid.value) == [2,3,4,5,6] && state.lastInsertRowid == 6 do
    fail "automatic key replacement lost actual rowid allocation or its victim"
  let (_,metadata) ← foreignStatement state "PRAGMA index_list(t);"
  let expected ← match [[Value.integer 0,.text "sqlite_autoindex_t_1",.integer 1,.text "pk",.integer 0]].mapM (List.mapM SQLSurface.value) with
    | .ok value => pure value | .error message => fail message
  unless metadata.flatMap (·.rows) == expected do fail "automatic compound key lost its pk origin"

end SQLeanite.Tests
