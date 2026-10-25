import SQLeanite.Core

namespace SQLeanite.CoreSchemaDrop

/-- Removing a table also removes the indexes owned by that table. Other
proof-carrying table values are retained without rebuilding their row trees. -/
def table (database : Core.Database) (name : String) : Except String Core.Database :=
  Core.Database.rebuild (database.tables.filter fun stored => stored.schema.name != name)

theorem table_exact {database next : Core.Database} {name : String}
    (success : table database name = .ok next) :
    next.tables = database.tables.filter (fun stored => stored.schema.name != name) :=
  Core.Database.rebuild_tables success

theorem table_member {database next : Core.Database} {name : String}
    (success : table database name = .ok next) (stored : Core.Table) :
    stored ∈ next.tables ↔ stored ∈ database.tables ∧ stored.schema.name ≠ name := by
  rw [table_exact success]
  simp

/-- Removing an explicit index retains the schema, row tree and declared-key
map. The existing checked index constructor retains its invariant proofs. -/
def index (stored : Core.Table) (name : String) : Except String Core.Table :=
  stored.withIndexes (stored.indexes.filter fun candidate => candidate.name != name)

theorem index_exact {stored next : Core.Table} {name : String}
    (success : index stored name = .ok next) :
    next.schema = stored.schema ∧
      next.indexes = stored.indexes.filter (fun candidate => candidate.name != name) ∧
      next.rows = stored.rows :=
  Core.Table.withIndexes_exact success

end SQLeanite.CoreSchemaDrop
