import SQLeanite.Core.TableReplaceValues

/-! SQL identifiers compare with SQLite's ASCII case folding. Stored names and
Core commands retain their exact spelling; only the SQL binding layer resolves
an input identifier to an existing object. -/
namespace SQLeanite.CoreNames

def table? (database : Core.Database) (name : String) : Option Core.Table :=
  database.tables.find? (fun table => table.schema.name.toLower == name.toLower)

def tableName (database : Core.Database) (name : String) : String :=
  ((table? database name).map (·.schema.name)).getD name

def index? (table : Core.Table) (name : String) : Option Core.Index :=
  table.indexes.find? (fun index => index.name.toLower == name.toLower)

def indexName (table : Core.Table) (name : String) : String :=
  ((index? table name).map (·.name)).getD name

theorem table?_folded (database : Core.Database) (left right : String)
    (same : left.toLower = right.toLower) :
    table? database left = table? database right := by
  simp only [table?, same]

theorem tableName_found (database : Core.Database) (name : String) (table : Core.Table)
    (found : table? database name = some table) :
    tableName database name = table.schema.name := by
  simp [tableName, found]

/-- Resolving a SQL name produces the exact Core object, not a renamed copy. -/
theorem tableName_resolves (database : Core.Database) (name : String) (table : Core.Table)
    (found : table? database name = some table) :
    database.findTable? (tableName database name) = some table := by
  rw [tableName_found database name table found]
  exact database.findTable?_eq_some_of_mem (List.mem_of_find?_eq_some found)

theorem indexName_found (table : Core.Table) (name : String) (index : Core.Index)
    (found : index? table name = some index) :
    indexName table name = index.name := by
  simp [indexName, found]

end SQLeanite.CoreNames
