import SQLeanite.Core

namespace SQLeanite.CoreSchemaRename

/-- Only the requested column's spelling changes. Positions, values, rowids
and all column properties used by the Core remain unchanged. -/
def columns (input : List Core.Column) (target : Nat) (name : String) : List Core.Column :=
  input.zipIdx.map fun (column, index) =>
    if index == target then { column with name } else column

theorem columns_length (input : List Core.Column) (target : Nat) (name : String) :
    (columns input target name).length = input.length := by
  simp [columns]

def column (stored : Core.Table) (target : Nat) (name : String) : Except String Core.Table :=
  Core.Table.rebuild { stored.schema with columns := columns stored.schema.columns target name }
    stored.indexes stored.rows

theorem column_exact {stored next : Core.Table} {target : Nat} {name : String}
    (success : column stored target name = .ok next) :
    next.schema = { stored.schema with columns := columns stored.schema.columns target name } ∧
      next.indexes = stored.indexes ∧ next.rows = stored.rows :=
  Core.Table.rebuild_exact success

/-- SQLite renames its automatic primary-key index with the table. User-named
indexes retain their own names and column positions. -/
def indexes (stored : Core.Table) (name : String) : List Core.Index :=
  stored.indexes.map fun index =>
    if index.isImplicitPrimary stored.schema then
      { index with name := "sqlite_autoindex_" ++ name ++ "_1" }
    else index

def table (stored : Core.Table) (name : String) : Except String Core.Table :=
  Core.Table.rebuild { stored.schema with name } (indexes stored name) stored.rows

theorem table_exact {stored next : Core.Table} {name : String}
    (success : table stored name = .ok next) :
    next.schema = { stored.schema with name } ∧
      next.indexes = indexes stored name ∧ next.rows = stored.rows :=
  Core.Table.rebuild_exact success

/-- Replacement matches the previous exact name, which may differ from the
new one. All other proof-carrying table objects are retained. -/
def replace (database : Core.Database) (oldName : String) (replacement : Core.Table) :
    Except String Core.Database :=
  Core.Database.rebuild (database.tables.map fun stored =>
    if stored.schema.name == oldName then replacement else stored)

theorem replace_exact {database next : Core.Database} {oldName : String} {replacement : Core.Table}
    (success : replace database oldName replacement = .ok next) :
    next.tables = database.tables.map (fun stored =>
      if stored.schema.name == oldName then replacement else stored) :=
  Core.Database.rebuild_tables success

end SQLeanite.CoreSchemaRename
