import SQLeanite.Core

namespace SQLeanite.CoreSchemaAdd

def insertAt (input : List α) (position : Nat) (value : α) : List α :=
  input.take position ++ [value] ++ input.drop position

theorem insertAt_length (input : List α) (position : Nat) (value : α) :
    (insertAt input position value).length = input.length + 1 := by
  have split := congrArg List.length (List.take_append_drop position input)
  simp only [List.length_append] at split
  simp only [insertAt, List.length_append, List.length_singleton]
  omega

def shifted (position index : Nat) : Nat :=
  if position ≤ index then index + 1 else index

/-- New visible columns precede the internal rowid column. Adjust positions,
including the no-declared-key sentinel, without changing existing definitions. -/
def schema (before : Core.Schema) (column : Core.Column) : Core.Schema :=
  let position := before.catalogColumns.length
  { before with
    columns := insertAt before.columns position column
    primaryKey := shifted position before.primaryKey
    declaredPrimaryKey := shifted position before.declaredPrimaryKey }

def row (position : Nat) (before : Core.Row) : Core.Row :=
  { before with values := insertAt before.values position .null }

theorem row_rowid (position : Nat) (before : Core.Row) :
    (row position before).rowid = before.rowid := rfl

def indexes (position : Nat) (before : List Core.Index) : List Core.Index :=
  before.map fun index => { index with column := shifted position index.column }

def table (before : Core.Table) (column : Core.Column) : Except String Core.Table :=
  let position := before.schema.catalogColumns.length
  Core.Table.rebuild (schema before.schema column) (indexes position before.indexes)
    (before.rows.map (row position))

theorem table_exact {before after : Core.Table} {column : Core.Column}
    (success : table before column = .ok after) :
    after.schema = schema before.schema column ∧
      after.indexes = indexes before.schema.catalogColumns.length before.indexes ∧
      after.rows = before.rows.map (row before.schema.catalogColumns.length) :=
  Core.Table.rebuild_exact success

end SQLeanite.CoreSchemaAdd
