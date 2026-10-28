import SQLeanite.Core.Table

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

def row (position : Nat) (value : Core.Value) (before : Core.Row) : Core.Row :=
  { before with values := insertAt before.values position value }

theorem row_rowid (position : Nat) (value : Core.Value) (before : Core.Row) :
    (row position value before).rowid = before.rowid := rfl

def indexes (position : Nat) (before : List Core.Index) : List Core.Index :=
  before.map fun index => { index with column := shifted position index.column }

def addedValue (before : Core.Table) (column : Core.Column) : Except String Core.Value :=
  if before.rows.isEmpty then .ok .null else column.defaultForRecord

def table (before : Core.Table) (column : Core.Column) : Except String Core.Table := do
  let value ← addedValue before column
  let position := before.schema.catalogColumns.length
  Core.Table.rebuild (schema before.schema column) (indexes position before.indexes)
    (before.rows.map (row position value))

theorem table_exact {before after : Core.Table} {column : Core.Column}
    (success : table before column = .ok after) :
    ∃ value, addedValue before column = .ok value ∧
      after.schema = schema before.schema column ∧
      after.indexes = indexes before.schema.catalogColumns.length before.indexes ∧
      after.rows = before.rows.map (row before.schema.catalogColumns.length value) := by
  cases evaluated : addedValue before column with
  | error message => simp [table, evaluated, bind, Except.bind] at success
  | ok value =>
      simp only [table, evaluated, bind, Except.bind] at success
      exact ⟨value, rfl, Core.Table.rebuild_exact success⟩

end SQLeanite.CoreSchemaAdd
