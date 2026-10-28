import SQLeanite.Core.Table

namespace SQLeanite.CoreSchemaDropColumn

def removeAt (input : List α) (position : Nat) : List α :=
  input.take position ++ input.drop (position + 1)

theorem removeAt_length (input : List α) (position : Nat) (bound : position < input.length) :
    (removeAt input position).length + 1 = input.length := by
  simp only [removeAt, List.length_append, List.length_take, List.length_drop]
  rw [Nat.min_eq_left (Nat.le_of_lt bound)]
  omega

def shifted (position index : Nat) : Nat :=
  if position < index then index - 1 else index

def schema (before : Core.Schema) (position : Nat) : Core.Schema :=
  { before with
    columns := removeAt before.columns position
    primaryKey := shifted position before.primaryKey
    declaredPrimaryKey := shifted position before.declaredPrimaryKey }

def row (position : Nat) (before : Core.Row) : Core.Row :=
  { before with values := removeAt before.values position }

theorem row_rowid (position : Nat) (before : Core.Row) :
    (row position before).rowid = before.rowid := rfl

def indexes (position : Nat) (before : List Core.Index) : List Core.Index :=
  before.map fun index => { index with column := shifted position index.column }

/-- A public column must remain. Neither a rowid alias, a declared primary
key nor any indexed column can be removed by this schema operation. -/
def allowed (before : Core.Table) (position : Nat) : Bool :=
  position < before.schema.catalogColumns.length && 1 < before.schema.catalogColumns.length &&
    position != before.schema.primaryKey && before.schema.declaredPrimaryKey? != some position &&
    !(before.indexes.any fun index => index.column == position)

def table (before : Core.Table) (position : Nat) : Except String Core.Table :=
  if allowed before position then
    Core.Table.rebuild (schema before.schema position) (indexes position before.indexes)
      (before.rows.map (row position))
  else .error "cannot drop a missing, last, primary-key or indexed column"

theorem table_allowed {before after : Core.Table} {position : Nat}
    (success : table before position = .ok after) : allowed before position = true := by
  unfold table at success
  split at success
  · assumption
  · contradiction

theorem table_exact {before after : Core.Table} {position : Nat}
    (success : table before position = .ok after) :
    after.schema = schema before.schema position ∧
      after.indexes = indexes position before.indexes ∧
      after.rows = before.rows.map (row position) := by
  have permitted := table_allowed success
  simp only [table, permitted, ↓reduceIte] at success
  exact Core.Table.rebuild_exact success

end SQLeanite.CoreSchemaDropColumn
