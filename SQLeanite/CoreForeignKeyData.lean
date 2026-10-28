import SQLeanite.CoreEngine.RowValue
import SQLeanite.CoreNames
import SQLeanite.SQLite.SchemaHash

/-! Read-only inspection of retained single-column REFERENCES declarations. -/
namespace SQLeanite.CoreForeignKeyData

def keys (table : Core.Table) : Except String (List (Nat × ForeignKeyDef)) :=
  match table.catalogSource with
  | none => .ok []
  | some source => source.compiledForeignKeys

def parentPosition (child : Core.Table) (key : ForeignKeyDef) (parent : Core.Table) : Except String Nat := do
  let mismatch := s!"foreign key mismatch - \"{child.schema.name}\" referencing \"{key.table}\""
  let position ← match key.column with
    | none => match parent.schema.declaredPrimaryKey? with
        | none => throw mismatch | some position => pure position
    | some name => match parent.schema.declaredColumn? name with
        | none => throw mismatch | some position => pure position
  unless parent.schema.declaredPrimaryKey? == some position ||
      parent.indexes.any (fun index => index.unique && index.column == position) do throw mismatch
  return position

def listRows (database : Core.Database) (target : String) : Except String (List (List Value)) := do
  let some table := CoreNames.table? database target | return []
  let declarations ← keys table
  declarations.reverse.zipIdx.mapM fun ((position, key), id) => do
    let some column := table.schema.catalogColumns[position]? | throw "missing foreign-key child column"
    return [.integer id, .integer 0, .text key.table, .text column.name,
      (key.column.map Value.text).getD .null, .text "NO ACTION", .text "NO ACTION", .text "NONE"]

def referenceSatisfied (parent : Option Core.Table) (position : Nat) (value : Core.Value) : Bool :=
  if value == .null then true else
    parent.any fun parent =>
      let affinity := ((parent.schema.columns[position]?).map (·.affinity)).getD .blob
      let value := SQLite.PhysicalAffinity.comparison affinity value
      parent.rows.any fun row => PhysicalQuery.sqlEquals value (row.value position) == .true

theorem referenceSatisfied_null (parent : Option Core.Table) (position : Nat) :
    referenceSatisfied parent position .null = true := rfl

structure Inspection where
  position : Nat
  key : ForeignKeyDef
  id : Nat
  parent : Option Core.Table
  parentColumn : Nat

def tableCheckRows (database : Core.Database) (child : Core.Table) : Except String (List (List Value)) := do
  let declarations ← keys child
  let prepared ← declarations.reverse.zipIdx.mapM fun ((position, key), id) => do
    let parent := CoreNames.table? database key.table
    let parentColumn ← match parent with
      | none => pure 0
      | some parent => parentPosition child key parent
    return ({ position, key, id, parent, parentColumn } : Inspection)
  let mut reversed := []
  for row in child.rows do
    for declaration in prepared do
      unless referenceSatisfied declaration.parent declaration.parentColumn (row.value declaration.position) do
        reversed := [.text child.schema.name, .integer row.rowid.value,
          .text declaration.key.table, .integer declaration.id] :: reversed
  return reversed.reverse

def checkRows (database : Core.Database) (schema : Option String) (target : Option String)
    (tableOrder : Option (List String) := none) :
    Except String (List (List Value)) := do
  let tables ← match target with
    | none => pure ((tableOrder.getD (SQLite.SchemaHash.order (database.tables.map (·.schema.name)))).filterMap database.findTable?)
    | some name => match CoreNames.table? database name with
        | none => throw s!"no such table: {(schema.map (· ++ ".")).getD ""}{name}"
        | some table => pure [table]
  return (← tables.mapM (tableCheckRows database)).flatten

end SQLeanite.CoreForeignKeyData
