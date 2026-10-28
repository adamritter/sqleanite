import SQLeanite.Syntax.TableConstraintDef

/-! Retained single-column foreign-key declarations, in source declaration
order. Table keys bind their child name to the same visible column positions
as column REFERENCES clauses. Compound targets are not silently reduced. -/
namespace SQLeanite.CoreForeignKeySyntax

def columnKeys (columns : Array ColumnDef) : List (Nat × ForeignKeyDef) :=
  columns.toList.zipIdx.filterMap fun (column, position) => column.references.map (position, ·)

def tableKey (columns : Array ColumnDef) (constraint : TableConstraintDef) :
    Except String (Option (Nat × ForeignKeyDef)) := do
  let some key := constraint.references | return none
  unless constraint.columns.size == 1 && constraint.collations.isEmpty &&
      constraint.descending.isEmpty && !constraint.primaryKey && !constraint.autoIncrement &&
      constraint.check.isNone && constraint.conflict == .abort && !key.onDeleteCascade do
    throw "unsupported general verified-MVP SQL: table FOREIGN KEY constraint"
  let name := constraint.columns[0]!
  let some position := columns.findIdx? (fun column => column.name.toLower == name.toLower) |
    throw s!"unknown column \"{name}\" in foreign key definition"
  return some (position, key)

def collect (columns : Array ColumnDef) (constraints : Array TableConstraintDef) :
    Except String (List (Nat × ForeignKeyDef)) := do
  let tableKeys ← constraints.toList.mapM (tableKey columns)
  return columnKeys columns ++ tableKeys.filterMap id

theorem collect_no_tables (columns : Array ColumnDef) :
    collect columns #[] = .ok (columnKeys columns) := by
  simp [collect, bind, Except.bind, pure, Except.pure]

end SQLeanite.CoreForeignKeySyntax
