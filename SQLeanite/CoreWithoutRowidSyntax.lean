import SQLeanite.CoreStrictSyntax
import SQLeanite.SQLite.Scalar

/-! Source-aware WITHOUT ROWID declarations lower to an ordinary logical row
store with a private ordinal. The actual primary key remains a source program. -/
namespace SQLeanite.CoreWithoutRowidSyntax

def primaryColumns (table : String) (columns : Array ColumnDef)
    (constraints : Array TableConstraintDef) : Except String (List String) := do
  let inline := columns.toList.filter (·.primaryKey)
  let declared := constraints.toList.filter (·.primaryKey)
  if inline.length + declared.length > 1 then throw s!"table \"{table}\" has more than one primary key"
  let keys ← match inline,declared with
    | [column],[] => pure [column.name]
    | [],[constraint] => pure constraint.columns.toList
    | _,_ => throw s!"PRIMARY KEY missing on table {table}"
  if keys.isEmpty then throw s!"PRIMARY KEY missing on table {table}"
  for name in keys do
    unless columns.any (fun column => column.name.toLower == name.toLower) do throw s!"no such column: {name}"
  return keys

def lower (table : String) (columns : Array ColumnDef) (constraints : Array TableConstraintDef)
    (strict : Bool) : Except String (Array ColumnDef × Array TableConstraintDef) := do
  if columns.any (·.autoIncrement) || constraints.any (·.autoIncrement) then
    throw "AUTOINCREMENT not allowed on WITHOUT ROWID tables"
  let keys ← primaryColumns table columns constraints
  unless columns.all (fun column => !column.primaryKey || column.conflict == .abort) &&
      constraints.all (fun constraint => !constraint.primaryKey || constraint.conflict == .abort) do
    throw "unsupported WITHOUT ROWID primary conflict policy"
  let columns ← if strict then CoreStrictSyntax.lower table columns constraints else pure columns
  let lowered := columns.map (fun column => { column with
    primaryKey := false, unique := false, conflict := .abort, autoIncrement := false
    notNull := column.notNull || keys.any (fun name => name.toLower == column.name.toLower) })
  return (lowered,constraints.filter (fun constraint => constraint.check.isSome || constraint.references.isSome))

end SQLeanite.CoreWithoutRowidSyntax
