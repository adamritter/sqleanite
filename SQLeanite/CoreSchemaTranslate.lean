import SQLeanite.CoreData
import SQLeanite.SQLite.ColumnType

namespace SQLeanite
namespace CoreSQL

def unsupported (feature : String) : Except String α :=
  .error s!"unsupported general verified-MVP SQL: {feature}"

def canonical (name : String) : String := name.toLower

/-- Exact public type spelling after SQLite's standard-type normalization. -/
def declaredTypeName := SQLite.ColumnType.name

def ordinaryColumn (definition : ColumnDef) : Core.Column :=
  if (SQLite.ColumnType.adjusted definition.declaredType).isEmpty then
    { name := definition.name, notNull := definition.notNull }
  else Core.Column.typed definition.name (declaredTypeName definition.declaredType) definition.notNull

def columnAllowed (column : ColumnDef) : Bool :=
  SQLite.ColumnType.valid column.declaredType &&
  (column.defaultValue.isSome == column.defaultSql.isSome) &&
  column.generated.isNone && !column.unique &&
  column.references.isNone && column.check.isNone && (!column.autoIncrement || column.primaryKey) &&
  column.collation.toLower == "binary" &&
  (column.conflict == .abort || column.conflict == .ignore || column.conflict == .replace) &&
  (column.primaryKey || column.conflict == .abort) &&
  (column.notNullConflict == .abort || column.notNullConflict == .ignore || column.notNullConflict == .replace) &&
  (column.notNull || column.notNullConflict == .abort)

def columnWithConflicts (definition : ColumnDef) (column : Core.Column) : Except String Core.Column := do
  let policy ← match definition.notNullConflict with
    | .abort => pure Core.NotNullConflict.abort
    | .ignore => pure Core.NotNullConflict.ignore
    | .replace => pure Core.NotNullConflict.replace
    | _ => unsupported "schema NOT NULL conflict policy"
  let column ← match column.withNotNullConflict policy with
    | some column => pure column
    | none => unsupported "NOT NULL policy without an explicit constraint"
  let primary ← match definition.conflict with
    | .abort => pure Core.NotNullConflict.abort
    | .ignore => pure Core.NotNullConflict.ignore
    | .replace => pure Core.NotNullConflict.replace
    | _ => unsupported "schema PRIMARY KEY conflict policy"
  let column ← match column.withPrimaryConflict primary with
    | some column => pure column
    | none => unsupported "primary policy without a PRIMARY KEY constraint"
  for (_, source) in definition.earlierDefaults do
    unless (ColumnDefault.fromSource source).isSome do unsupported "earlier DEFAULT expression"
  match definition.defaultSql with
  | none => return column
  | some source =>
      let some spec := ColumnDefault.fromSource source | unsupported "DEFAULT expression"
      return { column with defaultValue := some spec }

/-- Mark a table-level key without changing column order, names or other
column constraints. The caller validates that its target exists uniquely. -/
def markPrimaryColumn (name : String) (definitions : Array ColumnDef) (conflict : ConflictAction := .abort)
    (autoIncrement : Bool := false) : Array ColumnDef :=
  definitions.map fun column =>
    if canonical column.name == canonical name then { column with primaryKey := true, conflict, autoIncrement }
    else column

theorem markPrimaryColumn_size (name : String) (definitions : Array ColumnDef) (conflict : ConflictAction := .abort)
    (autoIncrement : Bool := false) :
    (markPrimaryColumn name definitions conflict autoIncrement).size = definitions.size := by
  simp [markPrimaryColumn]

theorem markPrimaryColumn_names (name : String) (definitions : Array ColumnDef) (conflict : ConflictAction := .abort)
    (autoIncrement : Bool := false) :
    (markPrimaryColumn name definitions conflict autoIncrement).toList.map (·.name) = definitions.toList.map (·.name) := by
  simp only [markPrimaryColumn, Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro column _
  simp only [Function.comp_apply]
  split <;> rfl

/-- Single-column table keys lower to the same Core key as column declarations.
Unlike column-level INTEGER PRIMARY KEY DESC, table-level DESC still aliases
the rowid in SQLite. Its index-only collation/direction therefore has no effect.
TEXT keys require the admitted ascending BINARY index representation. -/
def tablePrimaryColumns (definitions : Array ColumnDef)
    (constraints : Array TableConstraintDef) : Except String (Array ColumnDef) :=
  match constraints.toList with
  | [] => .ok definitions
  | [constraint] => do
      unless constraint.primaryKey && constraint.columns.size == 1 &&
          constraint.check.isNone &&
          (constraint.conflict == .abort || constraint.conflict == .ignore || constraint.conflict == .replace) do
        unsupported "table constraint"
      unless constraint.collations.size == 1 && constraint.descending.size == 1 do
        unsupported "table key metadata width"
      if definitions.any (·.primaryKey) then throw "table has more than one primary key"
      let name := constraint.columns[0]!
      let column ← match definitions.toList.find? (fun column => canonical column.name == canonical name) with
        | some column => .ok column
        | none => .error s!"no such column: {name}"
      let integerAlias := SQLite.ColumnType.standard column.declaredType == some "INTEGER"
      unless integerAlias || (!constraint.descending[0]! &&
          constraint.collations[0]!.all (fun name => canonical name == "binary")) do
        unsupported "table key index collation or direction"
      return markPrimaryColumn name definitions constraint.conflict constraint.autoIncrement
  | _ => unsupported "multiple table constraints"

theorem tablePrimaryColumns_empty (definitions : Array ColumnDef) :
    tablePrimaryColumns definitions #[] = .ok definitions := rfl

def schema (name : String) (definitions : Array ColumnDef)
    (constraints : Array TableConstraintDef) : Except String Core.Schema := do
  let definitions ← tablePrimaryColumns definitions constraints
  unless definitions.toList.all columnAllowed do
    throw "unsupported general verified-MVP SQL: column constraint"
  let foldedNames := definitions.toList.map (fun column => canonical column.name)
  unless foldedNames.eraseDups.length == foldedNames.length do
    throw "duplicate column name"
  let primaryKeys := definitions.toList.filter (·.primaryKey)
  if primaryKeys.isEmpty then
    let visibleColumns ← definitions.toList.mapM fun column => columnWithConflicts column (ordinaryColumn column)
    unless !visibleColumns.isEmpty do throw "table must have at least one column"
    if visibleColumns.any (fun column => canonical column.name == "__sqleanite_rowid") then
      throw "reserved verified column name: __sqleanite_rowid"
    return {
      name := name
      columns := visibleColumns ++ [Core.hiddenRowidColumn]
      primaryKey := visibleColumns.length
      declaredPrimaryKey := visibleColumns.length + 1 }
  unless primaryKeys.length = 1 do
    throw "verified MVP tables require exactly one PRIMARY KEY"
  let primaryKey ← match definitions.findIdx? (fun column => column.primaryKey) with
    | some index => .ok index
    | none => .error "verified MVP table has no primary key"
  let primaryDefinition ← match definitions[primaryKey]? with
    | some column => .ok column
    | none => .error "verified MVP primary-key index is out of bounds"
  let integerAlias := SQLite.ColumnType.standard primaryDefinition.declaredType == some "INTEGER"
  unless !primaryDefinition.autoIncrement || integerAlias do
    throw "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"
  let ordinary := ordinaryColumn primaryDefinition
  let indexedType : Core.IndexedType := {
    declaredType := ordinary.declaredType, explicitEmptyType := ordinary.explicitEmptyType,
    explicitEmptyTypeOnly := fun present => (ordinary.explicitEmptyTypeOnly present).1 }
  let visibleColumns ← definitions.toList.mapM fun column => columnWithConflicts column <|
    if column.primaryKey then {
      name := column.name
      notNull := integerAlias || column.notNull
      integerPrimaryKey := integerAlias
      integerPrimaryNotNull := integerAlias && column.notNull
      autoIncrement := integerAlias && column.autoIncrement
      autoIncrementOnly := fun present => (Bool.and_eq_true_iff.mp present).1
      textPrimaryKey := !integerAlias
      indexedType := if integerAlias || indexedType.declaredType == "TEXT" then none else some indexedType
      indexedTypeOnly := by
        split
        · simp
        · next custom => simp_all }
    else ordinaryColumn column
  if integerAlias then return {
    name := name
    columns := visibleColumns
    primaryKey
    declaredPrimaryKey := primaryKey }
  else
    let hiddenName := "__sqleanite_rowid"
    if visibleColumns.any (fun column => canonical column.name == hiddenName) then
      throw s!"reserved verified column name: {hiddenName}"
    return {
      name := name
      columns := visibleColumns ++ [Core.hiddenRowidColumn]
      primaryKey := visibleColumns.length
      declaredPrimaryKey := primaryKey }

def indexColumnName? : Expr → Option String
  | .column none name => some name
  | .call "lean_dqs" #[.literal (.text name)] false => some name
  | .call "__sqlean_boolean_true" #[] false => some "true"
  | .call "__sqlean_boolean_false" #[] false => some "false"
  | _ => none

end CoreSQL
end SQLeanite
