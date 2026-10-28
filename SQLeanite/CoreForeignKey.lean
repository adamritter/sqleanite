import SQLeanite.CoreConnectionSQL

/-! Connection-level immediate NO ACTION checks for retained single-column
REFERENCES declarations. Physical row and index invariants remain Core's
ordinary checked operations; foreign-key rejection precedes publication. -/
namespace SQLeanite.CoreForeignKey

structure Edge where
  child : String
  column : Nat
  parent : String
  parentColumn : Nat
  affinity : SQLite.Affinity

structure Violation where
  child : String
  column : Nat
  rowid : Core.Integer
  value : Core.Value
  deriving DecidableEq

def keyEqual (left right : Violation) : Bool :=
  left.child == right.child && left.column == right.column && left.value == right.value

def target? : Statement → Option String
  | .insert name .. | .insertSelect name .. | .update name .. | .delete name .. | .dropTable name _ => some name
  | .upsert base .. => target? base
  | _ => none

def assigned (schema : Core.Schema) (assignments : Array (String × Expr)) (position : Nat) : Bool :=
  assignments.any fun (name, _) => schema.column? name == some position

def affectedAssignment (table : Core.Table) (assignments : Array (String × Expr)) (position : Nat) : Bool :=
  let direct := assignments.toList.filterMap (fun (name,_) => table.schema.column? name)
  let generated := match table.catalogSource with
    | none => []
    | some source => source.compiledGeneratedColumns.toOption.getD []
  (CoreGeneratedSyntax.affected generated direct).contains position

def childActive (statement : Statement) (schema : Core.Schema) (position : Nat) : Bool :=
  match statement with
  | .update _ _ assignments .. => assigned schema assignments position
  | .dropTable .. => false
  | _ => true

abbrev parentPosition := CoreForeignKeyData.parentPosition

/-- Bind only relationships affected by this statement. An unrelated UPDATE
must not revalidate an old orphan or require its missing parent table. -/
def edges (state : Core.State) (statement : Statement) : Except String (List Edge) := do
  let some target := target? statement | return []
  if CoreSQL.schemaNoop state statement then return []
  let target := CoreSQL.resolveTableName state target
  let mut result := []
  for child in state.database.tables do
    let keys ← match child.catalogSource with
      | none => pure [] | some source => source.compiledForeignKeys
    for (position, key) in keys.reverse do
      let childWrite := child.schema.name.toLower == target.toLower &&
        (match statement with
        | .update _ _ assignments .. => affectedAssignment child assignments position
        | _ => childActive statement child.schema position)
      let parentWrite := key.table.toLower == target.toLower &&
        (match statement with
        | .update _ _ assignments .. =>
            match CoreNames.table? state.database key.table with
            | none => false
            | some parent =>
                match key.column with
                | some name => (parent.schema.declaredColumn? name).any (affectedAssignment parent assignments)
                | none => (parent.schema.declaredPrimaryKey?).any (affectedAssignment parent assignments)
        | _ => true)
      unless childWrite || parentWrite do continue
      let some parent := CoreNames.table? state.database key.table | throw s!"no such table: main.{key.table}"
      let parentColumn ← parentPosition child key parent
      let some column := parent.schema.columns[parentColumn]? | throw "missing foreign-key parent column"
      result := result ++ [{
        child := child.schema.name
        column := position
        parent := parent.schema.name
        parentColumn := parentColumn
        affinity := column.affinity }]
  return result

def violations (database : Core.Database) (edges : List Edge) : List Violation := Id.run do
  let mut result := []
  for edge in edges do
    let some child := database.findTable? edge.child | continue
    let parentRows := (database.findTable? edge.parent).map (·.rows) |>.getD []
    for row in child.rows do
      let value := row.value edge.column
      if value == .null then continue
      let value := SQLite.PhysicalAffinity.comparison edge.affinity value
      let found := parentRows.any fun candidate =>
        (PhysicalQuery.sqlEquals value (candidate.value edge.parentColumn)) == .true
      unless found do result := { child := edge.child, column := edge.column, rowid := row.rowid, value } :: result
  return result

def written (state : Core.State) (violation : Violation) : Bool :=
  state.foreignWrites.any fun write => write.table == violation.child && write.rowid == violation.rowid &&
    write.columns.all (fun positions => positions.contains violation.column)

def compatible (old current : List Violation) (after : Core.State) (violation : Violation) : Bool :=
  decide ((current.filter (keyEqual violation)).length ≤ (old.filter (keyEqual violation)).length) &&
    !written after violation

def requireTransition (before after : Core.State) (edges : List Edge) : Except String Unit :=
  let old := violations before.database edges
  let current := violations after.database edges
  if current.all (compatible old current after) then .ok ()
  else .error "FOREIGN KEY constraint failed"

theorem requireTransition_clause {before after : Core.State} {edges : List Edge}
    (success : requireTransition before after edges = .ok ())
    {violation : Violation} (member : violation ∈ violations after.database edges) :
    compatible (violations before.database edges) (violations after.database edges) after violation = true := by
  unfold requireTransition at success
  dsimp only at success
  split at success
  · next allowed => exact List.all_eq_true.mp allowed violation member
  · contradiction

def boolArgument (expression : Expr) : Except String Bool := do
  let some source := CoreSchemaPragma.argumentName expression | throw "unsupported PRAGMA argument"
  let name := source.toLower
  if ["on", "yes", "true"].contains name then return true
  if !source.toList.head?.any (fun c => '0' ≤ c && c ≤ '9') then return false
  return SQLite.ApplicationHeader.atoi source % 256 != 0

def pragma (state : Core.State) (argument : Option Expr) (schema : Option String) :
    Except String (Core.State × List Core.Result) := do
  if schema.any (fun name => !["main", "temp"].contains name.toLower) then
    throw s!"unknown database {schema.getD ""}"
  match argument with
  | none =>
      let value ← SQLSurface.value (.integer (if state.foreignKeys then 1 else 0))
      return (state, [{ rows := [[value]] }])
  | some argument =>
      if state.transactionSnapshot.isSome then return (state, [{}])
      let enabled ← boolArgument argument
      return ({ state with foreignKeys := enabled }, [{}])

theorem pragma_set_in_transaction (state : Core.State) (argument : Expr)
    (active : state.transactionSnapshot.isSome = true) :
    pragma state (some argument) none = .ok (state, [{}]) := by
  simp [pragma, active, pure, Except.pure]

end SQLeanite.CoreForeignKey
