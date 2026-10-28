import SQLeanite.CoreCollationSyntax

/-! Retained STORED generated-column programs. Dependency cycles are kept in
catalog metadata: SQLite diagnoses them when compiling a write, not CREATE. -/
namespace SQLeanite.CoreGeneratedSyntax

structure Spec where
  position : Nat
  name : String
  expression : Expr
  dependencies : List Nat

def validateDeclarations (columns : Array ColumnDef) (constraints : Array TableConstraintDef) : Except String Unit := do
  if columns.any (·.generated.isSome) && columns.all (·.generated.isSome) then
    throw "must have at least one non-generated column"
  for column in columns do
    if column.generated.isSome then
      unless column.generatedStored do throw "unsupported general verified-MVP SQL: VIRTUAL generated column"
      if column.defaultValue.isSome || !column.earlierDefaults.isEmpty then
        throw "cannot use DEFAULT on a generated column"
      if column.primaryKey || constraints.any (fun constraint => constraint.primaryKey &&
          constraint.columns.any (fun name => name.toLower == column.name.toLower)) then
        throw "generated columns cannot be part of the PRIMARY KEY"

def validateExpression (schema : Core.Schema) (expression : Expr) : Except String Unit := do
  if expression.any (fun node => match node with | .column (some _) _ => true | _ => false) then
    throw "the \".\" operator prohibited in generated columns"
  if expression.any (fun node => match node with
      | .scalarSubquery .. | .existsSubquery .. | .inSubquery .. => true | _ => false) then
    throw "subqueries prohibited in generated columns"
  if expression.any (fun node => match node with
      | .call name _ _ => ["random", "randomblob", "changes", "total_changes", "last_insert_rowid",
          "sqlite_version", "sqlite_source_id", "current_date", "current_time", "current_timestamp"].contains name.toLower
      | _ => false) then throw "non-deterministic functions prohibited in generated columns"
  if let some message := SQLite.Scalar.resolutionError
      (fun qualifier name => qualifier.isNone && (schema.declaredColumn? name).isSome) expression then throw message
  if let some message := SQLite.Scalar.aggregateMisuse expression then throw message
  if let some message := SQLite.Scalar.functionError expression.height expression then throw message
  if expression.any (fun node => match node with
      | .column .. => false
      | _ => SQLite.Scalar.forbidden node) then throw "unsupported generated expression"

def compile (schema : Core.Schema) (columns : Array ColumnDef) (constraints : Array TableConstraintDef) :
    Except String (List Spec) := do
  validateDeclarations columns constraints
  let mut result := []
  for (column, position) in columns.toList.zipIdx do
    if let some expression := column.generated then
      let expression := SQLite.Scalar.prepare (CoreCheck.bind schema expression)
      validateExpression schema expression
      let expression := CoreCollationSyntax.forTable schema.name columns expression
      let dependencies := (List.range schema.catalogColumns.length).filter fun index =>
        expression.any fun node => match node with
          | .column none name => schema.declaredColumn? name == some index
          | _ => false
      result := { position, name := column.name, expression, dependencies } :: result
  return result.reverse

/-- insert.c scans declaration order, postponing a program until its
 generated dependencies have registers. The final postponed declaration names
 a dependency loop if a complete scan makes no progress. -/
def orderFuel (all : List Spec) : Nat → List Spec → Except String (List Spec)
  | 0, _ => .error "generated column dependency limit exceeded"
  | fuel + 1, completed => do
      let mut result := completed
      let mut pending : Option Spec := none
      for current in all do
        if result.any (fun spec => spec.position == current.position) then continue
        if current.dependencies.any (fun position =>
            all.any (fun spec => spec.position == position) &&
            !result.any (fun spec => spec.position == position)) then
          pending := some current
        else result := result ++ [current]
      let some last := pending | return result
      if result.length == completed.length then throw s!"generated column loop on \"{last.name}\""
      orderFuel all fuel result

def order (specs : List Spec) : Except String (List Spec) :=
  orderFuel specs (specs.length + 1) []

def affected (specs : List Spec) (assigned : List Nat) : List Nat :=
  (List.range specs.length).foldl (fun columns _ => specs.foldl (fun columns spec =>
    if spec.dependencies.any columns.contains && !columns.contains spec.position then columns ++ [spec.position]
    else columns) columns) assigned

theorem order_empty : order [] = .ok [] := rfl

theorem affected_empty (assigned : List Nat) : affected [] assigned = assigned := rfl

end SQLeanite.CoreGeneratedSyntax
