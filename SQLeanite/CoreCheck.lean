import SQLeanite.CoreData

/-! CHECK predicates use SQL numeric truth: only false rejects a row; NULL
passes. Keep evaluator errors distinct from constraint failures so OR IGNORE
cannot suppress arithmetic or name-resolution errors. -/
namespace SQLeanite.CoreCheck

def collect (columns : Array ColumnDef) (constraints : Array TableConstraintDef) : List CheckDef :=
  columns.toList.flatMap (fun column => column.earlierChecks.toList ++ column.check.toList) ++
    constraints.toList.flatMap (fun constraint => constraint.check.toList)

def column? (schema : Core.Schema) (qualifier : Option String) (name : String) : Option Nat :=
  if qualifier.any (fun q => q.toLower != schema.name.toLower) then none else schema.column? name

def bind (schema : Core.Schema) (expression : Expr) : Expr :=
  SQLite.Scalar.bindNames (fun name => (column? schema none name).isSome) expression

def affinity (schema : Core.Schema) (expression : Expr) : Option SQLite.Affinity :=
  match SQLite.ExprCollation.strip (bind schema expression) with
  | .column qualifier name => do
      let index ← column? schema qualifier name
      return (← schema.columns[index]?).affinity
  | _ => SQLite.Scalar.expressionAffinity expression

def validate (schema : Core.Schema) (checks : List CheckDef) : Except String Unit := do
  for check in checks do
    let expression := SQLite.Scalar.prepare (bind schema check.expression)
    if expression.any (fun e => match e with
        | .scalarSubquery .. | .existsSubquery .. | .inSubquery .. => true
        | _ => false) then throw "subqueries prohibited in CHECK constraints"
    if let some message := SQLite.Scalar.resolutionError (fun q n => (column? schema q n).isSome) expression then
      throw message
    if let some message := SQLite.Scalar.aggregateMisuse expression then throw message
    if expression.any (fun e => match e with
        | .column qualifier name => (column? schema qualifier name).isNone
        | _ => SQLite.Scalar.forbidden e) then throw "unsupported CHECK expression"

def value : Core.Value → Value
  | .null => .null
  | .integer number => .integer number.value
  | .realBits bits => .real (Float.ofBits (UInt64.ofNat bits.val))
  | .blob bytes => .blob bytes.bytes.toArray
  | .text bytes => match String.fromUTF8? (ByteArray.mk bytes.bytes.toArray) with
      | some text => .text text
      | none => .textBytes bytes.bytes.toArray

/-- SQLite only runs UPDATE CHECK programs that reference a SET target. This
uses the prepared, bound expression, including quoted names and rowid aliases; a column
assigned its own value still counts as assigned. -/
def affected (schema : Core.Schema) (assigned : List Nat) (check : CheckDef) : Bool :=
  (SQLite.Scalar.prepare (bind schema check.expression)).any fun expression => match expression with
    | .column qualifier name => (column? schema qualifier name).any assigned.contains
    | _ => false

def forUpdate (schema : Core.Schema) (assigned : Option (List Nat)) (checks : List CheckDef) : List CheckDef :=
  match assigned with
  | none => checks
  | some columns => checks.filter (affected schema columns)

theorem forUpdate_insert (schema : Core.Schema) (checks : List CheckDef) :
    forUpdate schema none checks = checks := rfl

theorem forUpdate_member {schema : Core.Schema} {assigned : List Nat}
    {checks : List CheckDef} {check : CheckDef} :
    check ∈ forUpdate schema (some assigned) checks ↔
      check ∈ checks ∧ affected schema assigned check = true := by
  simp [forUpdate]

def failure (schema : Core.Schema) (checks : List CheckDef) (row : Core.Row) :
    Except String (Option String) := do
  for check in checks do
    let expression := SQLite.Scalar.prepare (bind schema check.expression)
    let lookup := fun qualifier name => do
      let some position := column? schema qualifier name | throw s!"no such column: {name}"
      let some stored := row.values[position]? | throw "missing CHECK row value"
      pure (value stored)
    let result ← SQLite.Scalar.evalWith lookup (affinity schema) expression
    unless (SQLite.Numeric.truth result).satisfiesCheck do
      return some s!"CHECK constraint failed: {check.diagnostic}"
  return none

theorem failure_empty (schema : Core.Schema) (row : Core.Row) :
    failure schema [] row = .ok none := rfl

end SQLeanite.CoreCheck
