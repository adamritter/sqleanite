import SQLeanite.CoreCheck

namespace SQLeanite.CoreCollationSyntax

abbrev Spec := String × String

def collect (columns : Array ColumnDef) : List Spec :=
  columns.toList.filterMap fun column =>
    if column.collation.toLower == "binary" then none else some (column.name, column.collation.toLower)

/-- Bind implicit metadata without converting explicit COLLATE nodes into
declarations or descending into another SELECT's lexical scope. -/
def annotateFuel (lookup : Option String → String → Option String) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
      let visit := annotateFuel lookup fuel
      if let some truth := SQLite.Scalar.booleanKeyword? expression then
        let name := SQLite.Scalar.booleanName truth
        match lookup none name with
        | none => expression
        | some collation => SQLite.ExprCollation.declared (.column none name) collation
      else if let some name := SQLite.Scalar.quotedIdentifier? expression then
        match lookup none name with
        | none => expression
        | some collation => SQLite.ExprCollation.declared (.column none name) collation
      else match expression with
      | .column qualifier name =>
          match lookup qualifier name with
          | none => expression
          | some collation => SQLite.ExprCollation.declared expression collation
      | .unary operation argument => .unary operation (visit argument)
      | .binary operation left right => .binary operation (visit left) (visit right)
      | .call "__sqlean_declared_collation" _ false => expression
      | .call name arguments star => .call name (arguments.map visit) star
      | .collate argument name => .collate (visit argument) name
      | .isNull argument negated => .isNull (visit argument) negated
      | .inList argument values negated affinity => .inList (visit argument) (values.map visit) negated affinity
      | .inSubquery argument source negated => .inSubquery (visit argument) source negated
      | .case_ base branches otherwise => .case_ (base.map visit)
          (branches.map fun (condition,result) => (visit condition,visit result)) (otherwise.map visit)
      | _ => expression

def annotate (lookup : Option String → String → Option String) (expression : Expr) : Expr :=
  annotateFuel lookup (expression.height + 1) expression

def forTable (table : String) (columns : Array ColumnDef) (expression : Expr) : Expr :=
  let declarations := collect columns
  if declarations.isEmpty then expression else
    annotate (fun qualifier name => do
      if qualifier.any (fun qualifier => qualifier.toLower != table.toLower) then none else do
        let spec ← declarations.find? (fun spec => spec.1.toLower == name.toLower)
        return spec.2) expression

def validateIndexes (schema : Core.Schema) (columns : Array ColumnDef)
    (constraints : Array TableConstraintDef) : Except String Unit := do
  for (column,position) in columns.toList.zipIdx do
    if column.collation.toLower == "binary" then continue
    let indexed := column.unique || (schema.hasHiddenRowid && schema.declaredPrimaryKey? == some position) ||
      constraints.any (fun constraint => constraint.check.isNone && constraint.references.isNone &&
        !constraint.primaryKey && constraint.columns.any (fun name => name.toLower == column.name.toLower))
    if indexed then throw "unsupported general verified-MVP SQL: declared collation index"

theorem forTable_binary (table : String) (columns : Array ColumnDef) (expression : Expr)
    (binary : collect columns = []) : forTable table columns expression = expression := by
  simp [forTable, binary]

end SQLeanite.CoreCollationSyntax
