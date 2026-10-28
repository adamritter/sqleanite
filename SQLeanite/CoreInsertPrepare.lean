import SQLeanite.CoreExpr

namespace SQLeanite.CoreInsertPrepare

/-- Bind constant VALUES expressions without executing them. Function lookup
precedes argument lookup, and no target-table columns are visible here. -/
def bindingFuel : Nat → Expr → Except String Unit
  | 0, _ => .error "INSERT expression depth exhausted"
  | fuel+1, expression => do
      if let some name := SQLite.Scalar.quotedIdentifier? expression then
        throw ("no such column: \"" ++ name ++ "\" - should this be a string literal in single-quotes?")
      let visit := bindingFuel fuel
      match expression with
      | .literal .. => pure ()
      | .column qualifier name => throw ("no such column: " ++ (qualifier.map (· ++ ".") |>.getD "") ++ name)
      | .call "__sqlean_bound_value" #[argument, .literal (.text _) _, .literal (.integer _) _] false => visit argument
      | .call "__sqlean_bound_value" #[argument, .literal (.text _) _] false |
          .call "__sqlean_declared_collation" #[argument, .literal (.text _) _] false => visit argument
      | .call "__sqlean_encoded" #[.literal (.text _) _,.literal (.integer _) _,argument] false => visit argument
      | .call name arguments star =>
          let function := SQLite.Scalar.scalarFunctionName name
          unless function.startsWith "cast_" || function == "__sqlean_between" || function == "__sqlean_trigger_abort" do
            let overloads := SQLite.FunctionSignatures.entries.filter (fun entry => entry.1 == function)
            if overloads.isEmpty then throw s!"no such function: {name}"
            unless overloads.any (fun entry => SQLite.FunctionSignatures.matchesArity entry.2.2 arguments.size) do
              throw s!"wrong number of arguments to function {name}()"
            if let some message := SQLite.Scalar.aggregateMisuseFuel 1 expression then throw message
          for argument in arguments do visit argument
      | .unary _ argument | .isNull argument _ | .collate argument _ => visit argument
      | .binary _ left right => visit left; visit right
      | .inList argument values _ _ =>
          visit argument
          for value in values do visit value
      | .case_ base branches otherwise =>
          discard <| base.mapM visit
          for (condition, result) in branches do visit condition; visit result
          discard <| otherwise.mapM visit
      | _ => throw "unsupported INSERT source expression"

def binding (expression : Expr) : Except String Unit :=
  let expression := SQLite.Scalar.prepare (SQLite.Scalar.bindNames (fun _ => false) expression)
  bindingFuel expression.height expression

/-- Source row widths and target names are preparation errors. Check them
before RETURNING binding while leaving runtime expressions unevaluated. -/
def check (schema : Core.Schema) (columns : Option (Array String))
    (rows : Array (Array Expr)) (implicitWidth : Option Nat := none) : Except String Unit := do
  let first := rows[0]?.getD #[]
  unless rows.all (fun row => row.size == first.size) do
    throw "all VALUES must have the same number of terms"
  if let some names := columns then
    for name in names do
      if (schema.column? name).isNone then throw s!"table {schema.name} has no column named {name}"
  for row in rows do
    for expression in row do binding expression
  if let some expected := implicitWidth then
    unless first.isEmpty || first.size == expected do
      throw s!"table {schema.name} has {expected} columns but {first.size} values were supplied"
    return ()
  match columns with
  | none =>
      unless first.isEmpty || first.size == schema.visibleColumns.length do
        throw s!"table {schema.name} has {schema.visibleColumns.length} columns but {first.size} values were supplied"
  | some names =>
      unless first.size == names.size do throw s!"{first.size} values for {names.size} columns"

theorem bindingFuel_literal (fuel : Nat) (value : Value) (source : Option String) :
    bindingFuel (fuel+1) (.literal value source) = .ok () := rfl

theorem check_default (schema : Core.Schema) :
    check schema none #[#[]] = .ok () := by
  simp [check, pure, Except.pure] <;> rfl

end SQLeanite.CoreInsertPrepare
