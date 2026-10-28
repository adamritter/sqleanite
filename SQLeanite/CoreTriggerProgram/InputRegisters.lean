import SQLeanite.CoreTriggerProgram.UpdateBefore

namespace SQLeanite.CoreTriggerProgram

def inputCell (read : ScopedRead) (state : Core.State) (expression : Expr) : Except String CoreReturning.Cell := do
  let selected ← read false state [] { columns := #[{ expr := expression }] }
  let some scalar := selected.firstTyped | throw "INSERT input lost its scalar register"
  CoreReturning.Cell.fromScalar scalar

/-- A scalar subquery's Once register keeps its own affinity and subtype. The
surrounding expression, including connection counters, is still executable. -/
def inputQueryRegister (read : ScopedRead) (state : Core.State) (expression : Expr) : Except String Expr := do
  let selected ← read false state [] { columns := #[{ expr := expression }] }
  let some scalar := selected.firstTyped | throw "INSERT subquery lost its scalar register"
  let cell ← CoreReturning.Cell.fromScalar scalar
  let value ← registerExpression cell
  let some affinity := selected.affinity | return value
  return .call "__sqlean_bound_value" #[value,.literal (.text (CoreCreateTableAs.declaredType affinity))] false

def inputTest (read : ScopedRead) (state : Core.State) (expression : Expr) : Except String Bool := do
  let selected ← read false state [] {
    columns := #[{ expr := .literal (.integer 1) }]
    where_ := some expression }
  return !selected.result.rows.isEmpty

/-- Boolean branches use the same true/false short-circuit rules as the
scalar evaluator's test context, rather than projecting both AND/OR operands. -/
def cacheInputCondition (visit : Expr → Except String Expr) (read : ScopedRead) (state : Core.State) :
    Nat → Bool → Expr → Except String Expr
  | 0,_,_ => throw "INSERT condition nesting limit exceeded"
  | fuel+1,wanted,expression => do
      match SQLite.Scalar.prepare expression with
      | .unary .not argument => return .unary .not (← cacheInputCondition visit read state fuel (!wanted) argument)
      | .binary op left right =>
          if op != .and && op != .or then return ← visit expression
          let left ← cacheInputCondition visit read state fuel wanted left
          let tested := if wanted then left else .unary .not left
          let selected ← inputTest read state tested
          let takeRight := if (op == .and) == wanted then selected else !selected
          let right ← if takeRight then cacheInputCondition visit read state fuel wanted right else pure right
          return .binary op left right
      | _ => visit expression

/-- Cache only subqueries actually reached by the first rowid evaluation.
Unselected CASE/conditional/coalesce branches remain executable for a later
pass that can observe different connection counters. -/
def cacheInputQueries (read : ScopedRead) (state : Core.State) : Nat → Expr → Except String Expr
  | 0,_ => throw "INSERT input nesting limit exceeded"
  | fuel+1,original => do
      let expression := SQLite.Scalar.prepare original
      if (CoreScalarQuery.captures expression.height expression).isEmpty then return expression
      let visit := cacheInputQueries read state fuel
      match expression with
      | .scalarSubquery _ | .existsSubquery _ => inputQueryRegister read state expression
      | .unary op argument => return .unary op (← visit argument)
      | .isNull argument negated => return .isNull (← visit argument) negated
      | .collate argument name => return .collate (← visit argument) name
      | .binary op left right => return .binary op (← visit left) (← visit right)
      | .inSubquery argument sql negated => return .inSubquery (← visit argument) sql negated
      | .inList argument values negated affinity =>
          if values.isEmpty then return expression
          let argument ← visit argument
          let mut output := #[]
          let mut taken := false
          for value in values do
            let value ← if taken then pure value else visit value
            if !taken then taken := (← inputTest read state (.inList argument #[value] false affinity))
            output := output.push value
          return .inList argument output negated affinity
      | .case_ base branches other =>
          -- expr.c duplicates CASE's base tree for each code-generation pass.
          -- Its scalar subqueries consequently have separate Once registers.
          let mut output := #[]
          let mut taken := false
          for (condition,value) in branches do
            if taken then
              output := output.push (condition,value)
            else
              let condition ← cacheInputCondition visit read state condition.height true condition
              let test := match base with | none => condition | some base => .binary .eq base condition
              let selected ← inputTest read state test
              let value ← if selected then visit value else pure value
              taken := selected
              output := output.push (condition,value)
          let other ← if taken then pure other else other.mapM visit
          return .case_ base output other
      | .call name arguments star =>
          let lower := SQLite.Scalar.scalarFunctionName name
          if !star && (lower == "coalesce" || lower == "ifnull") then
            let mut output := #[]
            let mut taken := false
            for argument in arguments do
              let argument ← if taken then pure argument else visit argument
              if !taken then taken := (← inputCell read state argument).value != .null
              output := output.push argument
            return .call name output star
          if !star && (lower == "iif" || lower == "if") then
            let mut output := #[]
            let mut taken := false
            for index in List.range arguments.size do
              let argument := arguments[index]!
              if index % 2 == 0 && index+1 < arguments.size then
                let argument ← if taken then pure argument else cacheInputCondition visit read state argument.height true argument
                let selected ← if taken then pure false else inputTest read state argument
                output := output.push argument
                let value := arguments[index+1]!
                output := output.push (← if selected then visit value else pure value)
                taken := taken || selected
              else if index % 2 == 0 then
                output := output.push (← if taken then pure argument else visit argument)
            return .call name output star
          return .call name (← arguments.mapM visit) star
      | _ => return expression

theorem cacheInputQueries_without_queries (read : ScopedRead) (state : Core.State) (fuel : Nat) (expression : Expr)
    (empty : (CoreScalarQuery.captures (SQLite.Scalar.prepare expression).height (SQLite.Scalar.prepare expression)).isEmpty = true) :
    cacheInputQueries read state (fuel+1) expression = .ok (SQLite.Scalar.prepare expression) := by
  simp [cacheInputQueries, empty]
  rfl

end SQLeanite.CoreTriggerProgram
