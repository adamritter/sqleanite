import SQLeanite.CoreExpr
import SQLeanite.CoreCollationSyntax
import SQLeanite.SQLSurface

/-! Schema scalar programs use ordinary lazy evaluation with an explicit
host-dependent date/time rejection. Physical keys receive no column affinity. -/
namespace SQLeanite.CoreIndexExpression

def requireCollation (name : Option String) : Except String Unit := do
  if let some name := name then
    unless (SQLite.Collation.named? name).isSome do throw s!"no such collation sequence: {name}"

def comparisonCollation (left right : Expr) : Option String :=
  (SQLite.ExprCollation.name left).orElse fun _ =>
    (SQLite.ExprCollation.name right).orElse fun _ =>
      (SQLite.ExprCollation.effectiveName left).orElse fun _ => SQLite.ExprCollation.effectiveName right

/-- Compilation resolves only collations consumed by an operation. A COLLATE
inside lower()/concatenation is metadata until a comparison actually uses it. -/
def validateCollationsFuel : Nat → Expr → Except String Unit
  | 0, _ => .error "index collation expression depth exhausted"
  | fuel + 1, expression => do
      let visit := validateCollationsFuel fuel
      match expression with
      | .collate argument _ | .unary _ argument | .isNull argument _ | .inSubquery argument _ _ => visit argument
      | .binary operation left right =>
          if [.eq,.ne,.lt,.le,.gt,.ge,.is,.isNot].contains operation then
            requireCollation (comparisonCollation left right)
          visit left *> visit right
      | .call name arguments _ =>
          if ["min","max","nullif"].contains name.toLower then
            requireCollation (arguments.toList.findSome? SQLite.ExprCollation.effectiveName)
          if name == "__sqlean_between" then
            if let [argument,lower,upper] := arguments.toList then
              requireCollation (comparisonCollation argument lower)
              requireCollation (comparisonCollation argument upper)
          arguments.forM visit
      | .inList argument values _ _ =>
          requireCollation (SQLite.ExprCollation.effectiveName argument)
          visit argument *> values.forM visit
      | .case_ base branches other =>
          if let some base := base then
            branches.forM (fun (condition,_) => requireCollation (comparisonCollation base condition))
          discard <| base.mapM visit
          branches.forM (fun (condition,result) => visit condition *> visit result)
          discard <| other.mapM visit
      | _ => pure ()

def validateCollations (expression : Expr) : Except String Unit :=
  validateCollationsFuel expression.height expression

def uniqueConflict (collation : SQLite.Collation.Kind) : Core.Value → Core.Value → Bool
  | .null, _ | _, .null => false
  | left, right => SQLite.Collation.compareValue collation left right == .eq

@[simp] theorem uniqueConflict_null (collation : SQLite.Collation.Kind) (value : Core.Value) :
    uniqueConflict collation .null value = false := rfl

def adjacentUnique (index : Core.Index) (collation : SQLite.Collation.Kind) : List Core.Row → Bool
  | left :: right :: tail =>
      !(index.unique && uniqueConflict collation ((left.values[index.column]?).getD .null) ((right.values[index.column]?).getD .null)) &&
        adjacentUnique index collation (right :: tail)
  | _ => true

def validateDeterminism (expression : Expr) (partialPredicate : Bool) : Except String Unit := do
  if expression.any (fun node => match node with
      | .call name _ _ => ["random", "randomblob", "changes", "total_changes", "last_insert_rowid",
          "sqlite_version", "sqlite_source_id", "current_date", "current_time", "current_timestamp"].contains name.toLower
      | _ => false) then
    throw (if partialPredicate then "non-deterministic functions prohibited in partial index WHERE clauses"
      else "non-deterministic functions prohibited in index expressions")

def builtin (name : String) (arguments : Array SQLite.ScalarValue) : Except String SQLite.ScalarValue :=
  match SQLite.DateTime.evaluate? name (arguments.toList.map (·.value)) with
  | some result => (SQLite.Scalar.plainScalar <$> result).mapError fun message =>
      if message == "unsupported verified SQL: date/time host clock or timezone service" then
        s!"non-deterministic use of {name}() in an index" else message
  | none => SQLite.Scalar.builtinTyped name arguments

def eval (context : CoreExpr.Context) (values : List Core.Value) (expression : Expr) :
    Except String Value :=
  (·.value) <$> SQLite.Scalar.evalTypedWithBuiltin (context.lookupScalar values)
    context.affinity builtin (context.bindNames expression)

def acceptsTerms (context : CoreExpr.Context) (values : List Core.Value) :
    List Expr → Except String Bool
  | [] => .ok true
  | expression :: rest => do
      let evaluate := SQLite.Scalar.evalTypedWithBuiltin (context.lookupScalar values)
        context.affinity builtin
      if ← SQLite.Scalar.testEvaluatedTypedFuel evaluate context.affinity true expression.height true expression then
        acceptsTerms context values rest
      else return false

def acceptsPredicate (context : CoreExpr.Context) (values : List Core.Value) (expression : Expr) :
    Except String Bool :=
  acceptsTerms context values (SQLite.Scalar.conditionTerms (SQLite.Scalar.prepare (context.bindNames expression)))

end SQLeanite.CoreIndexExpression
