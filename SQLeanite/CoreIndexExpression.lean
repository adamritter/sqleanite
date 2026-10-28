import SQLeanite.CoreExpr
import SQLeanite.SQLSurface

/-! Schema scalar programs use ordinary lazy evaluation with an explicit
host-dependent date/time rejection. Physical keys receive no column affinity. -/
namespace SQLeanite.CoreIndexExpression

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
