import SQLeanite.CoreAggregate

/-! Ungrouped aggregate ORDER BY validates every expression and registers its
aggregate terms. With one output group, SQLite finalizes those accumulators
but never evaluates the outer scalar sort-key expressions. -/
namespace SQLeanite.CoreAggregateOrder

/-- Bare ORDER BY columns bind against the source but need no retained value
for a singleton aggregate result. Aggregate arguments keep their original AST. -/
def eraseBareFuel : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
      if CoreAggregate.recognizes expression then expression
      else
        let erase := eraseBareFuel fuel
        match expression with
        | .column .. => .literal .null
        | .unary op argument => .unary op (erase argument)
        | .binary op left right => .binary op (erase left) (erase right)
        | .call name arguments star => .call name (arguments.map erase) star
        | .collate argument name => .collate (erase argument) name
        | .isNull argument negated => .isNull (erase argument) negated
        | .inList argument values negated affinity =>
            .inList (erase argument) (values.map erase) negated affinity
        | .case_ base branches otherwise => .case_ (base.map erase)
            (branches.map fun (condition, result) => (erase condition, erase result)) (otherwise.map erase)
        | _ => expression

def orderTerms (ctx : CoreExpr.Context) (columns : List ResultColumn)
    (terms : List OrderTerm) : Except String (List Expr) := do
  let resolved ← CoreOrder.resolve ctx columns terms
  resolved.mapM fun term => do
    let _ ← CoreOrder.specification term
    unless ctx.namesBound term.expr do throw "unbound aggregate ORDER BY expression"
    let bound := SQLite.Scalar.prepare (ctx.bindNames term.expr)
    return eraseBareFuel bound.height bound

def extend (ctx : CoreExpr.Context) (prepared : CoreAggregate.PreparedResults)
    (expressions : List Expr) : Except String CoreAggregate.PreparedResults :=
  (fun result => { prepared with terms := result.2 }) <$>
    (expressions.mapM (fun expression => CoreAggregate.prepareResultFuel ctx expression.height expression)).run prepared.terms

def prepare (ctx : CoreExpr.Context) (columns : List ResultColumn) (ordering : List OrderTerm) :
    Except String CoreAggregate.PreparedResults := do
  let expressions ← orderTerms ctx columns ordering
  let prepared ← CoreAggregate.prepareResults ctx columns
  extend ctx prepared expressions

theorem extend_preserves_expressions {ctx : CoreExpr.Context}
    {before after : CoreAggregate.PreparedResults} {expressions : List Expr}
    (success : extend ctx before expressions = .ok after) : after.expressions = before.expressions := by
  unfold extend at success
  cases result : (expressions.mapM (fun expression =>
      CoreAggregate.prepareResultFuel ctx expression.height expression)).run before.terms with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

theorem eraseBareFuel_aggregate (fuel : Nat) (expression : Expr)
    (aggregate : CoreAggregate.recognizes expression = true) :
    eraseBareFuel (fuel + 1) expression = expression := by
  simp [eraseBareFuel, aggregate]

end SQLeanite.CoreAggregateOrder
