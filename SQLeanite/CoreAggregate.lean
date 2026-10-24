import SQLeanite.CoreExpr
import SQLeanite.CoreEngine

/-! Bound scalar arguments and DISTINCT for ordinary aggregate result columns.
Input rows are supplied by the production Core query path. Group keys and
nested aggregate result expressions are separate from this term evaluator. -/
namespace SQLeanite.CoreAggregate

inductive Function where
  | count | sum | average | total | minimum | maximum
  deriving DecidableEq, Repr

def function? (name : String) : Option Function :=
  match aggregateFunctionName name with
  | "count" => some .count
  | "sum" => some .sum
  | "avg" => some .average
  | "total" => some .total
  | "min" => some .minimum
  | "max" => some .maximum
  | _ => none

def recognizes : Expr → Bool
  | .call name arguments star =>
      (function? name).isSome &&
        (!(["min", "max"].contains (aggregateFunctionName name)) || star || arguments.size ≤ 1)
  | _ => false

structure Term where
  function : Function
  argument : Option Expr
  distinct : Bool := false

def term (ctx : CoreExpr.Context) : ResultColumn → Except String Term
  | { expr := .call name arguments star, .. } => do
      let some function := function? name | throw "unsupported aggregate result expression"
      let distinct := isDistinctAggregateName name
      if function == .count && arguments.isEmpty && !distinct then
        return { function, argument := none }
      unless !star && arguments.size == 1 do
        throw "wrong number of arguments to aggregate function"
      let argument := arguments[0]!
      ctx.validate argument
      return { function, argument := some argument, distinct }
  | _ => .error "unsupported aggregate result expression"

def terms (ctx : CoreExpr.Context) (columns : List ResultColumn) : Except String (List Term) :=
  columns.mapM (term ctx)

/-- DISTINCT uses original values and Core's exact BINARY numeric equivalence.
In particular INTEGER and equal REAL keys share one accumulator step. -/
def uniqueValues (values : List Core.Value) : List Core.Value :=
  Core.stableDistinctBy (fun value => Core.distinctRowKey [value]) values

def values (ctx : CoreExpr.Context) (rows : List (List Core.Value))
    (argument : Expr) : Except String (List Core.Value) :=
  rows.mapM fun row => do SQLSurface.value (← ctx.eval row argument)

def result (function : Function) (inputs : List Core.Value) : Except String Core.Value :=
  match function with
  | .count => .integer <$> Core.countInteger (inputs.countP (· != .null))
  | .sum => SQLite.AggregateSum.sum inputs
  | .average => .ok (SQLite.AggregateSum.average inputs)
  | .total => .ok (SQLite.AggregateSum.total inputs)
  | .minimum => .ok (inputs.foldl (Core.chooseExtreme true) .null)
  | .maximum => .ok (inputs.foldl (Core.chooseExtreme false) .null)

def Term.eval (ctx : CoreExpr.Context) (rows : List (List Core.Value))
    (term : Term) : Except String Core.Value := do
  match term.argument with
  | none => .integer <$> Core.countInteger rows.length
  | some expression =>
      let inputs ← values ctx rows expression
      result term.function (if term.distinct then uniqueValues inputs else inputs)

def selectRows (ctx : CoreExpr.Context) (condition : Option Expr) :
    List (List Core.Value) → Except String (List (List Core.Value))
  | [] => .ok []
  | row :: rows => do
      let selected ← ctx.matches row condition
      let tail ← selectRows ctx condition rows
      return if selected then row :: tail else tail

theorem countStar_exact (ctx : CoreExpr.Context) (rows : List (List Core.Value)) :
    Term.eval ctx rows ⟨.count, none, false⟩ =
      (.integer <$> Core.countInteger rows.length) := rfl

theorem selectRows_length_le (ctx : CoreExpr.Context) (condition : Option Expr)
    (rows selected : List (List Core.Value))
    (success : selectRows ctx condition rows = .ok selected) : selected.length ≤ rows.length := by
  induction rows generalizing selected with
  | nil => simp [selectRows] at success; subst selected; simp
  | cons row rows ih =>
      simp only [selectRows] at success
      cases matched : ctx.matches row condition with
      | error message => simp [matched, bind, Except.bind] at success
      | ok keep =>
          cases rest : selectRows ctx condition rows with
          | error message => simp [matched, rest, bind, Except.bind] at success
          | ok tail =>
              have bounded := ih tail rest
              cases keep <;> simp [matched, rest, bind, Except.bind, pure, Except.pure] at success
              all_goals subst selected; simp only [List.length_cons]; omega

end SQLeanite.CoreAggregate
