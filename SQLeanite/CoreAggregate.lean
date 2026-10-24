import SQLeanite.CoreExpr
import SQLeanite.CoreEngine

/-! Bound scalar arguments and DISTINCT for ordinary aggregate result columns.
Input rows are supplied by the production Core query path. Aggregate terms
feed a separately bound scalar result template; group keys remain separate. -/
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
  collation : SQLite.Collation.Kind := .binary

def term (ctx : CoreExpr.Context) : ResultColumn → Except String Term
  | { expr := .call name arguments star, .. } => do
      let some function := function? name | throw "unsupported aggregate result expression"
      let distinct := isDistinctAggregateName name
      if function == .count && arguments.isEmpty && !distinct then
        return { function, argument := none }
      unless !star && arguments.size == 1 do
        throw "wrong number of arguments to aggregate function"
      let argument := ctx.bindNames arguments[0]!
      ctx.validate argument
      let collation ← if distinct || function == .minimum || function == .maximum then
          SQLite.ExprCollation.require (SQLite.ExprCollation.kind? argument)
        else pure SQLite.Collation.Kind.binary
      return { function, argument := some argument, distinct, collation }
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

/-- Preserve original representatives while applying the aggregate argument's
collation only to TEXT. Equal INTEGER/REAL inputs still share a step. -/
def uniqueValuesWith (kind : SQLite.Collation.Kind) (values : List Core.Value) : List Core.Value :=
  values.foldl (fun kept value =>
    if kept.any (fun old => SQLite.Collation.compareValue kind old value == .eq) then kept
    else kept ++ [value]) []

def resultWith (kind : SQLite.Collation.Kind) (function : Function)
    (inputs : List Core.Value) : Except String Core.Value :=
  if function == .minimum || function == .maximum then
    .ok (inputs.foldl (fun best value =>
      if value == .null then best
      else if best == .null then value
      else
        let order := SQLite.Collation.compareValue kind best value
        if (if function == .minimum then order == .gt else order == .lt) then value else best) .null)
  else result function inputs

def Term.eval (ctx : CoreExpr.Context) (rows : List (List Core.Value))
    (term : Term) : Except String Core.Value := do
  match term.argument with
  | none => .integer <$> Core.countInteger rows.length
  | some expression =>
      let inputs ← values ctx rows expression
      resultWith term.collation term.function
        (if term.distinct then uniqueValuesWith term.collation inputs else inputs)

/-- Aggregate recognition includes aggregates nested inside scalar result
operators. An aggregate's own arguments are still checked as scalar inputs. -/
def containsAggregate (expression : Expr) : Bool := expression.any recognizes

structure PreparedResults where
  expressions : List Expr
  terms : Array Term

abbrev PrepareM := StateT (Array Term) (Except String)

/-- Lower aggregate calls to private result slots. Source column references
outside aggregate arguments remain rejected by this aggregate-only result path.
The private slot syntax can only be produced here: ordinary user calls and
columns are validated before any slot is installed. -/
def prepareResultFuel (ctx : CoreExpr.Context) : Nat → Expr → PrepareM Expr
  | 0, _ => throw "aggregate expression depth exhausted"
  | fuel + 1, expression => do
      if recognizes expression then
        let bound ← term ctx { expr := expression }
        let terms ← get
        set (terms.push bound)
        let slot := Expr.column (some "__aggregate_result") (toString terms.size)
        return match SQLite.ExprCollation.name expression with
          | none => slot
          | some name => .collate slot name
      if SQLite.Scalar.forbidden expression then
        throw "unsupported aggregate result operator"
      let prepare := prepareResultFuel ctx fuel
      match expression with
      | .literal _ => return expression
      | .collate arg name => return .collate (← prepare arg) name
      | .unary op arg => return .unary op (← prepare arg)
      | .binary op left right => return .binary op (← prepare left) (← prepare right)
      | .call name args star => return .call name (← args.mapM prepare) star
      | .isNull arg negated => return .isNull (← prepare arg) negated
      | .inList arg values negated affinity =>
          return .inList (← prepare arg) (← values.mapM prepare) negated affinity
      | .case_ base branches otherwise =>
          return .case_ (← base.mapM prepare)
            (← branches.mapM fun (condition, result) => do return (← prepare condition, ← prepare result))
            (← otherwise.mapM prepare)
      | _ => throw "unsupported bare column or subquery in aggregate result"

def prepareResults (ctx : CoreExpr.Context) (columns : List ResultColumn) :
    Except String PreparedResults := do
  let (expressions, terms) ←
    (columns.mapM fun column =>
      let expression := ctx.bindNames column.expr
      prepareResultFuel ctx expression.height expression).run #[]
  return { expressions, terms }

/-- Accumulators are finalized before OFFSET. Scalar result expressions are
kept separate so a skipped output row does not evaluate its scalar operations. -/
def PreparedResults.accumulate (prepared : PreparedResults) (ctx : CoreExpr.Context)
    (rows : List (List Core.Value)) : Except String (Array Core.Value) :=
  Subtype.val <$> prepared.terms.mapM' (Term.eval ctx rows)

def resultSlot (values : Array Core.Value) (qualifier : Option String) (name : String) :
    Except String Core.Value := do
  unless qualifier == some "__aggregate_result" do throw "unbound aggregate result column"
  let some index := name.toNat? | throw "invalid aggregate result slot"
  let some value := values[index]? | throw "aggregate result slot is outside its accumulator array"
  return value

def PreparedResults.finish (prepared : PreparedResults) (values : Array Core.Value) :
    Except String (List Core.Value) :=
  prepared.expressions.mapM fun expression =>
    match expression with
    | .column qualifier name => resultSlot values qualifier name
    | _ => do
        let result ← SQLite.Scalar.evalWith
          (fun qualifier name => do CoreExpr.value (← resultSlot values qualifier name))
          SQLite.Scalar.expressionAffinity expression
        SQLSurface.value result

theorem PreparedResults.accumulate_length (prepared : PreparedResults) (ctx : CoreExpr.Context)
    (rows : List (List Core.Value)) (values : Array Core.Value)
    (success : prepared.accumulate ctx rows = .ok values) :
    values.size = prepared.terms.size := by
  unfold PreparedResults.accumulate at success
  cases evaluated : prepared.terms.mapM' (Term.eval ctx rows) with
  | error message => simp [evaluated, Functor.map, Except.map] at success
  | ok checked =>
      simp [evaluated, Functor.map, Except.map] at success
      cases success
      exact checked.property

def selectRows (ctx : CoreExpr.Context) (condition : Option Expr) :
    List (List Core.Value) → Except String (List (List Core.Value))
  | [] => .ok []
  | row :: rows => do
      let selected ← ctx.matches row condition
      let tail ← selectRows ctx condition rows
      return if selected then row :: tail else tail

theorem countStar_exact (ctx : CoreExpr.Context) (rows : List (List Core.Value)) :
    Term.eval ctx rows ⟨.count, none, false, .binary⟩ =
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
