import SQLeanite.CoreAggregateOrder
import SQLeanite.CoreCompoundTail

/-! Ungrouped HAVING uses finalized aggregate slots and a retained source row.
Only validated source references can become private source slots. -/
namespace SQLeanite.CoreAggregateHaving

structure Prepared where
  results : CoreAggregate.PreparedResults
  having : Option Expr

def resolve (ctx : CoreExpr.Context) (columns : List ResultColumn) (expression : Expr) : Expr :=
  CoreOrder.resolveNamesFuel ctx columns expression.height expression

def prepare (ctx : CoreExpr.Context) (columns : List ResultColumn)
    (ordering : List OrderTerm) (having : Option Expr) : Except String Prepared := do
  let columns ← CoreOrder.expandResults ctx columns
  let orderTerms ← CoreAggregateOrder.orderTerms ctx columns ordering
  let having := having.map (resolve ctx columns)
  for expression in columns.map (·.expr) ++ having.toList do
    if let some message := SQLite.Scalar.nameError (fun qualifier name => (ctx.column? qualifier name).isSome) expression then
      throw message
  unless columns.all (fun c => ctx.namesBound c.expr) && having.all ctx.namesBound do
    throw "unbound aggregate expression"
  let prepareOne (expression : Expr) : CoreAggregate.PrepareM Expr :=
    let expression := SQLite.Scalar.prepare (ctx.bindNames expression)
    CoreAggregate.prepareTemplateFuel ctx true expression.height expression
  let ((expressions, having), terms) ← (do
    let expressions ← columns.mapM (fun (c : ResultColumn) => prepareOne c.expr)
    discard <| orderTerms.mapM prepareOne
    let having ← having.mapM prepareOne
    pure (expressions, having) : CoreAggregate.PrepareM (List Expr × Option Expr)).run #[]
  return { results := { expressions, terms }, having }

def sameArgument (ctx : CoreExpr.Context) (left right : Option Expr) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
      let left := CoreCompoundTail.normalizeFuel (some ctx) left.height left
      let right := CoreCompoundTail.normalizeFuel (some ctx) right.height right
      CoreCompoundTail.sameFuel (max left.height right.height) left right
  | _, _ => false

/-- SQLite shares repeated aggregate calls before choosing the accumulator
that controls bare columns. Explicit argument collations remain part of identity. -/
def extremeTerms (ctx : CoreExpr.Context) (terms : Array CoreAggregate.Term) : Array CoreAggregate.Term :=
  terms.foldl (fun kept term =>
    if term.function != .minimum && term.function != .maximum then kept
    else if kept.any (fun old => old.function == term.function && old.distinct == term.distinct &&
        sameArgument ctx old.argument term.argument && sameArgument ctx old.filter term.filter &&
        CoreAggregateOrdering.sameOrdering ctx old.ordering term.ordering) then kept
    else kept.push term) #[]

structure ExtremeState where
  best : Core.Value := .null
  seen : List Core.Value := []

/-- A DISTINCT duplicate skips the whole step, including its update flag.
A performed MIN/MAX step overwrites the shared flag; all-NULL steps load rows. -/
def extremeStep (ctx : CoreExpr.Context) (term : CoreAggregate.Term) (state : ExtremeState)
    (row : List Core.Value) : Except String (ExtremeState × Option Bool) := do
  unless ← term.matchesFilter ctx row do return (state, none)
  let some expression := term.argument | throw "MIN/MAX has no argument"
  let value ← SQLSurface.value (← ctx.eval row expression)
  if term.distinct && state.seen.any (fun old => SQLite.Collation.compareValue term.collation old value == .eq) then
    return (state, none)
  let seen := if term.distinct then value :: state.seen else state.seen
  let order := SQLite.Collation.compareValue term.collation state.best value
  let improves := state.best == .null || (value != .null &&
    (if term.function == .minimum then order == .gt else order == .lt))
  return ({ best := if improves then value else state.best, seen }, some (!improves))

def retain (previous current : List Core.Value) (skip : Bool) : List Core.Value :=
  if skip then previous else current

theorem retain_member (previous current : List Core.Value) (skip : Bool) :
    retain previous current skip = previous ∨ retain previous current skip = current := by
  cases skip <;> simp [retain]

/-- With no extrema, SQLite retains the first source row. With extrema, the
last performed unique MIN/MAX step controls whether this row replaces it. -/
def representative (ctx : CoreExpr.Context) (terms : Array CoreAggregate.Term)
    (rows : List (List Core.Value)) (grouped : Bool := false) : Except String (List Core.Value) := do
  let empty := List.replicate ctx.schema.columns.length (.null : Core.Value)
  let extremes := extremeTerms ctx terms
  if extremes.isEmpty then return rows.headD empty
  let mut states : Array ExtremeState := extremes.map (fun _ => {})
  let resetFiltered := grouped || extremes.all (fun term => term.filter.isSome)
  let mut visited := false
  let mut skip := false
  let mut chosen := empty
  for row in rows do
    let mut next := #[]
    for (term, state) in extremes.zip states do
      -- Grouped scans always have regAcc. Ungrouped scans only allocate it
      -- when no unfiltered MIN/MAX can initialize the retained source row.
      if resetFiltered && term.filter.isSome then skip := visited
      let (state, flag) ← extremeStep ctx term state row
      next := next.push state
      if let some flag := flag then skip := flag
    states := next
    chosen := retain chosen row skip
    visited := true
  return chosen

def lookup (values : Array CoreAggregate.Result) (row : List Core.Value)
    (qualifier : Option String) (name : String) : Except String SQLite.ScalarValue := do
  if qualifier == some "__aggregate_result" then
    (← CoreAggregate.resultSlot values qualifier name).scalar
  else
    unless qualifier == some "__aggregate_source" do throw "unbound aggregate template column"
    let some index := name.toNat? | throw "invalid aggregate source slot"
    let some value := row[index]? | throw "aggregate source slot is outside the retained row"
    SQLite.Scalar.plainScalar <$> CoreExpr.value value

def affinity (ctx : CoreExpr.Context) (expression : Expr) : Option SQLite.Affinity :=
  match SQLite.ExprCollation.strip expression with
  | .column (some "__aggregate_source") name => do
      let index ← name.toNat?
      return (← ctx.schema.columns[index]?).affinity
  | _ => SQLite.Scalar.expressionAffinity expression

def Prepared.matches (prepared : Prepared) (ctx : CoreExpr.Context)
    (values : Array CoreAggregate.Result) (row : List Core.Value) : Except String Bool :=
  match prepared.having with
  | none => .ok true
  | some expression => SQLite.Scalar.testBranchTypedWith (lookup values row) (affinity ctx)
      expression.height true expression

def Prepared.finish (prepared : Prepared) (ctx : CoreExpr.Context)
    (values : Array CoreAggregate.Result) (row : List Core.Value) : Except String (List Core.Value) :=
  prepared.results.expressions.mapM fun expression => do
    SQLSurface.value (← SQLite.Scalar.evalTypedWith (lookup values row) (affinity ctx) expression).value

theorem Prepared.matches_none (results : CoreAggregate.PreparedResults) (ctx : CoreExpr.Context)
    (values : Array CoreAggregate.Result) (row : List Core.Value) :
    (Prepared.mk results none).matches ctx values row = .ok true := rfl

end SQLeanite.CoreAggregateHaving
