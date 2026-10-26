import SQLeanite.CoreCompoundTail
import SQLeanite.SQLite.StaticCondition

/-! The ordinary aggregate ORDER BY sorter. DISTINCT normally admits the
first input before sorting. SQLite's single identical argument/order-key
optimization instead uses a unique sorting index, replacing equal keys with
the last original representative. Keys evaluate even for duplicate inputs. -/
namespace SQLeanite.CoreAggregateOrdering

/-- SQLite resolves ignored MIN/MAX ordering expressions but emits no value
or collation operations for them. Function names/arity still bind, including
builtins not otherwise executable by this Core subset. -/
abbrev ignoredForbidden := SQLite.StaticCondition.resolutionForbidden

def validateIgnored (ctx : CoreExpr.Context) (expression : Expr) : Except String Unit := do
  let expression := SQLite.Scalar.prepare (ctx.bindNames expression)
  if let some message := SQLite.Scalar.admissionError expression then throw message
  unless ctx.namesBound expression && !expression.any ignoredForbidden do
    throw "unsupported or unbound ignored aggregate ordering expression"

def sameArgument (ctx : CoreExpr.Context) (left right : Expr) : Bool :=
  let left := CoreCompoundTail.normalizeFuel (some ctx) left.height left
  let right := CoreCompoundTail.normalizeFuel (some ctx) right.height right
  CoreCompoundTail.sameFuel (max left.height right.height) left right

def sameOrdering (ctx : CoreExpr.Context) (left right : List OrderTerm) : Bool :=
  left.length == right.length && (left.zip right).all (fun (a,b) =>
    a.descending == b.descending &&
      a.nullsFirst.getD (!a.descending) == b.nullsFirst.getD (!b.descending) && sameArgument ctx a.expr b.expr)

def identicalKey (ctx : CoreExpr.Context) (argument : Expr) (terms : List OrderTerm) : Bool :=
  match terms with | [term] => sameArgument ctx argument term.expr | _ => false

def equalKeys (directions : List CoreOrder.KeySpec) (left right : List Core.Value) : Bool :=
  !CoreOrder.keysLess directions left right && !CoreOrder.keysLess directions right left

def arrange (ctx : CoreExpr.Context) (rows : List (List Core.Value)) (argument : Expr)
    (distinct : Bool) (kind : SQLite.Collation.Kind) (terms : List OrderTerm) :
    Except String (List (List Core.Value)) := do
  let directions ← terms.mapM CoreOrder.specification
  let replaceEqual := distinct && identicalKey ctx argument terms
  let mut seen : List Core.Value := []
  let mut sorted : List CoreOrder.SortRow := []
  for row in rows do
    let keys ← ctx.projectRow row (terms.map (·.expr))
    let value ← SQLSurface.value (← ctx.eval row argument)
    if replaceEqual then
      sorted := sorted.filter (fun old => !equalKeys directions old.keys keys)
    else if distinct then
      if seen.any (fun old => SQLite.Collation.compareValue kind old value == .eq) then continue
      seen := value :: seen
    sorted := CoreOrder.insertStable directions { projected := { source := row, output := [value] }, keys } sorted
  return sorted.map (fun row => row.projected.source)

theorem sameOrdering_nil (ctx : CoreExpr.Context) : sameOrdering ctx [] [] = true := rfl

end SQLeanite.CoreAggregateOrdering
