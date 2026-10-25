import SQLeanite.CoreExpr
import SQLeanite.SQLite.PlannerCost
import Init.Data.List.Sort.Lemmas

/-! One-pass UPDATE order for admitted single-column BINARY indexes. Default
size/selectivity estimates choose a scan; changing rowids or that scan index
requires update.c's rowid-collection path. STAT1/STAT4, expression/partial
indexes and the full multi-index OR cost search are not implemented here. -/
namespace SQLeanite.CoreUpdateScan

structure Access where
  column : Nat
  equal : Bool := false
  nullEqual : Bool := false
  inCount : Nat := 1
  lower : Bool := false
  upper : Bool := false
  virtualNull : Bool := false
  truth : Int := 1

def column? (ctx : CoreExpr.Context) (expression : Expr) : Option Nat :=
  match SQLite.ExprCollation.strip expression with
  | .column qualifier name => ctx.column? qualifier name
  | _ => none

def comparisonColumn? (ctx : CoreExpr.Context) (left right : Expr) : Option (Nat × Bool) :=
  if SQLite.ExprCollation.binaryKind? left right != some .binary then none
  else if SQLite.Scalar.constantExpression right then (column? ctx left).map (·, false)
  else if SQLite.Scalar.constantExpression left then (column? ctx right).map (·, true)
  else none

/-- An OR of equalities on one column becomes an IN access term. Other OR
forms retain UPDATE's rowid collection, unless an AND term selects a scan. -/
def orEqualities (ctx : CoreExpr.Context) : Nat → Expr → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, .binary .or left right => do
      let (column, count) ← orEqualities ctx fuel left
      let (other, more) ← orEqualities ctx fuel right
      if column == other then some (column, count + more) else none
  | _ + 1, .binary .eq left right => (comparisonColumn? ctx left right).map fun (column, _) => (column, 1)
  | _, _ => none

def globColumn? (ctx : CoreExpr.Context) (value pattern : Expr) : Option Nat := do
  let column ← column? ctx value
  let .literal (.text text) _ := pattern | none
  let prefixChars := text.toList.takeWhile (fun c => c != '*' && c != '?' && c != '[' && c != Char.ofNat 0)
  let first ← prefixChars.head?
  let textAffinity := (ctx.schema.columns[column]?).any (fun c => c.affinity == .text)
  if !textAffinity && (first.isDigit || first == '-' || first == '+') then none else some column

def hintTruth (name : String) (arguments : Array Expr) : Int :=
  match aggregateFunctionName name, arguments.toList with
  | "likely", _ => -1
  | "unlikely", _ => -40
  | "likelihood", [_, .literal (.real probability) _] =>
      SQLite.PlannerCost.logEst (probability * 134217728.0).toUInt64.toNat - 270
  | _, _ => 1

def accesses (ctx : CoreExpr.Context) : Nat → Int → Expr → List Access
  | 0, _, _ => []
  | fuel + 1, truth, expression =>
      match expression with
      | .binary .and left right => accesses ctx fuel truth left ++ accesses ctx fuel truth right
      | .collate expression _ => accesses ctx fuel truth expression
      | .call name arguments false =>
          match SQLite.Probability.input? name arguments with
          | some input => accesses ctx fuel (hintTruth name arguments) input
          | none =>
              match SQLite.Scalar.scalarFunctionName name, arguments.toList with
              | "glob", [pattern, value] =>
                  (globColumn? ctx value pattern).toList.map fun column => { column, lower := true, upper := true, truth }
              | _, _ => []
      | .binary .glob value pattern =>
          (globColumn? ctx value pattern).toList.map fun column => { column, lower := true, upper := true, truth }
      | .binary .or .. =>
          (orEqualities ctx expression.height expression).toList.map fun (column, count) =>
            { column, equal := true, inCount := count, truth }
      | .binary operation left right =>
          if [.eq, .is, .lt, .le, .gt, .ge].contains operation then
            (comparisonColumn? ctx left right).toList.map fun (column, reversed) =>
              let equal := operation == .eq || operation == .is
              let lower := if reversed then operation == .lt || operation == .le else operation == .gt || operation == .ge
              { column, equal, lower := !equal && lower, upper := !equal && !lower, truth }
          else []
      | .inList argument values false _ =>
          if !values.isEmpty && values.all SQLite.Scalar.constantExpression &&
              SQLite.ExprCollation.kind? argument == some .binary then
            (column? ctx argument).toList.map fun column => { column, equal := true, inCount := values.size, truth }
          else []
      | .isNull argument negated =>
          (column? ctx argument).toList.filterMap fun column =>
            if (ctx.schema.columns[column]?).any (·.notNull) then none
            else some { column, equal := !negated, nullEqual := !negated, lower := negated, virtualNull := negated, truth }
      | _ => []

def boundEstimate (term : Access) (rows : Int) : Int :=
  if term.truth ≤ 0 then rows + term.truth else if term.virtualNull then rows else rows - 20

def rangeEstimate (terms : List Access) : Int :=
  let lower := terms.filter (·.lower)
  let upper := terms.filter (·.upper)
  let bottom := lower.foldl (fun current term => min current (boundEstimate term 200)) 200
  let top := upper.foldl (fun current term => min current (boundEstimate term 200)) 200
  let pairedDefault := lower.any (fun term => term.truth > 0) && upper.any (fun term => term.truth > 0)
  let guess := bottom + top - 200 - if pairedDefault then 20 else 0
  min (200 - (if lower.isEmpty then 0 else 1) - (if upper.isEmpty then 0 else 1)) (max 10 guess)

def usedColumns (ctx : CoreExpr.Context) (expressions : List Expr) : List Nat :=
  (List.range ctx.schema.columns.length).filter fun column =>
    expressions.any fun expression => (ctx.bindNames expression).any (fun node => match node with
      | .column qualifier name => ctx.column? qualifier name == some column
      | _ => false)

/-- Compare the actual default index costs, including covering access and
IN multiplicity. Candidate enumeration preserves SQLite's newest-index tie. -/
def chosenColumn? (ctx : CoreExpr.Context) (stored : Core.Table) (assignments : List (Nat × Expr))
    (condition : Option Expr) : Option Nat := Id.run do
  let terms := condition.toList.flatMap fun expression =>
    let prepared := SQLite.Scalar.prepare (ctx.bindNames expression)
    accesses ctx prepared.height 1 prepared
  let used := usedColumns ctx ((assignments.map (·.2)) ++ condition.toList)
  let candidates := (ctx.schema.primaryKey, true) :: stored.indexes.reverse.map (fun index =>
    (index.column, index.unique || index.isImplicitPrimary stored.schema))
  let mut best : Int := 216
  let mut selected := none
  for (column, unique) in candidates do
    let available := terms.filter (fun term => term.column == column)
    let covering := used.all (fun used => used == column || used == ctx.schema.primaryKey)
    for term in available.filter (·.equal) do
      let input := if term.truth ≤ 0 && column != ctx.schema.primaryKey then 200 + term.truth
        else (if unique then 0 else 33) + (if term.nullEqual then 10 else 0)
      let multiplicity := SQLite.PlannerCost.logEst term.inCount
      let rows := input - if term.truth ≤ 0 then multiplicity else 0
      let cost := SQLite.PlannerCost.scan ctx.schema column rows covering + multiplicity
      if cost < best then best := cost; selected := some column
    if available.any (fun term => term.lower || term.upper) then
      let cost := SQLite.PlannerCost.scan ctx.schema column (rangeEstimate available) covering
      if cost < best then best := cost; selected := some column
  return selected

def byColumn (column : Nat) (rows : List Core.Row) : List Core.Row :=
  rows.mergeSort (fun left right =>
    PhysicalQuery.compareValue (left.values[column]?.getD .null) (right.values[column]?.getD .null) != .gt)

theorem byColumn_perm (column : Nat) (rows : List Core.Row) : (byColumn column rows).Perm rows :=
  List.mergeSort_perm _ _

def order (ctx : CoreExpr.Context) (stored : Core.Table) (assignments : List (Nat × Expr))
    (condition : Option Expr) (rows : List Core.Row) : Except String (List Core.Row) := do
  if assignments.any (fun assignment => assignment.1 == ctx.schema.primaryKey) then return rows
  let changesUnique := assignments.any fun assignment =>
    assignment.1 == ctx.schema.declaredPrimaryKey || stored.indexes.any (fun index => index.unique && index.column == assignment.1)
  unless changesUnique do return rows
  match chosenColumn? ctx stored assignments condition with
  | none => return rows
  | some column =>
      if column == ctx.schema.primaryKey || assignments.any (fun assignment => assignment.1 == column) then return rows
      return byColumn column rows

end SQLeanite.CoreUpdateScan
