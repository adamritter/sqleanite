import SQLeanite.CoreAggregateHaving
import SQLeanite.CoreCollatedGroup

/-! Expression grouping over Core rows, with HAVING and output ordering.
Grouping keys and retained source rows are distinct: collated-equal rows can
still have different original values. -/
namespace SQLeanite.CoreGrouped

structure GroupTerm where
  expression : Expr
  collation : SQLite.Collation.Kind
  output : Option Nat

def exactExpression (ctx : CoreExpr.Context) (left right : Expr) : Bool :=
  CoreAggregateHaving.sameArgument ctx (some left) (some right)

def resolveGroupExpression (ctx : CoreExpr.Context) (columns : List ResultColumn) :
    Expr → Except String (Expr × Option Nat)
  | .collate expression name => do
      let (resolved, position) ← resolveGroupExpression ctx columns expression
      let resolved := Expr.collate resolved name
      let output := if (CoreOrder.ordinal? (SQLite.ExprCollation.strip expression)).isSome then position
        else columns.zipIdx.foldl (fun found (column, index) =>
          if exactExpression ctx resolved (ctx.bindNames column.expr) then some index else found) none
      return (resolved, output)
  | expression => do
      if let some position := CoreOrder.ordinal? expression then
        unless 1 ≤ position && position.toNat ≤ columns.length do
          throw "GROUP BY position is outside the result columns"
        let some column := columns[position.toNat - 1]? | throw "GROUP BY position is out of range"
        return (ctx.bindNames column.expr, some (position.toNat - 1))
      let expression := ctx.bindNames (CoreAggregateHaving.resolve ctx columns expression)
      let output := columns.zipIdx.foldl (fun found (column, index) =>
        if exactExpression ctx expression (ctx.bindNames column.expr) then some index else found) none
      return (expression, output)

def groupTerms (ctx : CoreExpr.Context) (columns : List ResultColumn)
    (expressions : List Expr) : Except String (List GroupTerm) :=
  expressions.mapM fun expression => do
    let (expression, output) ← resolveGroupExpression ctx columns (SQLite.Scalar.prepare expression)
    ctx.validate expression
    let collation ← SQLite.ExprCollation.require (SQLite.ExprCollation.kind? expression)
    return { expression, collation, output }

/-- Only BINARY group keys are eligible for SQLite's HAVING-to-WHERE move.
Aggregate calls and bare columns outside such keys prevent the move. -/
def constantOrGroupFuel (ctx : CoreExpr.Context) (groups : List GroupTerm) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      if groups.any (fun group => group.collation == .binary &&
          CoreCompoundTail.sameExpression (some ctx) expression group.expression) then true
      else if CoreAggregate.recognizes expression then false
      else
        let constant := constantOrGroupFuel ctx groups fuel
        match expression with
        | .literal _ _ => true
        | .column .. | .star .. | .scalarSubquery .. | .inSubquery .. | .existsSubquery .. => false
        | .unary _ arg | .collate arg _ | .isNull arg _ => constant arg
        | .binary _ left right => constant left && constant right
        | .call _ args _ => args.all constant
        | .inList arg choices _ _ => constant arg && choices.all constant
        | .case_ base branches otherwise => base.all constant && otherwise.all constant &&
            branches.all (fun (condition, result) => constant condition && constant result)

/-- An always-false integer HAVING term stays after aggregation. Other eligible
terms move before grouping, preserving the order of WHERE and HAVING conjuncts. -/
def pushHaving (ctx : CoreExpr.Context) (groups : List GroupTerm)
    (where_ having : Option Expr) : Option Expr × Option Expr :=
  let terms := having.toList.flatMap SQLite.Scalar.conditionTerms
  terms.foldl (fun (condition, retained) term =>
    let moved := constantOrGroupFuel ctx groups term.height term &&
      SQLite.Scalar.staticTruth term != some false
    let append (left : Option Expr) (right : Expr) :=
      some (left.map (fun prior => Expr.binary .and prior right) |>.getD right)
    if moved then (append condition term, retained)
    else (condition, append retained term)) (where_, none)

structure Prepared where
  aggregate : CoreAggregateHaving.Prepared
  groups : List GroupTerm
  ordering : List Expr
  directions : List CoreOrder.KeySpec
  groupDirections : List CoreOrder.KeySpec
  orderedGroups : Bool
  where_ : Option Expr
  originalResults : List Expr

/-- A non-column output reused by GROUP BY reads the stored grouping key.
Column outputs instead follow SQLite's MIN/MAX bare-column representative. -/
def groupOutput (groups : List GroupTerm) (index : Nat) (original lowered : Expr) : Expr :=
  match SQLite.ExprCollation.strip original with
  | .column .. => lowered
  | _ =>
      match (groups.zipIdx.find? (fun (group, _) => group.output == some index)) with
      | none => lowered
      | some (group, position) =>
          let slot := Expr.column (some "__group_key") (toString position)
          match SQLite.ExprCollation.name group.expression with
          | none => slot
          | some name => .collate slot name

/-- Sort payload columns that reuse an ORDER BY key are evaluated from that
key expression, even when GROUP BY had replaced the output by a key register. -/
def orderOutput (ctx : CoreExpr.Context) (columns : List ResultColumn) (raw resolved : Expr) : Option Nat :=
  let raw := SQLite.ExprCollation.strip (SQLite.Scalar.prepare raw)
  match (CoreOrder.bareName? raw).bind (fun name =>
      columns.findIdx? (fun c => c.alias.any (fun alias => alias.toLower == name.toLower))) with
  | some index => some index
  | none => match CoreOrder.ordinal? raw with
      | some position => some (position.toNat - 1)
      | none => columns.zipIdx.foldl (fun found (column, index) =>
          if exactExpression ctx resolved (ctx.bindNames column.expr) then some index else found) none

def prepare (ctx : CoreExpr.Context) (select : Select) : Except String Prepared := do
  unless !select.groupBy.isEmpty do throw "GROUP BY is empty"
  let columns ← CoreOrder.expandResults ctx select.columns.toList
  let groups ← groupTerms ctx columns select.groupBy.toList
  let order ← CoreOrder.resolve ctx columns select.orderBy.toList
  let directions ← order.mapM CoreOrder.specification
  let having := select.having.map (fun expression =>
    SQLite.Scalar.prepare (ctx.bindNames (CoreAggregateHaving.resolve ctx columns expression)))
  unless columns.all (fun column => ctx.namesBound column.expr) &&
      having.all ctx.namesBound && order.all (fun term => ctx.namesBound term.expr) do
    throw "unbound grouped expression"
  let prepareOne (expression : Expr) : CoreAggregate.PrepareM Expr :=
    let expression := SQLite.Scalar.prepare (ctx.bindNames expression)
    CoreAggregate.prepareTemplateFuel ctx true expression.height expression
  -- Validate HAVING before moving any terms, even when a false WHERE will
  -- suppress their evaluation. The moved terms contain no aggregate calls.
  discard <| (having.mapM prepareOne).run #[]
  let where_ := select.where_.map (CoreOrder.resolveAliases ctx columns)
  let (where_, having) := pushHaving ctx groups where_ having
  let _ ← where_.mapM ctx.validate
  if select.distinct then CoreExpr.validateDistinct (columns.map (fun c => ctx.bindNames c.expr))
  let ((expressions, ordering, having), terms) ← (do
    let expressions ← columns.mapM (fun (column : ResultColumn) => prepareOne column.expr)
    let ordering ← order.mapM (fun (term : OrderTerm) => prepareOne term.expr)
    let having ← having.mapM prepareOne
    pure (expressions, ordering, having) :
      CoreAggregate.PrepareM (List Expr × List Expr × Option Expr)).run #[]
  let originals := columns.map (fun c => ctx.bindNames c.expr)
  let orderedGroups := order.isEmpty || (order.length == groups.length &&
    (order.zip groups).all (fun (term, group) => exactExpression ctx (ctx.bindNames term.expr) group.expression &&
      term.nullsFirst.getD (!term.descending) == !term.descending))
  let reused := (select.orderBy.toList.zip order).map (fun (raw, resolved) => orderOutput ctx columns raw.expr resolved.expr)
  let expressions := (originals.zip expressions).zipIdx.map fun ((original, lowered), index) =>
    if !select.distinct && !orderedGroups && reused.contains (some index) then lowered
    else groupOutput groups index original lowered
  let ordering := if select.distinct then (ordering.zip reused).map (fun (expression, position) =>
      (position.bind (fun index => expressions[index]?)).getD expression) else ordering
  -- SQLite copies direction flags before testing expression equality, so
  -- even a separate output sort can reverse the enumeration of group ties.
  let groupDirections := if order.length == groups.length then
      (order.zip groups).map (fun (term, group) =>
        { descending := term.descending, nullsFirst := !term.descending, collation := group.collation })
    else groups.map (fun group => { descending := false, nullsFirst := true, collation := group.collation })
  return { aggregate := { results := { expressions, terms }, having }
           groups := groups
           ordering := ordering
           directions := directions
           groupDirections := groupDirections
           orderedGroups := orderedGroups
           where_ := where_
           originalResults := originals }

structure Bucket where
  keys : List Core.Value
  rows : List (List Core.Value)

def insertRow (kinds : List SQLite.Collation.Kind) (keys row : List Core.Value) :
    List Bucket → List Bucket
  | [] => [{ keys, rows := [row] }]
  | bucket :: rest =>
      if CoreCollatedGroup.compareKeys kinds keys bucket.keys == .eq then
        { bucket with rows := bucket.rows ++ [row] } :: rest
      else bucket :: insertRow kinds keys row rest

def buckets (ctx : CoreExpr.Context) (prepared : Prepared) (rows : List (List Core.Value)) :
    Except String (List Bucket) := do
  let mut groups := []
  for row in rows do
    if ← ctx.matches row prepared.where_ then
      let keys ← ctx.projectRow row (prepared.groups.map (·.expression))
      groups := insertRow (prepared.groups.map (·.collation)) keys row groups
  return groups.mergeSort (fun left right => !CoreOrder.keysLess prepared.groupDirections right.keys left.keys)

def lookup (values : Array Core.Value) (row keys : List Core.Value)
    (qualifier : Option String) (name : String) : Except String Value := do
  if qualifier == some "__group_key" then
    let some index := name.toNat? | throw "invalid group key slot"
    let some value := keys[index]? | throw "group key slot is outside its array"
    CoreExpr.value value
  else CoreAggregateHaving.lookup values row qualifier name

def Prepared.affinity (prepared : Prepared) (ctx : CoreExpr.Context) (expression : Expr) : Option SQLite.Affinity :=
  match SQLite.ExprCollation.strip expression with
  | .column (some "__group_key") name => do
      let index ← name.toNat?
      ctx.affinity (← prepared.groups[index]?).expression
  | _ => CoreAggregateHaving.affinity ctx expression

def Prepared.eval (prepared : Prepared) (ctx : CoreExpr.Context) (values : Array Core.Value)
    (row keys : List Core.Value) (expressions : List Expr) : Except String (List Core.Value) :=
  expressions.mapM fun expression => do
    SQLSurface.value (← SQLite.Scalar.evalWith (lookup values row keys) (prepared.affinity ctx) expression)

def emitOrdered (ctx : CoreExpr.Context) (prepared : Prepared) (distinct : Bool) :
    List Bucket → Nat → Option Nat → List (List Core.Value) → Except String (List (List Core.Value))
  | [], _, _, _ => .ok []
  | bucket :: rest, offset, limit, seen => do
      if limit == some 0 then return []
      let values ← prepared.aggregate.results.accumulate ctx bucket.rows
      let row ← CoreAggregateHaving.representative ctx prepared.aggregate.results.terms bucket.rows true
      unless ← prepared.aggregate.matches ctx values row do
        return ← emitOrdered ctx prepared distinct rest offset limit seen
      let output ← if distinct || offset == 0 then
          some <$> prepared.eval ctx values row bucket.keys prepared.aggregate.results.expressions
        else pure none
      if distinct && output.any (fun result => seen.any (CoreExpr.distinctEqual prepared.originalResults result)) then
        return ← emitOrdered ctx prepared distinct rest offset limit seen
      let seen := output.toList ++ seen
      if offset > 0 then return ← emitOrdered ctx prepared distinct rest (offset - 1) limit seen
      let tail ← emitOrdered ctx prepared distinct rest 0 (limit.map (· - 1)) seen
      return output.toList ++ tail

def emitSorted (ctx : CoreExpr.Context) (prepared : Prepared) (distinct : Bool) (capacity : Option Nat) :
    List Bucket → List (List Core.Value) → List CoreOrder.SortRow → Except String (List CoreOrder.SortRow)
  | [], _, sorted => .ok sorted
  | bucket :: rest, seen, sorted => do
      let values ← prepared.aggregate.results.accumulate ctx bucket.rows
      let row ← CoreAggregateHaving.representative ctx prepared.aggregate.results.terms bucket.rows true
      unless ← prepared.aggregate.matches ctx values row do
        return ← emitSorted ctx prepared distinct capacity rest seen sorted
      let output ← if distinct || capacity.isNone then
          some <$> prepared.eval ctx values row bucket.keys prepared.aggregate.results.expressions
        else pure none
      if distinct && output.any (fun result => seen.any (CoreExpr.distinctEqual prepared.originalResults result)) then
        return ← emitSorted ctx prepared distinct capacity rest seen sorted
      let seen := if distinct then output.toList ++ seen else seen
      let keys ← prepared.eval ctx values row bucket.keys prepared.ordering
      if capacity.any (fun count => sorted.length ≥ count) &&
          sorted.getLast?.any (fun last => !CoreOrder.keysLess prepared.directions keys last.keys) then
        return ← emitSorted ctx prepared distinct capacity rest seen sorted
      let output ← match output with
        | some output => pure output
        | none => prepared.eval ctx values row bucket.keys prepared.aggregate.results.expressions
      let sorted := CoreOrder.insertStable prepared.directions { projected := { source := row, output }, keys } sorted
      let sorted := capacity.map (fun count => sorted.take count) |>.getD sorted
      emitSorted ctx prepared distinct capacity rest seen sorted

def run (ctx : CoreExpr.Context) (select : Select) (rows : List (List Core.Value)) :
    Except String (List (List Core.Value) × Nat) := do
  let prepared ← prepare ctx select
  let width := prepared.aggregate.results.expressions.length
  if select.limit == some 0 then return ([], width)
  unless ← ctx.constantMatches prepared.where_ do return ([], width)
  let groups ← buckets ctx prepared rows
  if prepared.orderedGroups then
    return (← emitOrdered ctx prepared select.distinct groups select.offset select.limit [], width)
  let sorted ← emitSorted ctx prepared select.distinct (select.limit.map (· + select.offset)) groups [] []
  return ((sorted.drop select.offset).map (·.projected.output), width)

theorem insertRow_nil (kinds : List SQLite.Collation.Kind) (keys row : List Core.Value) :
    insertRow kinds keys row [] = [{ keys, rows := [row] }] := rfl

theorem emitOrdered_limit_zero (ctx : CoreExpr.Context) (prepared : Prepared) (distinct : Bool)
    (groups : List Bucket) (offset : Nat) (seen : List (List Core.Value)) :
    emitOrdered ctx prepared distinct groups offset (some 0) seen = .ok [] := by
  cases groups <;> simp [emitOrdered, pure, Except.pure]

end SQLeanite.CoreGrouped
