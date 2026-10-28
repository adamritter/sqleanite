import SQLeanite.CoreSQL.JoinScalarBind

namespace SQLeanite
namespace CoreSQL

def joinSearchRootFixed (context : JoinContext) (prepared : JoinScalarPrepared)
    (root : Option JoinSearchAccess) (on : Option Expr) : Bool :=
  root.any fun access => (joinSearchSingletonKey access).any fun key =>
    (joinScalarReference context prepared key.column).any fun ref =>
      [on, prepared.select.where_].any fun condition =>
        (joinSearchConstantRoot context prepared ref.side condition).any fun candidate =>
          (joinSearchSingletonKey candidate).any (joinSearchFixesColumn prepared)

/-- Keep a constraint's operation and key expression while propagating its
rowid column across a direct rowid equality. -/
def JoinSearchKey.retarget (key : JoinSearchKey) (column : Expr) : JoinSearchKey :=
  { key with column }

theorem JoinSearchKey.retarget_value (key : JoinSearchKey) (column : Expr) :
    (key.retarget column).value = key.value ∧
      (key.retarget column).operation = key.operation := ⟨rfl, rfl⟩

def joinSearchRowidEquality (context : JoinContext) (prepared : JoinScalarPrepared)
    (on : Option Expr) : Bool :=
  (on.map SQLite.Scalar.conditionTerms |>.getD []).any fun term =>
    match SQLite.ExprCollation.strip term with
    | .binary .eq left right =>
        match joinScalarReference context prepared left, joinScalarReference context prepared right with
        | some l, some r => l.side != r.side &&
            l.column == (if l.side == .left then context.leftSchema else context.rightSchema).primaryKey &&
            r.column == (if r.side == .left then context.leftSchema else context.rightSchema).primaryKey
        | _, _ => false
    | _ => false

def joinSearchRangeBound (context : JoinContext) (prepared : JoinScalarPrepared)
    (term : Expr) : Option (CoreJoin.Side × JoinSearchKey) := do
  let key ← joinSearchKey? context prepared .left term <|> joinSearchKey? context prepared .right term
  unless [.lt, .le, .gt, .ge].contains key.operation && prepared.context.constantExpression key.value do none
  let ref ← joinScalarReference context prepared key.column
  unless ref.column == (if ref.side == .left then context.leftSchema else context.rightSchema).primaryKey do none
  return (ref.side, key)

/-- A direct rowid equality carries constant bounds from either source to the
outer cursor. The key value and comparison operator are retained unchanged. -/
def joinSearchRangeRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (on : Option Expr) : Option JoinSearchAccess := do
  let equal := joinSearchRowidEquality context prepared on
  let keys := (joinSearchRangeTerms (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD [])).filterMap fun term => do
    let (origin, key) ← joinSearchRangeBound context prepared term
    unless origin == side || equal do none
    return key
  let lower := joinSearchChoose prepared (keys.filter (fun key => [.gt, .ge].contains key.operation))
  let upper := joinSearchChoose prepared (keys.filter (fun key => [.lt, .le].contains key.operation))
  unless lower.isSome || upper.isSome do none
  let schema := if side == .left then context.leftSchema else context.rightSchema
  let column ← joinScalarOperand context (.column ⟨side, schema.primaryKey⟩)
  return .range (lower.map (·.retarget column)) (upper.map (·.retarget column))

/-- Constant ON bounds can drive the outer cursor when an ORDER BY on
that rowid selects it. WHERE bounds retain their existing priority. -/
def joinSearchIndependentRangeRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (on : Option Expr) : Option JoinSearchAccess := do
  if let some root := joinSearchRangeRoot context prepared side on then return root
  let keys := (joinSearchRangeTerms (on.map SQLite.Scalar.conditionTerms |>.getD [])).filterMap fun term => do
    let (origin, key) ← joinSearchRangeBound context prepared term
    unless origin == side do none
    return key
  let lower := joinSearchChoose prepared (keys.filter (fun key => [.gt, .ge].contains key.operation))
  let upper := joinSearchChoose prepared (keys.filter (fun key => [.lt, .le].contains key.operation))
  unless lower.isSome || upper.isSome do none
  return .range lower upper

/-- Unindexed null tests on an originally nullable source reduce its estimated
output. where.c:whereLoopOutputAdjust decrements LogEst for each such term.
Keep the two-source null-test score independent of actual stored row values. -/
def joinSearchNullFilterCount (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Nat :=
  ((prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter fun term =>
    match SQLite.ExprCollation.strip term with
    | .isNull arg _ => (joinScalarReference context prepared arg).any (fun ref =>
        ref.side == side && joinScalarOriginallyNullable context prepared ref)
    | _ => false).length

def joinSearchRetainedRightNullFilter (context : JoinContext) (prepared : JoinScalarPrepared) : Bool :=
  joinSearchNullFilterCount context prepared .right != 0

/-- For the unordered two-source range/point shape, the derived right range
drives the left point lookup. Extra left filters retain the left-driven plan. -/
def joinSearchTransitiveRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (on : Option Expr) : Option JoinSearchAccess := do
  unless joinSearchRowidEquality context prepared on do none
  let onTerms := on.map SQLite.Scalar.conditionTerms |>.getD []
  if onTerms.any (fun term => joinScalarOnlySide context prepared .left term &&
      !prepared.context.constantExpression term) &&
      !joinSearchRetainedRightNullFilter context prepared then none
  let whereTerms := joinSearchRangeTerms (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD [])
  let compatibleNullTest := fun term => match SQLite.ExprCollation.strip term with
    | .isNull arg true => (joinScalarReference context prepared arg).any (fun ref =>
        ref.side == .right || !joinScalarOriginallyNullable context prepared ref)
    | _ => false
  unless whereTerms.all (fun term => prepared.context.constantExpression term ||
      compatibleNullTest term ||
      (joinSearchRangeBound context prepared term).any (fun bound => bound.1 == .left)) do none
  joinSearchRangeRoot context prepared .right on

/-- In an unordered rowid-equality join, a retained right-side null
filter gives that scan a lower row estimate. A rowid null test originating on
the nullable side survives early expression preparation, even after reduction.
This covers this two-source plan shape, not the general statistics solver. -/
def joinSearchNullFilterRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (on : Option Expr) : Option JoinSearchAccess := do
  unless joinSearchRowidEquality context prepared on do none
  let onTerms := on.map SQLite.Scalar.conditionTerms |>.getD []
  if onTerms.any (fun term => joinScalarOnlySide context prepared .left term &&
      !prepared.context.constantExpression term) then none
  let terms := prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []
  let test := fun term => match SQLite.ExprCollation.strip term with
    | .isNull arg _ => joinScalarReference context prepared arg
    | _ => none
  unless terms.all (fun term => prepared.context.constantExpression term ||
      (test term).any (fun ref => ref.side == .right || !joinScalarOriginallyNullable context prepared ref)) do none
  unless terms.any (fun term => (test term).any (fun ref => ref.side == .right &&
      joinScalarOriginallyNullable context prepared ref)) do none
  return .scan

/-- An unfixed rowid equality can carry a singleton bound to the opposite
cursor. A fixed left operand also generates the swapped constant constraint.
Source-local left filters retain the left-driven singleton plan. -/
def joinSearchDerivedRightRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (leftRoot : Option JoinSearchAccess) (on : Option Expr) : Option JoinSearchAccess := do
  let root ← leftRoot
  let key ← joinSearchSingletonKey root
  let terms := on.map SQLite.Scalar.conditionTerms |>.getD []
  let rootTerm := fun term => (joinSearchKey? context prepared .left term).any fun candidate =>
    [.eq, .is].contains candidate.operation && prepared.context.constantExpression candidate.value &&
      joinScalarReference context prepared candidate.column == joinScalarReference context prepared key.column
  if terms.any (fun term => joinScalarOnlySide context prepared .left term &&
      !prepared.context.constantExpression term && !rootTerm term) then none
  unless joinSearchRowidEquality context prepared on do none
  if joinSearchRootFixed context prepared leftRoot on &&
      joinSearchNullFilterCount context prepared .right ≤ joinSearchNullFilterCount context prepared .left then
    unless terms.any (fun term => match SQLite.ExprCollation.strip term with
      | .binary .eq left right =>
          (joinScalarReference context prepared left).any (fun ref =>
            ref.side == .left && ref.column == context.leftSchema.primaryKey) &&
          (joinScalarReference context prepared right).any (fun ref =>
            ref.side == .right && ref.column == context.rightSchema.primaryKey)
      | _ => false) do none
  let column ← joinScalarOperand context (.column ⟨.right, context.rightSchema.primaryKey⟩)
  return .point (key.retarget column)

/-- Default rowid range estimates reduce LogEst by 20 for one bound and
60 for both bounds (where.c:whereRangeScanEst). Only available opposite-source
bounds participate; this estimate never inspects stored row values. -/
def joinSearchRowidRangeReduction (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (on : Option Expr) : Nat :=
  let schema := if side == .left then context.leftSchema else context.rightSchema
  let keys := joinSearchKeys context prepared side (on.map SQLite.Scalar.conditionTerms |>.getD [])
  let rowid := fun key => (joinScalarReference context prepared key.column).any (fun ref => ref.column == schema.primaryKey)
  let lower := keys.any (fun key => rowid key && [.gt, .ge].contains key.operation)
  let upper := keys.any (fun key => rowid key && [.lt, .le].contains key.operation)
  if lower && upper then 60 else if lower || upper then 20 else 0

/-- In an unordered pair of unindexed scans, source-local residual predicates
lower the source's default row estimate by one LogEst unit each. Keep existing
point/range/automatic choices and probability-hinted plans outside this rule. -/
def joinSearchScanFilterRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (on : Option Expr) : Option JoinSearchAccess := do
  let terms := (on.map SQLite.Scalar.conditionTerms |>.getD []) ++
    (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD [])
  unless terms.all (fun term => !term.any (fun node => match node with
    | .call name _ _ => SQLite.Probability.recognizesName (SQLite.Scalar.scalarFunctionName name)
    | _ => false)) do none
  for side in [CoreJoin.Side.left, .right] do
    let keys := joinSearchKeys context prepared side terms
    let schema := if side == .left then context.leftSchema else context.rightSchema
    unless !keys.any (fun key =>
      (joinScalarReference context prepared key.column).any (fun ref => ref.column == schema.primaryKey) ||
        ([.eq, .is].contains key.operation && joinSearchIndexAffinity prepared key)) do none
  let count := fun side => (terms.filter fun term =>
    !prepared.context.constantExpression term && joinScalarOnlySide context prepared side term &&
      (match SQLite.ExprCollation.strip term with
        | .isNull argument true => !(joinScalarReference context prepared argument).any
            (fun ref => !joinScalarOriginallyNullable context prepared ref)
        | _ => true)).length
  unless count .right > count .left do none
  return .scan

/-- One source traversal plan serves both streaming and materialized results.
A right-driven rowid lookup also determines the order in which a bounded sorter
sees candidates; it must not be changed to a left-driven cross product. -/
structure JoinScalarTraversal where
  exchanged : Bool
  reverseLeft : Bool
  reverseRight : Bool
  ordered : Bool
  root : Option JoinSearchAccess := none

def joinScalarTraversal (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (terms : List OrderTerm) (on : Option Expr) : JoinScalarTraversal :=
  let aggregate := !prepared.select.groupBy.isEmpty ||
    prepared.select.columns.any (fun c => CoreAggregate.containsAggregate c.expr)
  let probesLeft := on.any (fun e => joinScalarProbesRowid context prepared .left e.height e) ||
    context.shared.any (fun column => column.left == context.leftSchema.primaryKey)
  let probesRight := on.any (fun e => joinScalarProbesRowid context prepared .right e.height e) ||
    context.shared.any (fun column => column.right == context.rightSchema.primaryKey)
  let mayExchange := !source.leftJoin && !source.rightJoin && !source.crossJoin
  let sharedLeft := joinUsingAutomaticProbe context prepared .left
  let sharedRight := joinUsingAutomaticProbe context prepared .right
  let leadingRight := terms.head?.any (fun term =>
    (joinScalarReference context prepared term.expr).any (fun ref => ref.side == .right && ref.column == context.rightSchema.primaryKey))
  let rightOnly := on.any (fun expression =>
    !prepared.context.constantExpression expression && joinScalarOnlySide context prepared .right expression)
  let leftRange := joinSearchRowidRangeReduction context prepared .left on
  let rightRange := joinSearchRowidRangeReduction context prepared .right on
  let leadingLeft := terms.head?.any (fun term =>
    (joinScalarReference context prepared term.expr).any (fun ref => ref.side == .left && ref.column == context.leftSchema.primaryKey))
  -- An unbounded outer-rowid ORDER can outweigh a dependent range lookup.
  -- An independent WHERE range on the right still supplies a selective root.
  let rangeExchange := !probesLeft && !probesRight && leftRange > rightRange &&
    (!leadingLeft || prepared.select.limit.isSome ||
      (joinSearchRangeRoot context prepared .right on).isSome)
  let leftRoot := (if mayExchange then joinSearchConstantRoot context prepared .left on else none).orElse
    (fun _ => if !source.rightJoin then
      joinSearchConstantRoot context prepared .left prepared.select.where_ else none)
  let rightRoot := if mayExchange then
      ((joinSearchConstantRoot context prepared .right on).orElse
        (fun _ => joinSearchConstantRoot context prepared .right prepared.select.where_)).orElse
        (fun _ => if terms.isEmpty then
          (joinSearchTransitiveRoot context prepared on).orElse
            (fun _ => (joinSearchNullFilterRoot context prepared on).orElse
              (fun _ => joinSearchScanFilterRoot context prepared on)) else none)
    else none
  let rightRoot := rightRoot.orElse (fun _ =>
    if mayExchange && !probesLeft && !probesRight &&
        (leftRange > 0 || leadingRight || (terms.isEmpty && rightOnly && rightRange == 0 &&
          joinSearchRowidRangeReduction context prepared .right prepared.select.where_ > 20)) &&
        (rangeExchange || !leadingLeft || prepared.select.limit.isSome) then
      joinSearchIndependentRangeRoot context prepared .right on else none)
  let rightRoot := match rightRoot with
    | some (.membership ..) => if leadingLeft && prepared.select.limit.isNone then none else rightRoot
    | _ => rightRoot
  let rightNeedsPoint := match rightRoot with
    | none | some .scan | some (.range ..) => true
    | _ => false
  let derivedRight := if mayExchange && rightNeedsPoint then
      joinSearchDerivedRightRoot context prepared leftRoot on else none
  let rightRoot := derivedRight.orElse (fun _ => rightRoot)
  let filteredRightPoint := leftRoot.any JoinSearchAccess.singleton &&
    rightRoot.any JoinSearchAccess.singleton &&
    joinSearchNullFilterCount context prepared .right > joinSearchNullFilterCount context prepared .left
  let exchanged := mayExchange && (leftRoot.isNone || derivedRight.isSome || filteredRightPoint) &&
    (rightRoot.isSome || (probesLeft && !probesRight) ||
      (sharedLeft && !sharedRight && !probesRight) || rangeExchange)
  let root := if exchanged then rightRoot else leftRoot
  let singleton := root.any JoinSearchAccess.singleton
  let outerSide := if exchanged then CoreJoin.Side.right else .left
  let outerSchema := if exchanged then context.rightSchema else context.leftSchema
  let innerSchema := if exchanged then context.leftSchema else context.rightSchema
  let leadingOuter := !aggregate && terms.head?.any (fun term =>
    (joinScalarReference context prepared term.expr).any
      (fun ref => ref.side == outerSide && ref.column == outerSchema.primaryKey))
  let leadingInner := singleton && !aggregate && terms.head?.any (fun term =>
    (joinScalarReference context prepared term.expr).any
      (fun ref => ref.side != outerSide && ref.column == innerSchema.primaryKey))
  let outerReverse := leadingOuter && terms.head?.any (·.descending)
  let root := root.orElse (fun _ => if !source.leftJoin && !source.rightJoin then
      joinSearchRangeRoot context prepared outerSide on else none)
  let root := match root with
    | some (.range start finish) => if outerReverse then some (.range finish start) else root
    | _ => root
  -- USING/NATURAL share the same index-order restriction as explicit ON;
  -- a shared rowid conjunct supplies a point lookup even with other keys.
  let automatic := !singleton &&
    ((if exchanged then sharedLeft else sharedRight) ||
      (!exchanged && on.any (fun e => joinScalarAutomaticProbe context prepared e.height e)))
  let innerPoint := if exchanged then probesLeft else probesRight
  let outerTermsOnly := terms.all (fun term => (joinScalarReference context prepared term.expr).any
    (fun ref => ref.side == outerSide))
  let prefixOrdered := (leadingOuter || leadingInner) && (innerPoint || !automatic || outerTermsOnly) &&
    terms.all (fun term => (joinScalarReference context prepared term.expr).any
      (fun ref => ref.side == outerSide || ref.column == innerSchema.primaryKey))
  let ordered := prefixOrdered && !source.rightJoin
  let innerReverse := prefixOrdered && (terms.find? (fun term =>
    (joinScalarReference context prepared term.expr).any (fun ref => ref.side != outerSide))).any (·.descending)
  { exchanged
    reverseLeft := if exchanged then innerReverse else outerReverse
    reverseRight := if exchanged then outerReverse else innerReverse
    ordered, root }

/-- select.c:constInsert visits the rightmost equality first. A replacement
has no expression affinity and uses BINARY comparison. Origin indices retain
which column occurrence defines, rather than consumes, the fixed value. -/
def joinFixedColumns (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (source : TableRef) (on : Option Expr) : List JoinFixedColumn := Id.run do
  if source.leftJoin || source.rightJoin then return []
  let terms := on.map SQLite.Scalar.conditionTerms |>.getD []
  let mut result := []
  for (term, origin) in terms.zipIdx.reverse do
    if let some key := joinSearchKey? context prepared side term then
      if key.operation == .eq && prepared.context.constantExpression key.value &&
          (prepared.context.affinity key.value).isNone &&
          key.collation? == some .binary then
        if let .column qualifier name := key.column then
          if let some index := prepared.context.column? qualifier name then
            unless result.any (fun item => item.index == index) do
              result := result ++ [{
                index := index
                origin := origin
                expression := key.value
                affinity := (prepared.context.affinity key.column).getD .blob }]
  return result

/-- BLOB-affinity fixed columns are substituted only as immediate comparison
operands; the right operand is protected when the left carries TEXT affinity. -/
def joinFixedReady (context : JoinContext) (prepared : JoinScalarPrepared)
    (outer : Option CoreJoin.Side) (fixed : List JoinFixedColumn) (markedBounds : Bool) : Nat → Bool → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, blobAllowed, expression =>
      let ready := joinFixedReady context prepared outer fixed markedBounds fuel false
      match expression with
      | .literal .. => true
      | .column qualifier name =>
          (joinScalarReference context prepared expression).any (fun ref => outer == some ref.side) ||
            (prepared.context.column? qualifier name).any (fun index => fixed.any
              (fun item => item.index == index && (item.affinity != .blob || blobAllowed)))
      | .unary _ argument | .collate argument _ | .isNull argument _ => ready argument
      | .binary operation left right =>
          if [.eq, .lt, .le, .gt, .ge, .is].contains operation then
            joinFixedReady context prepared outer fixed markedBounds fuel true left &&
              joinFixedReady context prepared outer fixed markedBounds fuel (prepared.context.affinity left != some .text) right
          else ready left && ready right
      | .call "__sqlean_between" arguments false =>
          match arguments.toList with
          | [argument, lower, upper] =>
              -- select.c:unsetJoinExpr clears pLeft and function arguments,
              -- but retains original outer markings on a BETWEEN bound list.
              let bound := joinFixedReady context prepared outer
                (if markedBounds then [] else fixed) markedBounds fuel false
              ready argument && bound lower && bound upper
          | _ => false
      | .call _ arguments false => arguments.all ready
      | .inList argument values _ _ => ready argument && values.all ready
      | .case_ base branches otherwise => base.all ready && otherwise.all ready &&
          branches.all (fun (condition, value) => ready condition && ready value)
      | _ => false

/-- Original outer markings prevent constant substitution in the BETWEEN
bound list, while its tested pLeft operand uses the ordinary fixed-column walk. -/
theorem joinFixedReady_between_marked (context : JoinContext) (prepared : JoinScalarPrepared)
    (outer : Option CoreJoin.Side) (fixed : List JoinFixedColumn) (fuel : Nat)
    (argument lower upper : Expr) :
    joinFixedReady context prepared outer fixed true (fuel + 1) false
      (.call "__sqlean_between" #[argument, lower, upper] false) =
      (joinFixedReady context prepared outer fixed true fuel false argument &&
        joinFixedReady context prepared outer [] true fuel false lower &&
        joinFixedReady context prepared outer [] true fuel false upper) := rfl

def joinFixedEarly (context : JoinContext) (prepared : JoinScalarPrepared)
    (outer : CoreJoin.Side) (fixed : List JoinFixedColumn) (on : Option Expr) : List Expr :=
  (on.map SQLite.Scalar.conditionTerms |>.getD []).zipIdx.filterMap fun (term, index) =>
    if fixed.any (fun item => item.origin == index) then none
    else if joinFixedReady context prepared (some outer) fixed
        (prepared.nullableLeft || prepared.nullableRight) term.height false term then some term
    else none

/-- EP_FixedCol keeps the column's affinity and applies that affinity when
loading the constant value. Other source values keep the ordinary lookup. -/
def joinFixedLookup (prepared : JoinScalarPrepared) (input : List Core.Value)
    (fixed : List JoinFixedColumn) (qualifier : Option String) (name : String) : Except String Value := do
  let index := prepared.context.column? qualifier name
  if let some item := fixed.find? (fun item => index == some item.index) then
    let value ← prepared.context.eval input item.expression
    CoreExpr.value (SQLite.PhysicalAffinity.write item.affinity (← SQLSurface.value value))
  else prepared.context.lookup input qualifier name

def joinFixedMatches (prepared : JoinScalarPrepared) (input : List Core.Value)
    (fixed : List JoinFixedColumn) (terms : List Expr) : Except String Bool :=
  let context : CoreExpr.Context := { prepared.context with fixedColumns := fixed.map (fun item => item.index) }
  SQLite.Scalar.testTermsWithConstants (joinFixedLookup prepared input fixed)
    context.affinity context.constantExpression
    (terms.map (fun term => SQLite.Scalar.prepare (context.bindNames term)))

/-- A NOT NULL test on an originally non-null column is removed during
expression preparation, before fixed constants can introduce value evaluation. -/
def joinScalarTrivialNotNull (context : JoinContext) (prepared : JoinScalarPrepared)
    (term : Expr) : Bool :=
  match SQLite.ExprCollation.strip term with
  | .isNull argument true => (joinScalarReference context prepared argument).any
      (fun ref => !joinScalarOriginallyNullable context prepared ref)
  | _ => false

/-- Fixed ON columns can turn WHERE terms into constant predicates. Evaluate
only substitutions allowed by the original affinity walk, before either cursor.
Outer joins retain their original constant-WHERE preparation. -/
def joinFixedConstantMatches (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (on : Option Expr) : Except String Bool :=
  if source.leftJoin || source.rightJoin then
    prepared.context.constantMatches prepared.select.where_
  else
    let fixed := joinFixedColumns context prepared .left source on ++
      joinFixedColumns context prepared .right source on
    let ctx : CoreExpr.Context := { prepared.context with fixedColumns := fixed.map (fun item => item.index) }
    let terms := (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
      (fun term => !joinScalarTrivialNotNull context prepared term && ctx.constantExpression term &&
        joinFixedReady context prepared none fixed false term.height false term)
    joinFixedMatches prepared [] fixed terms

theorem joinFixedConstantMatches_outer (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (on : Option Expr)
    (outer : (source.leftJoin || source.rightJoin) = true) :
    joinFixedConstantMatches context prepared source on =
      prepared.context.constantMatches prepared.select.where_ := by
  unfold joinFixedConstantMatches
  rw [outer]
  rfl

theorem joinFixedLookup_unfixed (prepared : JoinScalarPrepared) (input : List Core.Value)
    (fixed : List JoinFixedColumn) (qualifier : Option String) (name : String)
    (absent : fixed.find? (fun item => prepared.context.column? qualifier name == some item.index) = none) :
    joinFixedLookup prepared input fixed qualifier name = prepared.context.lookup input qualifier name := by
  simp [joinFixedLookup, absent]

/-- A BETWEEN pair consumes one parent predicate in whereLoopOutputAdjust,
whereas independently selected lower/upper terms consume two. Keep the pair
when both bounds can drive the same rowid cursor. Virtual children are appended
while original terms are analyzed right-to-left, including ON after WHERE. -/
def joinSearchBetweenPair (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (terms : List Expr) : Option (JoinSearchKey × JoinSearchKey) :=
  terms.reverse.findSome? fun term => do
    let .call "__sqlean_between" arguments false := SQLite.ExprCollation.strip term | none
    let [argument, lower, upper] := arguments.toList | none
    let ref ← joinScalarReference context prepared argument
    let schema := if side == .left then context.leftSchema else context.rightSchema
    unless ref.side == side && ref.column == schema.primaryKey &&
        joinScalarOnlySide context prepared (joinSearchOpposite side) lower &&
        joinScalarOnlySide context prepared (joinSearchOpposite side) upper do none
    return ({ column := argument, value := lower, operation := .ge },
      { column := argument, value := upper, operation := .le })

end CoreSQL

end SQLeanite
