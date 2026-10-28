import SQLeanite.CoreCreateTableAs
import SQLeanite.CoreSQL.ExecuteFilteredSelectPreservesState
import SQLeanite.SQLite.Scalar.TestBetweenArgumentError

namespace SQLeanite
namespace CoreSQL

def joinScalarBind (context : JoinContext) (expression : Expr) : Except String Expr := do
  let expression := SQLite.Scalar.prepare (joinBindNames context expression)
  let some result := joinScalarBindFuel context expression.height expression
    | throw "unbound or unsupported joined expression"
  return result

/-- The expression context has no stored table or newly allocated rowids.
Every input value is a bound source operand with its original affinity. -/
def joinScalarContext (context : JoinContext) : Except String CoreExpr.Context := do
  let columns ← (joinScalarInputs context).mapIdxM fun index operand => do
    let source ← match operand with
      | .column reference => joinColumnDefinition context reference
      | .mergedColumn _ left _ => joinColumnDefinition context ⟨.left, left⟩
      | _ => throw "invalid joined expression input"
    return ({ name := s!"__joined_{index}", declaredType := CoreCreateTableAs.declaredType source.affinity } : Core.Column)
  return { schema := { name := "__joined", columns, primaryKey := columns.length }, sourceName := "__joined" }

def joinScalarResults (context : JoinContext) : List ResultColumn → Except String (List ResultColumn)
  | [] => .ok []
  | column :: columns => do
      let head ← match column.expr with
        | .star qualifier => do
            let references ← joinCompoundStarReferences context qualifier
            references.mapM fun reference => do
              let some expr := joinScalarOperand context (joinStarOperand context reference)
                | throw "invalid joined star input"
              let definition ← joinColumnDefinition context reference
              return ({ expr, alias := some definition.name } : ResultColumn)
        | expression => do
            let bound ← joinScalarBind context expression
            pure [{ column with expr := bound }]
      return head ++ (← joinScalarResults context columns)

def joinScalarOrderExpression (context : JoinContext) (original expanded : List ResultColumn) :
    Expr → Except String Expr
  | .collate expression name => return .collate (← joinScalarOrderExpression context original expanded expression) name
  | expression => do
      if let some result := (CoreOrder.bareName? expression).bind (CoreOrder.aliasExpression? expanded) then
        return result
      joinScalarBind context (CoreOrder.resolveAliasesWith (joinHasColumn context) original expression)

structure JoinScalarPrepared where
  context : CoreExpr.Context
  select : Select
  on : Option CoreJoin.Predicate
  onExpression : Option Expr := none
  nullableRight : Bool := false
  nullableLeft : Bool := false

def joinScalarPrepare (context : JoinContext) (select : Select) (rightSource : TableRef)
    (storedTexts : List SQLite.StoredText := []) : Except String JoinScalarPrepared := do
  let ctx ← joinScalarContext context
  let ctx := { ctx with
    storedTexts := storedTexts
    storedSources := [
      { table := context.leftSchema.name, rowidColumn := context.leftSchema.primaryKey, offset := 0, width := context.leftSchema.columns.length },
      { table := context.rightSchema.name, rowidColumn := context.leftSchema.columns.length + context.rightSchema.primaryKey, offset := context.leftSchema.columns.length, width := context.rightSchema.columns.length }] }
  let columns ← joinScalarResults context select.columns.toList
  unless !columns.isEmpty && columns.length ≤ SQLite.Limits.maxColumns do
    throw "invalid SELECT result column count"
  let resolve := CoreOrder.resolveAliasesWith (joinHasColumn context) select.columns.toList
  let (on, deferred) := match rightSource.joinOn with
    | none => (none, none)
    | some expression => CoreOrder.resolveJoinOnAliases (joinHasColumn context) select.columns.toList expression
  let (on, onExpression) ← match on with
    | none => pure (none, none)
    | some expression => match joinPredicate context expression (rightSource.leftJoin || rightSource.rightJoin) with
      | .ok predicate => pure (some predicate, none)
      | .error _ => do
          let bound ← joinScalarBind context expression
          unless joinStaticAdmitted context (SQLite.Scalar.prepare (joinBindNames context expression))
              (rightSource.leftJoin || rightSource.rightJoin) do
            throw "unbound or invalid joined ON expression"
          pure (none, some bound)
  let shared ← joinUsingPredicate context
  let on := match on, shared with
    | none, other | other, none => other
    | some left, some right => some (.and left right)
  let where_ ← (CoreOrder.combineAliasConditions (select.where_.map resolve) deferred).mapM (joinScalarBind context)
  let order ← select.orderBy.mapM fun term => do
    return { term with expr := ← joinScalarOrderExpression context select.columns.toList columns term.expr }
  let groups ← select.groupBy.mapM (fun expression => joinScalarBind context (resolve expression))
  let having ← select.having.mapM (fun expression => joinScalarBind context (resolve expression))
  return {
    context := ctx
    on := on
    onExpression := onExpression
    nullableRight := rightSource.leftJoin
    nullableLeft := rightSource.rightJoin
    select := { select with
      columns := (columns.map (fun column => { column with alias := none })).toArray
      sources := #[]
      where_, orderBy := order, groupBy := groups, having } }

def joinScalarRows (context : JoinContext) (source : TableRef) (on : Option CoreJoin.Predicate)
    (left right : List Core.Row) : List CoreJoin.JoinedRow :=
  if source.rightJoin then
    CoreOuterJoin.joinedRows source.leftJoin context.leftSchema.columns.length context.rightSchema.columns.length on left right
  else if source.leftJoin then CoreJoin.leftOuterRows on context.rightSchema.columns.length left right
  else CoreJoin.matchingRows on none (CoreJoin.crossRows left right)

def joinScalarMatches (context : JoinContext) (prepared : JoinScalarPrepared) (outer : Bool)
    (row : CoreJoin.JoinedRow) : Except String Bool := do
  unless CoreJoin.selects prepared.on row do return false
  let some expression := prepared.onExpression | return true
  let input := CoreJoin.projectRow (joinScalarInputs context) row
  if !outer then return ← prepared.context.matches input (some expression)
  let decision := SQLite.StaticCondition.conditionDecision (SQLite.Scalar.conditionTerms expression)
  decision.testWith (fun atom wanted =>
    SQLite.Scalar.testEvaluatedTypedFuel (prepared.context.evalTyped input)
      prepared.context.affinity false atom.height wanted atom) true

/-- Match bookkeeping is completed before WHERE filtering. Dynamic ON values
are evaluated once for each visited pair and can return an expression error. -/
def joinScalarRowsM (context : JoinContext) (prepared : JoinScalarPrepared) (source : TableRef)
    (left right : List Core.Row) (exchanged : Bool := false) : Except String (List CoreJoin.JoinedRow) := do
  if exchanged && !source.leftJoin && !source.rightJoin then
    return ← (right.flatMap (fun r => left.map (fun l => (l, r)))).filterM
      (joinScalarMatches context prepared false)
  if prepared.onExpression.isNone then return joinScalarRows context source prepared.on left right
  let (initial, matched) ← left.foldlM (fun (prior, matched) l => do
    let found ← right.zipIdx.filterM (fun (r, _) => joinScalarMatches context prepared
      (source.leftJoin || source.rightJoin) (l, r))
    let output := if found.isEmpty && source.leftJoin then
        [(l, CoreJoin.nullRow context.rightSchema.columns.length)]
      else found.map (fun (r, _) => (l, r))
    pure (prior ++ output, matched ++ found.map Prod.snd)) ([], [])
  let remaining := if source.rightJoin then
      (right.zipIdx.filter (fun (_, index) => !matched.contains index)).map
        (fun (r, _) => (CoreJoin.nullRow context.leftSchema.columns.length, r))
    else []
  return initial ++ remaining

def joinScalarAggregate (ctx : CoreExpr.Context) (select : Select) (rows : List (List Core.Value)) :
    Except String (Core.Result × Nat) := do
  if select.distinct then CoreExpr.validateDistinct (select.columns.toList.map (·.expr))
  let prepared ← CoreAggregateHaving.prepare ctx select.columns.toList select.orderBy.toList select.having
  let _ ← select.where_.mapM ctx.validate
  if select.limit == some 0 then return ({}, prepared.results.expressions.length)
  let enabled ← ctx.constantMatches select.where_
  let (values, inputs) ← prepared.results.accumulateSelected ctx select.where_
    (if enabled then rows else [])
  let values := values.val
  let representative ← CoreAggregateHaving.representative ctx prepared.results.terms inputs
  let selected ← prepared.matches ctx values representative
  let output ← if !selected || select.offset > 0 then pure []
    else do pure [← prepared.finish ctx values representative]
  return ({ rows := output }, prepared.results.expressions.length)

def joinScalarRun (context : JoinContext) (prepared : JoinScalarPrepared)
    (rows : List CoreJoin.JoinedRow) (orderedInput : Bool := false) : Except String (Core.Result × Nat) := do
  let ctx := prepared.context
  let select := prepared.select
  let inputs := rows.map (CoreJoin.projectRow (joinScalarInputs context))
  if !select.groupBy.isEmpty then
    let (rows, width) ← CoreGrouped.run ctx select inputs
    return ({ rows }, width)
  if select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) then
    return ← joinScalarAggregate ctx select inputs
  unless select.having.isNone do unsupported "HAVING requires an aggregate"
  let expressions ← ctx.projection select.columns.toList
  if select.distinct then CoreExpr.validateDistinct expressions
  let _ ← select.where_.mapM ctx.validate
  let terms ← CoreOrder.resolve ctx select.columns.toList select.orderBy.toList
  let _ ← terms.mapM (CoreOrder.validateTerm ctx)
  if select.limit == some 0 then return ({}, expressions.length)
  unless ← ctx.constantMatches select.where_ do return ({}, expressions.length)
  let projected ← if terms.isEmpty || orderedInput then
      ctx.scanWindow select.where_ expressions select.distinct inputs select.offset select.limit []
    else CoreOrder.scan ctx select.where_ expressions terms select.distinct inputs select.offset select.limit
  return ({ rows := projected.map (·.output) }, expressions.length)

def joinScalarReference (context : JoinContext) (prepared : JoinScalarPrepared)
    (expression : Expr) : Option CoreJoin.ColumnRef := do
  let .column qualifier name := SQLite.ExprCollation.strip expression | none
  let index ← prepared.context.column? qualifier name
  let .column reference ← (joinScalarInputs context)[index]? | none
  return reference

def joinScalarOnlySide (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (expression : Expr) : Bool :=
  !expression.any (fun expression => match expression with
    | .column .. => !(joinScalarReference context prepared expression).any (fun ref => ref.side == side)
    | _ => false)

/-- Conservative counterpart of expr.c:impliesNotNullRow. Ordinary functions,
IS, CASE and nested null tests do not establish a non-null source row. -/
def joinScalarNullWalk (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      let walk := joinScalarNullWalk context prepared side fuel
      match expression with
      | .column .. => (joinScalarReference context prepared expression).any (fun ref => ref.side == side)
      | .collate arg _ | .unary _ arg => walk arg
      | .binary .and left right | .binary .or left right => walk left && walk right
      | .binary op left right =>
          ![.is, .isNot, .like, .glob, .match, .arrow, .arrowText].contains op && (walk left || walk right)
      | .inList arg values _ _ => !values.isEmpty && walk arg
      | .call "__sqlean_between" arguments false =>
          match arguments.toList with
          | [argument, lower, upper] => walk argument || (walk lower && walk upper)
          | _ => false
      | .call name args _ =>
          (SQLite.Scalar.scalarFunctionName name).startsWith "cast_" && args.size == 1 &&
            args.toList.any walk
      | _ => false

/-- expr.c:sqlite3ExprImpliesNonNullRow peels a root NOT NULL test, then
recursively visits the left arms of an AND chain. Its final right arm uses the
ordinary walker, which prunes nested null tests. Preserve that preparation order. -/
def joinScalarNullRejectsVisit (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Nat → Bool → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, peel, expression =>
      let inspect := joinScalarNullRejectsVisit context prepared side fuel
      match expression with
      | .collate arg _ => if peel then inspect true arg else
          joinScalarNullWalk context prepared side (fuel + 1) expression
      | .call name args false =>
          match if peel then SQLite.Probability.input? name args else none with
          | some arg => inspect true arg
          | none => joinScalarNullWalk context prepared side (fuel + 1) expression
      | .binary .and left right => inspect true left || inspect false right
      | .isNull arg true => peel && joinScalarNullWalk context prepared side fuel arg
      | _ => joinScalarNullWalk context prepared side (fuel + 1) expression

def joinScalarNullRejects (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (fuel : Nat) (expression : Expr) : Bool :=
  joinScalarNullRejectsVisit context prepared side fuel true expression

theorem joinScalarNullRejectsVisit_unpeeled_notNull (context : JoinContext)
    (prepared : JoinScalarPrepared) (side : CoreJoin.Side) (fuel : Nat) (arg : Expr) :
    joinScalarNullRejectsVisit context prepared side (fuel + 1) false (.isNull arg true) = false := rfl

/-- Both alternatives must reject a missing source before an OR expression
can establish a non-null source. This is a syntactic optimizer property. -/
theorem joinScalarNullWalk_or (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (fuel : Nat) (left right : Expr) :
    joinScalarNullWalk context prepared side (fuel + 1) (.binary .or left right) =
      (joinScalarNullWalk context prepared side fuel left &&
        joinScalarNullWalk context prepared side fuel right) := rfl

/-- An AND's left branch gets the root null-test rule; its final right branch
uses the unpeeled walk. ON terms are excluded by the caller. -/
theorem joinScalarNullRejects_and (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (fuel : Nat) (left right : Expr) :
    joinScalarNullRejects context prepared side (fuel + 1) (.binary .and left right) =
      (joinScalarNullRejects context prepared side fuel left ||
        joinScalarNullRejectsVisit context prepared side fuel false right) := rfl

def joinScalarProbesRowid (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      let inspect := joinScalarProbesRowid context prepared side fuel
      match expression with
      | .collate arg _ => inspect arg
      | .binary .and left right => inspect left || inspect right
      | .binary .eq left right =>
          let other := if side == .left then CoreJoin.Side.right else .left
          let schema := if side == .left then context.leftSchema else context.rightSchema
          let probes := fun column value =>
            (joinScalarReference context prepared column).any (fun ref => ref.side == side && ref.column == schema.primaryKey) &&
              joinScalarOnlySide context prepared other value
          probes left right || probes right left
      | _ => false

/-- An equality lookup on a non-rowid inner column can use a transient index.
Its rowid suffix is not treated as an ordered table scan by SQLite's planner. -/
def joinScalarAutomaticProbe (context : JoinContext) (prepared : JoinScalarPrepared) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      let inspect := joinScalarAutomaticProbe context prepared fuel
      match expression with
      | .collate arg _ => inspect arg
      | .binary .and left right => inspect left || inspect right
      | .binary .eq left right =>
          let probes := fun column value =>
            (joinScalarReference context prepared column).any (fun ref =>
              ref.side == .right && ref.column != context.rightSchema.primaryKey) &&
              joinScalarOnlySide context prepared .left value
          probes left right || probes right left
      | _ => false

/-- Only WHERE can remove an outer side. A condition that admits a missing
source leaves that side's unmatched-row bookkeeping in place. -/
def joinScalarReducedSource (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) : TableRef :=
  { source with
    leftJoin := source.leftJoin && !prepared.select.where_.any
      (fun expr => joinScalarNullRejects context prepared .right expr.height expr)
    rightJoin := source.rightJoin && !prepared.select.where_.any
      (fun expr => joinScalarNullRejects context prepared .left expr.height expr) }

theorem joinScalarReducedSource_no_new_outer (context : JoinContext)
    (prepared : JoinScalarPrepared) (source : TableRef) :
    ((joinScalarReducedSource context prepared source).leftJoin = true → source.leftJoin = true) ∧
    ((joinScalarReducedSource context prepared source).rightJoin = true → source.rightJoin = true) := by
  constructor <;> intro kept <;>
    simp only [joinScalarReducedSource, Bool.and_eq_true] at kept <;> exact kept.1

/-- Both the physical rowid and declared NOT NULL payload columns carry
non-null metadata before outer-row extension. -/
def joinScalarColumnNotNull (context : JoinContext) (ref : CoreJoin.ColumnRef) : Bool :=
  let schema := if ref.side == .left then context.leftSchema else context.rightSchema
  ref.column == schema.primaryKey || (schema.columns[ref.column]?).any (·.notNull)

/-- Original outer-source nullability overrides a column's declaration while
expressions are prepared, even if a later WHERE condition reduces the join. -/
def joinScalarOriginallyNullable (context : JoinContext) (prepared : JoinScalarPrepared)
    (ref : CoreJoin.ColumnRef) : Bool :=
  (if ref.side == .left then prepared.nullableLeft else prepared.nullableRight) ||
    !joinScalarColumnNotNull context ref

theorem joinScalarOriginallyNullable_outer (context : JoinContext) (prepared : JoinScalarPrepared)
    (ref : CoreJoin.ColumnRef)
    (outer : (if ref.side == .left then prepared.nullableLeft else prepared.nullableRight) = true) :
    joinScalarOriginallyNullable context prepared ref = true := by
  unfold joinScalarOriginallyNullable
  rw [outer]
  simp

/-- A present source row preserves its non-null column constraints. SQLite
can eliminate a conjunct asking such a column to be NULL before either cursor.
An outer side that may be absent does not provide this fact. -/
def joinScalarKnownEmpty (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) : Bool :=
  (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).any fun term =>
    match SQLite.ExprCollation.strip term with
    | .isNull argument false => (joinScalarReference context prepared argument).any fun ref =>
        joinScalarColumnNotNull context ref &&
          (if ref.side == .left then !source.rightJoin else !source.leftJoin)
    | _ => false

/-- A selected cursor constraint retains the original comparison operands so
lookup filtering uses the same affinity and collation as its SQL condition. -/
structure JoinSearchKey where
  column : Expr
  value : Expr
  operation : BinaryOp := .eq
  originalOperands : Option (Expr × Expr) := none

inductive JoinSearchAccess where
  | scan
  | point (key : JoinSearchKey)
  | membership (column : Expr) (values : List Expr)
  | range (start finish : Option JoinSearchKey)
  | automatic (keys : List JoinSearchKey)

/-- Turning a comparison into an indexed-side constraint may swap its
operands. Collation precedence belongs to the original SQL comparison. -/
def JoinSearchKey.collation? (key : JoinSearchKey) : Option SQLite.Collation.Kind :=
  match key.originalOperands with
  | some (left,right) => SQLite.ExprCollation.binaryKind? left right
  | none => SQLite.ExprCollation.binaryKind? key.column key.value

theorem JoinSearchKey.collation_original (key : JoinSearchKey) (left right : Expr)
    (original : key.originalOperands = some (left,right)) :
    key.collation? = SQLite.ExprCollation.binaryKind? left right := by
  simp [JoinSearchKey.collation?, original]

structure JoinFixedColumn where
  index : Nat
  origin : Nat
  expression : Expr
  affinity : SQLite.Affinity

/-- A point seek or a one-element constant IN loop visits at most one row. -/
def JoinSearchAccess.singleton : JoinSearchAccess → Bool
  | .point _ | .membership _ [_] => true
  | _ => false

structure JoinSearchPlan where
  access : JoinSearchAccess := .scan
  early : List Expr := []
  fixed : List JoinFixedColumn := []
  innerWhere : List Expr := []

structure JoinSearchResult where
  rows : List (Core.Row × Nat)
  halt : Bool := false

def joinSearchOpposite : CoreJoin.Side → CoreJoin.Side
  | .left => .right
  | .right => .left

def joinSearchSwap : BinaryOp → BinaryOp
  | .lt => .gt | .le => .ge | .gt => .lt | .ge => .le | op => op

def joinSearchKey? (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (expression : Expr) : Option JoinSearchKey := do
  let .binary operation left right := SQLite.ExprCollation.strip expression | none
  unless [.eq, .is, .lt, .le, .gt, .ge].contains operation do none
  if operation == .is && (SQLite.Scalar.isTruthKeyword? right).isSome then none
  let candidate := fun column value operation => do
    let ref ← joinScalarReference context prepared column
    unless ref.side == side && joinScalarOnlySide context prepared (joinSearchOpposite side) value do none
    return ({ column, value, operation, originalOperands := some (left,right) } : JoinSearchKey)
  candidate left right operation <|> candidate right left (joinSearchSwap operation)

/-- whereexpr.c keeps an indexed original left operand in place. When both
operands are columns, the swapped constraint is appended as a virtual term.
The expression analyzer visits original terms from right to left. -/
def joinSearchKeyOrder (keys : List (Bool × JoinSearchKey)) : List JoinSearchKey :=
  ((keys.filter (fun item => !item.1)) ++ (keys.filter Prod.fst).reverse).map Prod.snd

theorem joinSearchKeyOrder_perm (keys : List (Bool × JoinSearchKey)) :
    (joinSearchKeyOrder keys).Perm (keys.map Prod.snd) := by
  have partition : (keys.filter (fun item => !item.1) ++ keys.filter Prod.fst).Perm keys := by
    simpa only [Bool.not_not] using List.filter_append_perm (fun item : Bool × JoinSearchKey => !item.1) keys
  exact ((List.reverse_perm (keys.filter Prod.fst)).append_left
    (keys.filter (fun item => !item.1)) |>.trans partition).map Prod.snd

def joinSearchKeys (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (terms : List Expr) : List JoinSearchKey :=
  joinSearchKeyOrder ((joinSearchRangeTerms terms).filterMap fun term => do
    let key ← joinSearchKey? context prepared side term
    let virtual := match SQLite.ExprCollation.strip term with
      | .binary _ left right => (joinScalarReference context prepared left).isSome &&
          (joinScalarReference context prepared right).any (fun ref => ref.side == side)
      | _ => false
    return (virtual, key))

/-- where.c:sqlite3WhereFindTerm prefers a constant RHS, then the first usable
constraint in SQL term order. This selection does not inspect row values. -/
def joinSearchChoose (prepared : JoinScalarPrepared) (keys : List JoinSearchKey) : Option JoinSearchKey :=
  keys.find? (fun key => prepared.context.constantExpression key.value) <|> keys.head?

def joinSearchIndexAffinity (prepared : JoinScalarPrepared) (key : JoinSearchKey) : Bool :=
  let affinity := (prepared.context.affinity key.column).getD .blob
  let comparison := SQLite.Scalar.comparisonAffinity (prepared.context.affinity key.column)
    (prepared.context.affinity key.value)
  comparison == .blob || (comparison == .text && affinity == .text) ||
    (SQLite.Scalar.numericAffinity comparison && SQLite.Scalar.numericAffinity affinity)

/-- USING/NATURAL equality can drive an automatic index only when its
comparison affinity is compatible with the indexed side. Rowid equalities
are handled as point probes, independently of this flag. -/
def joinUsingAutomaticProbe (context : JoinContext) (_prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) : Bool := joinUsingIndexEligible context side

def joinSearchConstantRoot (context : JoinContext) (prepared : JoinScalarPrepared)
    (side : CoreJoin.Side) (on : Option Expr) : Option JoinSearchAccess := do
  let schema := if side == .left then context.leftSchema else context.rightSchema
  let terms := on.map SQLite.Scalar.conditionTerms |>.getD []
  let point := (terms.filterMap (joinSearchKey? context prepared side)).find? fun key =>
    [.eq, .is].contains key.operation && prepared.context.constantExpression key.value &&
      (joinScalarReference context prepared key.column).any (fun ref => ref.column == schema.primaryKey)
  if let some key := point then return .point key
  terms.findSome? fun term => do
    let .inList column values false _ := SQLite.ExprCollation.strip term | none
    let ref ← joinScalarReference context prepared column
    unless ref.side == side && ref.column == schema.primaryKey && values.all prepared.context.constantExpression do none
    return .membership column values.toList

def joinSearchSingletonKey : JoinSearchAccess → Option JoinSearchKey
  | .point key => some key
  | .membership column [value] => some { column, value := .unary .plus value }
  | _ => none

/-- Constant-column preparation retains column affinity. EQ needs a bare
column, a constant RHS without expression affinity and BINARY comparison.
A one-element IN supplies the affinity-free RHS used by scalar preparation. -/
def joinSearchFixesColumn (prepared : JoinScalarPrepared) (key : JoinSearchKey) : Bool :=
  key.operation == .eq && prepared.context.constantExpression key.value &&
    (prepared.context.affinity key.value).isNone &&
    key.collation? == some .binary &&
    (match key.column with | .column .. => true | _ => false)

end CoreSQL

end SQLeanite
