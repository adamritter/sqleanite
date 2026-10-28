import SQLeanite.CoreSQL.JoinSearchPlan

namespace SQLeanite
namespace CoreSQL

def joinStreamPrepared (state : Core.State) (select : Select) : Except String JoinReadReport := do
  let (leftSource, originalRight) ← match select.sources.toList with
    | [left, right] => pure (left, right)
    | _ => unsupported "joined expression source count"
  unless leftSource.schema.isNone && leftSource.functionArgs.isNone && leftSource.subquerySql.isNone && originalRight.schema.isNone && originalRight.functionArgs.isNone && originalRight.subquerySql.isNone && leftSource.joinOn.isNone do
    unsupported "joined expression sources"
  let leftName := resolveTableName state leftSource.name
  let rightName := resolveTableName state originalRight.name
  let some left := state.database.findTable? leftName | throw s!"no such table: {leftSource.name}"
  let some right := state.database.findTable? rightName | throw s!"no such table: {originalRight.name}"
  let context ← joinContext leftSource originalRight leftName rightName left.schema right.schema
  unless context.leftName != context.rightName do throw "ambiguous join source names"
  let prepared ← joinScalarPrepare context select originalRight state.catalog.storedTexts
  let source := joinScalarReducedSource context prepared originalRight
  let terms ← CoreOrder.resolve prepared.context prepared.select.columns.toList prepared.select.orderBy.toList
  let aggregate := !prepared.select.groupBy.isEmpty || prepared.select.columns.any (fun c => CoreAggregate.containsAggregate c.expr)
  let (on, _) := match originalRight.joinOn with
    | none => (none, none)
    | some expression => CoreOrder.resolveJoinOnAliases (joinHasColumn context) select.columns.toList expression
  let on ← on.mapM (joinScalarBind context)
  let traversal := joinScalarTraversal context prepared source terms on
  if !prepared.select.groupBy.isEmpty || (!aggregate && !terms.isEmpty && !traversal.ordered) then
    return ← joinScalarMaterializedReport state select
  if aggregate then
    return ← joinAggregateStreamResult context prepared source traversal on left.rows right.rows
  let ctx := prepared.context
  unless prepared.select.having.isNone do unsupported "HAVING requires an aggregate"
  let expressions ← ctx.projection prepared.select.columns.toList
  if prepared.select.distinct then CoreExpr.validateDistinct expressions
  let _ ← prepared.select.where_.mapM ctx.validate
  let _ ← terms.mapM (CoreOrder.validateTerm ctx)
  let width := expressions.length
  if select.limit == some 0 || joinScalarKnownEmpty context prepared source then return { width }
  unless ← joinFixedConstantMatches context prepared source on do return { width }
  let right := if traversal.reverseRight then right.rows.reverse else right.rows
  let left := if traversal.reverseLeft then left.rows.reverse else left.rows
  let outerSide := if traversal.exchanged then CoreJoin.Side.right else .left
  let early := if source.rightJoin then [] else
    (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
      (fun term => joinScalarOnlySide context prepared outerSide term && !ctx.constantExpression term)
  let plan := joinSearchPlan context prepared source traversal on
  let early := early ++ plan.early
  unless source.leftJoin || source.rightJoin do
    unless ← ctx.constantMatches on do return { width }
  let outer := if traversal.exchanged then right else left
  let inner := if traversal.exchanged then left else right
  let outer ← match traversal.root with
    | none => pure outer
    | some access => do
        let empty := CoreJoin.nullRow (if traversal.exchanged then context.leftSchema.columns.length else context.rightSchema.columns.length)
        pure ((← joinSearchCandidates context prepared source (!traversal.exchanged) empty access outer.zipIdx).rows.map Prod.fst)
  let inner := inner.zipIdx
  let initial : JoinStreamState := { skip := select.offset, remaining := select.limit }
  let result := joinStreamLeft context prepared source expressions early traversal.exchanged inner plan outer initial []
  return { result := { rows := result.reversed.reverse }, width, error := result.error }

/-- Preparation failures have no emitted prefix. Runtime failures in a streamed
scan retain exactly the rows produced before the failing step. -/
def joinScalarReadReport (state : Core.State) (select : Select) : JoinReadReport :=
  match joinStreamPrepared state select with
  | .ok report => report
  | .error message => { error := some message }

def joinScalarResult (state : Core.State) (select : Select) : Except String (Core.Result × Nat) :=
  (joinScalarReadReport state select).toExcept

theorem joinStreamStep_stopped (context : JoinContext) (prepared : JoinScalarPrepared)
    (expressions : List Expr) (state : JoinStreamState) (row : CoreJoin.JoinedRow)
    (stopped : state.stopped = true) :
    joinStreamStep context prepared expressions state row = state := by
  simp [joinStreamStep, stopped]

theorem joinStreamRight_stopped (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (expressions : List Expr) (exchanged : Bool) (outer : Core.Row)
    (rows : List (Core.Row × Nat)) (state : JoinStreamState) (found : Bool) (matched : List Nat)
    (stopped : state.stopped = true) :
    joinStreamRight context prepared source plan expressions exchanged outer rows state found matched =
      (state, found, matched) := by
  cases rows <;> simp [joinStreamRight, stopped]

theorem joinStreamSuffix_stopped (context : JoinContext) (prepared : JoinScalarPrepared)
    (expressions : List Expr) (rows : List Core.Row) (state : JoinStreamState)
    (stopped : state.stopped = true) :
    joinStreamSuffix context prepared expressions rows state = state := by
  cases rows <;> simp [joinStreamSuffix, stopped]

theorem joinStreamLeft_stopped (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (expressions early : List Expr) (exchanged : Bool)
    (inner : List (Core.Row × Nat)) (plan : JoinSearchPlan) (outer : List Core.Row) (state : JoinStreamState)
    (matched : List Nat) (stopped : state.stopped = true) :
    joinStreamLeft context prepared source expressions early exchanged inner plan outer state matched = state := by
  cases outer <;> simp [joinStreamLeft, stopped, joinStreamSuffix_stopped context prepared expressions _ state stopped]

def executeJoinScalar (state : Core.State) (select : Select) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> joinScalarResult state select

theorem executeJoinScalar_preserves_state {state : Core.State} {select : Select}
    {result : SelectExecution} (success : executeJoinScalar state select = .ok result) :
    result.state = state := by
  unfold executeJoinScalar at success
  cases executed : joinScalarResult state select with
  | error message => simp [executed, Functor.map, Except.map] at success
  | ok output =>
      simp [executed, Functor.map, Except.map] at success
      cases success
      rfl

/-- Extend only two-source queries. Successful existing execution remains
authoritative, and all other source shapes keep their original error behavior. -/
def executeSelectBaseComplete (state : Core.State) (select : Select) : Except String SelectExecution :=
  if select.sources.size != 2 then executeSelectBase state select
  else match executeSelectBase state select with
    | .ok result => .ok result
    | .error _ => executeJoinScalar state select

theorem executeSelectBaseComplete_existing (state : Core.State) (select : Select)
    (result : SelectExecution) (success : executeSelectBase state select = .ok result) :
    executeSelectBaseComplete state select = .ok result := by
  simp [executeSelectBaseComplete, success]

theorem joinScalarRowsM_pure (context : JoinContext) (prepared : JoinScalarPrepared) (source : TableRef)
    (left right : List Core.Row) (pureOn : prepared.onExpression = none) :
    joinScalarRowsM context prepared source left right =
      .ok (joinScalarRows context source prepared.on left right) := by
  simp [joinScalarRowsM, pureOn, pure, Except.pure]

theorem joinScalarRowsM_exchange_inner (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (left right : List Core.Row)
    (noLeft : source.leftJoin = false) (noRight : source.rightJoin = false) :
    joinScalarRowsM context prepared source left right true =
      (right.flatMap (fun r => left.map (fun l => (l, r)))).filterM
        (joinScalarMatches context prepared false) := by
  simp [joinScalarRowsM, noLeft, noRight]

/-- Bind identifiers and expand stars before resolving each output column's
explicit or declared collation. Joined stars expand with BINARY metadata;
wrapped atoms retain their original explicit and inherited collation. -/
def baseResultCollations (state : Core.State) (select : Select) (wrappedValues : Bool := false) :
    Except String (List (Option String)) := do
  if let some rows := select.valueRows then
    return SQLite.Values.collations rows.toList wrappedValues
  match select.sources.toList with
  | [] => return select.columns.toList.map (fun column => SQLite.ExprCollation.effectiveName column.expr)
  | [source] =>
      let some stored := state.database.findTable? (resolveTableName state source.name) | throw s!"no such table: {source.name}"
      let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name, storedTexts := state.catalog.storedTexts }
      let expanded ← CoreOrder.expandResults ctx select.columns.toList
      return expanded.map (fun column => SQLite.ExprCollation.effectiveName (ctx.bindNames column.expr))
  | [leftSource, rightSource] =>
      let some left := state.database.findTable? (resolveTableName state leftSource.name) | throw s!"no such table: {leftSource.name}"
      let some right := state.database.findTable? (resolveTableName state rightSource.name) | throw s!"no such table: {rightSource.name}"
      let leftName := resolveTableName state leftSource.name
      let rightName := resolveTableName state rightSource.name
      let context ← joinContext leftSource rightSource leftName rightName left.schema right.schema
      match joinAliasQuery { select with orderBy := #[], offset := 0 }
          leftName rightName left.schema right.schema left.rows right.rows with
      | .ok _ => return (← joinWrappedColumns context select.columns.toList).2
      | .error _ =>
          let prepared ← joinScalarPrepare context { select with orderBy := #[], offset := 0 } rightSource state.catalog.storedTexts
          let _ ← joinScalarRun context { prepared with select := { prepared.select with limit := some 0 } } []
          return prepared.select.columns.toList.map (fun column => SQLite.ExprCollation.effectiveName column.expr)
  | _ => unsupported "compound source shape"

/-- multiSelectCollSeq takes the first arm that supplies a collation for each
output position. An unused later unknown name must not replace an earlier one. -/
def resultCollationsFuel : Nat → Core.State → Select → Except String (List (Option String))
  | 0, _, _ => .error "compound collation depth exhausted"
  | fuel + 1, state, select => do
      let first ← baseResultCollations state select
      select.compounds.toList.foldlM (fun current (operation, arm) => do
        let next ← if arm.valueRows.isSome then baseResultCollations state arm true
          else resultCollationsFuel fuel state arm
        unless current.length == next.length do
          throw (CoreCompound.widthError operation)
        return current.zipWith (fun left right => left.orElse fun _ => right) next) first

/-- Expand source columns for compound ORDER BY alias/expression matching. -/
def compoundTailArm (state : Core.State) (select : Select) : Except String CoreCompoundTail.Arm := do
  match select.sources.toList with
  | [] =>
      return { columns := select.columns.toList, context := some {
        schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" } }
  | [source] =>
      let some stored := state.database.findTable? (resolveTableName state source.name) | throw s!"no such table: {source.name}"
      let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name, storedTexts := state.catalog.storedTexts }
      return { columns := ← CoreOrder.expandResults ctx select.columns.toList, context := some ctx }
  | [leftSource, rightSource] =>
      let leftName := resolveTableName state leftSource.name
      let rightName := resolveTableName state rightSource.name
      let some left := state.database.findTable? leftName | throw s!"no such table: {leftSource.name}"
      let some right := state.database.findTable? rightName | throw s!"no such table: {rightSource.name}"
      let context ← joinContext leftSource rightSource leftName rightName left.schema right.schema
      return {
        columns := ← joinCompoundColumns context select.columns.toList
        context := none
        bindExpression := some (fun expression => joinCompoundBind context
          (CoreOrder.resolveAliasesWith (joinHasColumn context) select.columns.toList expression)) }
  | _ => unsupported "compound source shape"

def compoundValuesArms (rows : Array (Array Expr)) (wrapped : Bool) : List CoreCompoundTail.Arm :=
  (SQLite.Values.projections rows.toList wrapped).map fun (row, source) =>
    { columns := row.toList.zipIdx.map (fun (expression, index) =>
        if source then { expr := .column none s!"column{index + 1}", alias := some s!"column{index + 1}" }
        else { expr := expression }), context := none }

def compoundTailArmsFuel : Nat → Core.State → Select → Bool → Except String (List CoreCompoundTail.Arm)
  | 0, _, _, _ => .error "compound ORDER BY depth exhausted"
  | fuel + 1, state, select, wrapped => do
      let first ← if let some rows := select.valueRows then pure (compoundValuesArms rows wrapped)
        else (fun arm => [arm]) <$> compoundTailArm state select
      let others ← select.compounds.toList.mapM (fun arm => compoundTailArmsFuel fuel state arm.2 true)
      return first ++ others.flatten

/-- Leaf execution keeps ORDER BY's top-N evaluation discipline. Aggregates,
groups and bounded joins already produce their output rows in their own
executor, so result-slot ordering is applied to those rows. The second return
value counts rows consumed by OFFSET for concatenated UNION ALL arms. -/
def compoundTailLeaf (run : Core.State → Select → Except String SelectExecution)
    (state : Core.State) (select : Select) (terms : List CoreCompoundTail.Term)
    (offset : Nat) (limit : Option Nat) (wrappedValues : Bool := false) : Except String (List (List Core.Value) × Nat) := do
  if let some rows := select.valueRows then
    if terms.isEmpty then
      if wrappedValues && rows.size > 1 then
        let result ← run state { select with orderBy := #[], offset := 0, limit := limit.map (· + offset) }
        return (result.result.rows.drop offset, min offset rows.size)
      let result ← run state { select with orderBy := #[], offset, limit }
      return (result.result.rows, min offset rows.size)
    else
      let result ← run state { select with orderBy := #[], offset := 0, limit := none }
      let sorted := CoreCompoundTail.sort terms result.result.rows
      return (CoreCompoundTail.window offset limit sorted, min offset sorted.length)
  let aggregate := select.columns.any (fun c => CoreAggregate.containsAggregate c.expr)
  if !terms.isEmpty then
    if !aggregate && select.groupBy.isEmpty && select.sources.size ≤ 1 then
      let result ← run state { select with orderBy := (terms.map CoreCompoundTail.orderTerm).toArray, offset, limit }
      return (result.result.rows, 0)
    let result ← run state { select with orderBy := #[], offset := 0, limit := none }
    let sorted := CoreCompoundTail.sort terms result.result.rows
    return (CoreCompoundTail.window offset limit sorted, min offset sorted.length)
  if offset > 0 && !select.distinct && select.groupBy.isEmpty && !aggregate && select.sources.size ≤ 1 then
    -- Count skipped source rows without evaluating their output expressions.
    -- Supported scalar functions are deterministic; validation of the original
    -- projections has already happened before any leaf executes.
    let skipped ← run state { select with columns := #[{ expr := .literal (.integer 1) }], orderBy := #[], offset := 0, limit := some offset }
    let count := skipped.result.rows.length
    if count < offset then return ([], count)
    let result ← run state { select with orderBy := #[], offset, limit }
    return (result.result.rows, count)
  if aggregate && select.groupBy.isEmpty then
    let result ← run state { select with orderBy := #[], offset, limit }
    return (result.result.rows, min offset 1)
  let result ← run state { select with orderBy := #[], offset := 0, limit := limit.map (· + offset) }
  return (CoreCompoundTail.window offset limit result.result.rows, min offset result.result.rows.length)

/-- Reverse-arm recursion represents SQL's left-associated compound tree.
Only UNION ALL propagates a finite bound into its input arms. Set operations
complete the merge key with the remaining output columns. -/
def compoundTailPlan (run : Core.State → Select → Except String SelectExecution)
    (state : Core.State) (kinds : List SQLite.Collation.Kind) (base : Select) :
    List (CompoundOp × Select) → List CoreCompoundTail.Term → Nat → Option Nat →
      Except String (List (List Core.Value) × Nat)
  | [], terms, offset, limit => compoundTailLeaf run state base terms offset limit
  | (operation, arm) :: prior, terms, offset, limit => do
      if operation == .unionAll && terms.isEmpty then
        let (left, skipped) ← compoundTailPlan run state kinds base prior [] offset limit
        let remaining := limit.map (· - left.length)
        if remaining == some 0 then return (left, skipped)
        let (right, moreSkipped) ← compoundTailLeaf run state arm [] (offset - skipped) remaining true
        return (left ++ right, skipped + moreSkipped)
      let ordering := if operation == .unionAll then terms else CoreCompoundTail.complete kinds terms
      let capacity := if operation == .unionAll then limit.map (· + offset) else none
      let (left, _) ← compoundTailPlan run state kinds base prior ordering 0 capacity
      if left.isEmpty && (operation == .intersect || operation == .except) then return ([], 0)
      let (right, _) ← compoundTailLeaf run state arm ordering 0 capacity true
      let rows := CoreCompoundTail.merge kinds operation ordering left right
      return (CoreCompoundTail.window offset limit rows, min offset rows.length)

def compoundTailResult (run : Core.State → Select → Except String SelectExecution)
    (state : Core.State) (select : Select) (encoding : Nat := 1) : Except String (Core.Result × Nat) := do
  let names ← resultCollationsFuel select.compoundHeight state select
  let usesSets := select.compounds.any (fun arm => arm.1 != .unionAll)
  let kinds ← if usesSets then names.mapM (fun name => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName name))
    else pure (names.map (fun name => (SQLite.ExprCollation.ofName name).getD .binary))
  let kinds := kinds.map (SQLite.Collation.forEncoding encoding)
  let bindings ← compoundTailArmsFuel select.compoundHeight state select false
  let terms ← select.orderBy.toList.mapM (CoreCompoundTail.resolve bindings names)
  let terms := terms.map fun term => { term with specification := { term.specification with
    collation := SQLite.Collation.forEncoding encoding term.specification.collation } }
  let base := { select with compounds := #[], orderBy := #[], limit := none, offset := 0 }
  for (operation, arm) in ((select.compounds[0]?.map Prod.fst).getD .unionAll, base) :: select.compounds.toList do
    let validated ← run state { arm with orderBy := #[], limit := some 0, offset := 0 }
    unless validated.width == names.length do
      throw (CoreCompound.widthError operation)
  if select.limit == some 0 then return ({}, names.length)
  let externalSort := usesSets && select.orderBy.any (fun term => (SQLite.ExprCollation.name term.expr).isSome)
  let rows ← if externalSort then do
      let (rows, _) ← compoundTailPlan run state kinds base select.compounds.toList.reverse [] 0 none
      pure (CoreCompoundTail.window select.offset select.limit (CoreCompoundTail.sort terms rows))
    else do
      let (rows, _) ← compoundTailPlan run state kinds base select.compounds.toList.reverse terms select.offset select.limit
      pure rows
  return ({ rows }, names.length)

def executeCompoundTail (run : Core.State → Select → Except String SelectExecution)
    (state : Core.State) (select : Select) (encoding : Nat := 1) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> compoundTailResult run state select encoding

theorem executeCompoundTail_preserves_state
    {run : Core.State → Select → Except String SelectExecution}
    {state : Core.State} {select : Select} {execution : SelectExecution}
    (success : executeCompoundTail run state select = .ok execution) : execution.state = state := by
  unfold executeCompoundTail at success
  cases result : compoundTailResult run state select with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

def executeSelectFuel : Nat → Core.State → Select → Except String SelectExecution
  | 0, _, _ => .error "compound SELECT exceeds its verified recursion bound"
  | fuel + 1, state, select => do
      if !(select.compounds.isEmpty ||
          (select.orderBy.isEmpty && select.limit.isNone && select.offset = 0)) then
        return ← executeCompoundTail (executeSelectFuel fuel) state select
      if requiresCompoundCollation select then
        let names ← resultCollationsFuel select.compoundHeight state select
        let kinds ← if select.compounds.any (fun arm => arm.1 != .unionAll) then
            names.mapM (fun name => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName name))
          else pure []
        let base ← executeSelectBaseComplete state { select with compounds := #[] }
        let rec executeCollatedArms (current : SelectExecution) :
            List (CompoundOp × Select) → Except String SelectExecution
          | [] => .ok current
          | (operation, arm) :: arms => do
              let next ← executeSelectFuel fuel current.state arm
              unless current.width == next.width do
                throw (CoreCompound.widthError operation)
              let combined : SelectExecution := {
                state := next.state
                result := { rows := CoreCompound.combineCollated kinds operation current.result.rows next.result.rows }
                width := current.width }
              executeCollatedArms combined arms
        return ← executeCollatedArms base select.compounds.toList
      let base ← executeSelectBaseComplete state { select with compounds := #[] }
      let rec executeArms (current : SelectExecution) :
          List (CompoundOp × Select) → Except String SelectExecution
        | [] => .ok current
        | (operation, arm) :: arms => do
            let next ← executeSelectFuel fuel current.state arm
            unless current.width = next.width do
              throw (CoreCompound.widthError operation)
            let combined : SelectExecution := {
              state := next.state
              result := { rows := (combineRows
                (CoreOptimizerBridge.optimizeCompoundOp operation)
                current.result.rows next.result.rows) }
              width := current.width }
            executeArms combined arms
      executeArms base select.compounds.toList

def executeSelect (state : Core.State) (select : Select) :
    Except String SelectExecution :=
  executeSelectFuel select.compoundHeight state select


/-- The source-aware connection supplies its actual default encoding.
The original source-free executeSelect and its contracts retain UTF-8 defaults. -/
def executeSelectEncoded (state : Core.State) (select : Select) : Except String SelectExecution :=
  if (state.catalog.current.textEncoding == 2 || state.catalog.current.textEncoding == 3) &&
      !select.compounds.isEmpty then
    executeCompoundTail (executeSelectFuel select.compoundHeight) state select state.catalog.current.textEncoding
  else executeSelect state select


theorem executeCompoundTail_encoding_preserves_state
    {run : Core.State → Select → Except String SelectExecution}
    {state : Core.State} {select : Select} {execution : SelectExecution} (encoding : Nat)
    (success : executeCompoundTail run state select encoding = .ok execution) : execution.state = state := by
  unfold executeCompoundTail at success
  cases result : compoundTailResult run state select encoding with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

/-- Read-only observation retains a typed row prefix separately from the
ordinary success/error result. It cannot turn a failure into a successful read. -/
structure ObservedSelect where
  execution : SelectExecution
  error : Option String := none

def ObservedSelect.toExcept (report : ObservedSelect) : Except String SelectExecution :=
  match report.error with
  | none => .ok report.execution
  | some message => .error message

def executeSelectBaseObserved (state : Core.State) (select : Select) : ObservedSelect :=
  match executeSelectBase state select with
  | .ok execution => { execution }
  | .error _ =>
      let report := joinScalarReadReport state select
      { execution := ⟨state, report.result, report.width⟩, error := report.error }

theorem executeSelectBaseObserved_refines (state : Core.State) (select : Select)
    (twoSources : select.sources.size = 2) :
    (executeSelectBaseObserved state select).toExcept = executeSelectBaseComplete state select := by
  cases base : executeSelectBase state select with
  | ok execution => simp [executeSelectBaseObserved, ObservedSelect.toExcept,
      executeSelectBaseComplete, twoSources, base]
  | error message =>
      cases failure : (joinScalarReadReport state select).error <;>
        simp [executeSelectBaseObserved, ObservedSelect.toExcept, executeSelectBaseComplete,
          twoSources, base, executeJoinScalar, joinScalarResult, JoinReadReport.toExcept,
          failure, Functor.map, Except.map]

theorem executeSelect_without_compounds (state : Core.State) (select : Select)
    (noCompounds : select.compounds = #[]) :
    executeSelect state select = executeSelectBaseComplete state select := by
  have height : select.compoundHeight = 1 := by
    rw [show select.compoundHeight = selectCompoundListHeight select.compounds.toList + 1 by
      cases select
      rfl, noCompounds]
    rfl
  have cleared : { select with compounds := #[] } = select := by
    cases select
    simp_all
  cases base : executeSelectBaseComplete state select <;>
    simp [executeSelect, height, executeSelectFuel, requiresCompoundCollation, noCompounds,
      cleared, base, executeSelectFuel.executeArms, bind, Except.bind]

/-- Add observation only to a complete two-source leaf. Compound operators keep
owning their materialization and result publication. -/
def observeJoinedSelect? (state : Core.State) (select : Select) : Option ObservedSelect :=
  if select.sources.size = 2 ∧ select.compounds = #[] then
    some (executeSelectBaseObserved state select)
  else none

theorem observeJoinedSelect_refines (state : Core.State) (select : Select)
    (report : ObservedSelect) (observed : observeJoinedSelect? state select = some report) :
    report.toExcept = executeSelect state select := by
  unfold observeJoinedSelect? at observed
  split at observed
  next supported =>
    cases Option.some.inj observed
    rw [executeSelectBaseObserved_refines state select supported.1,
      executeSelect_without_compounds state select supported.2]
  next unsupported => simp at observed

/-- Prepare a single-table read using the same bound sources as execution.
Ordered groups retain their emitted prefix; ungrouped aggregates remain atomic. -/
def singleSourceReadPrepared (state : Core.State) (select : Select) : Except String ScalarReadReport := do
  unless select.sources.size == 1 do unsupported "single-source read observation"
  let some source := select.sources[0]? | unsupported "single-source observation source"
  unless source.schema.isNone && source.functionArgs.isNone && source.subquerySql.isNone && source.joinOn.isNone do
    unsupported "single-source observation source"
  let some stored := state.database.findTable? (resolveTableName state source.name) |
    throw s!"no such table: {source.name}"
  if !select.groupBy.isEmpty then
    let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name, storedTexts := state.catalog.storedTexts }
    let (report, width) ← CoreGrouped.observe ctx select (stored.rows.map (·.values))
    return { result := { rows := report.rows }, width, error := report.error }
  unless select.having.isNone &&
      !select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) do
    unsupported "single-source aggregate observation"
  let select ← if selectNamesBound stored.schema source select then pure select else do
    let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name, storedTexts := state.catalog.storedTexts }
    unless select.where_.any (CoreOrder.needsAliases ctx select.columns.toList) do
      if let some message := selectResolutionError stored.schema source select then throw message
      unsupported "unbound SELECT name"
    unless selectNamesBound stored.schema source { select with where_ := none } do
      if let some message := selectResolutionError stored.schema source { select with where_ := none } then throw message
      unsupported "unbound SELECT result or ordering name"
    pure { select with where_ := select.where_.map (CoreOrder.resolveAliases ctx select.columns.toList) }
  filteredSelectReadPrepared state select source stored

def singleSourceReadReport (state : Core.State) (select : Select) : ScalarReadReport :=
  match singleSourceReadPrepared state select with
  | .ok report => report
  | .error message => { error := some message }

end CoreSQL

end SQLeanite
