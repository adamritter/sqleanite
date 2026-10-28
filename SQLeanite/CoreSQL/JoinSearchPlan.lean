import SQLeanite.CoreSQL.JoinSearchRootFixed

namespace SQLeanite
namespace CoreSQL

def joinSearchPlan (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (traversal : JoinScalarTraversal) (on : Option Expr) : JoinSearchPlan := Id.run do
  let side := if traversal.exchanged then CoreJoin.Side.left else .right
  let schema := if side == .left then context.leftSchema else context.rightSchema
  let outer := joinSearchOpposite side
  let terms := on.map SQLite.Scalar.conditionTerms |>.getD []
  let whereRanges := if source.leftJoin || source.rightJoin then [] else
    (joinSearchRangeTerms (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD [])).filterMap fun term => do
      let key ← joinSearchKey? context prepared side term
      unless [.lt, .le, .gt, .ge].contains key.operation do none
      return key
  let keys := whereRanges ++ joinSearchKeys context prepared side terms
  let rootFixed := joinSearchRootFixed context prepared traversal.root on
  let inherited := if source.leftJoin || source.rightJoin || rootFixed ||
      !joinSearchRowidEquality context prepared on then none else do
    let root ← traversal.root
    let key ← joinSearchSingletonKey root
    let column ← joinScalarOperand context (.column ⟨side, schema.primaryKey⟩)
    return key.retarget column
  let keys := inherited.toList ++ keys
  let rowid := fun key => (joinScalarReference context prepared key.column).any (fun ref => ref.column == schema.primaryKey)
  let equals := keys.filter (fun key => rowid key && [.eq, .is].contains key.operation)
  let fixedOuterColumn := fun key => rootFixed &&
    (traversal.root.bind joinSearchSingletonKey).any (fun root =>
      joinScalarReference context prepared key.value == joinScalarReference context prepared root.column)
  let equals := if !source.leftJoin && !source.rightJoin && !source.crossJoin then
      equals.filter (fun key => !fixedOuterColumn key) ++ equals.filter fixedOuterColumn else equals
  -- With a singleton outer source, a dependent point lookup retains the
  -- independent equality as an additional inner filter. CROSS/outer fences
  -- and an inherited transitive seek keep their existing constraint order.
  let dependent := fun key => !prepared.context.constantExpression key.value && !fixedOuterColumn key
  let equals := if !source.leftJoin && !source.rightJoin && !source.crossJoin &&
      traversal.root.any JoinSearchAccess.singleton && inherited.isNone then
      equals.filter dependent ++ equals.filter (fun key => !dependent key) else equals
  let fixed := joinFixedColumns context prepared side source on
  let early := if source.leftJoin || source.rightJoin then [] else
    joinFixedEarly context prepared outer fixed on
  let innerWhere := if source.leftJoin || source.rightJoin then [] else
    (prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
      (fun term => joinScalarOnlySide context prepared side term && !prepared.context.constantExpression term)
  if let some key := equals.head? then
    return { access := .point key, early, fixed, innerWhere }
  let membership := terms.findSome? fun term => do
    let .inList column values false _ := SQLite.ExprCollation.strip term | none
    let ref ← joinScalarReference context prepared column
    unless ref.side == side && ref.column == schema.primaryKey &&
      values.all (joinScalarOnlySide context prepared outer) do none
    return (column, values.toList)
  if let some (column, values) := membership then
    return { access := .membership column values, early, fixed, innerWhere }
  -- With a non-singleton outer cursor, a usable automatic equality index
  -- has the default 20-row estimate, below the default rowid range estimate.
  if !source.rightJoin && !traversal.root.any JoinSearchAccess.singleton then
    let candidates := keys.filter (fun key => !rowid key && [.eq, .is].contains key.operation && joinSearchIndexAffinity prepared key)
    let mut chosen := []
    for key in candidates do
      let ref := joinScalarReference context prepared key.column
      unless chosen.any (fun old => joinScalarReference context prepared old.column == ref) do
        chosen := chosen ++ [key]
    unless chosen.isEmpty do return { access := .automatic chosen, early, fixed, innerWhere }
  let whereTerms := if source.leftJoin || source.rightJoin then [] else
    prepared.select.where_.map SQLite.Scalar.conditionTerms |>.getD []
  let pair := joinSearchBetweenPair context prepared side (whereTerms ++ terms)
  let lower := (pair.map Prod.fst).orElse (fun _ =>
    joinSearchChoose prepared (keys.filter (fun key => rowid key && [.gt, .ge].contains key.operation)))
  let upper := (pair.map Prod.snd).orElse (fun _ =>
    joinSearchChoose prepared (keys.filter (fun key => rowid key && [.lt, .le].contains key.operation)))
  if lower.isSome || upper.isSome then
    let reverse := if traversal.exchanged then traversal.reverseLeft else traversal.reverseRight
    return { access := .range (if reverse then upper else lower) (if reverse then lower else upper), early, fixed, innerWhere }
  return { early, fixed, innerWhere }

def joinSearchPair (context : JoinContext) (exchanged : Bool) (outer : Core.Row)
    (inner : Option Core.Row := none) : CoreJoin.JoinedRow :=
  if exchanged then (inner.getD (CoreJoin.nullRow context.leftSchema.columns.length), outer)
  else (outer, inner.getD (CoreJoin.nullRow context.rightSchema.columns.length))

def joinSearchFilter (context : JoinContext) (prepared : JoinScalarPrepared)
    (exchanged : Bool) (outer : Core.Row) (key : JoinSearchKey) (value : Value)
    (rows : List (Core.Row × Nat)) : Except String (List (Core.Row × Nat)) :=
  rows.filterM fun (row, _) => do
    let input := CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer row)
    let column ← prepared.context.eval input key.column
    let kind ← SQLite.ExprCollation.require key.collation?
    let affinity := SQLite.Scalar.comparisonAffinity (prepared.context.affinity key.column)
      (prepared.context.affinity key.value)
    return SQLite.Numeric.truth (SQLite.Scalar.comparisonWith kind key.operation
      (SQLite.Scalar.applyComparisonAffinity affinity column)
      (SQLite.Scalar.applyComparisonAffinity affinity value)) == .true

/-- Cursor initialization happens before its first candidate pair. A rowid
seek evaluates its key even on an empty table. Rewind and automatic-index
construction can instead finish an inner join before evaluating that key. -/
def joinSearchCandidates (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (exchanged : Bool) (outer : Core.Row) (access : JoinSearchAccess)
    (inner : List (Core.Row × Nat)) : Except String JoinSearchResult := do
  let input := CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer)
  let evaluate := prepared.context.eval input
  let filter := joinSearchFilter context prepared exchanged outer
  match access with
  | .scan => return { rows := inner, halt := inner.isEmpty && !source.leftJoin }
  | .point key =>
      let value ← evaluate key.value
      return { rows := ← filter key value inner }
  | .membership column expressions =>
      let values ← expressions.mapM evaluate
      let rows ← inner.filterM fun (row, _) => do
        let rowInput := CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer row)
        let value ← prepared.context.eval rowInput column
        return values.any (fun key => SQLite.Numeric.truth (SQLite.Scalar.comparison .eq
          (SQLite.Scalar.applyComparisonAffinity .numeric value)
          (SQLite.Scalar.applyComparisonAffinity .numeric key)) == .true)
      return { rows }
  | .range start finish =>
      if start.isNone && inner.isEmpty then return { rows := [], halt := !source.leftJoin }
      let rows ← match start with
        | none => pure inner
        | some key => do filter key (← evaluate key.value) inner
      if rows.isEmpty then return { rows := [] }
      let rows ← match finish with
        | none => pure rows
        | some key => do filter key (← evaluate key.value) rows
      return { rows }
  | .automatic keys =>
      if inner.isEmpty && !source.leftJoin then return { rows := [], halt := true }
      let mut evaluated := []
      for key in keys do
        let value ← evaluate key.value
        if value == .null && key.operation == .eq then return { rows := [] }
        evaluated := evaluated ++ [(key, value)]
      let rows ← evaluated.foldlM (fun rows (key, value) => filter key value rows) inner
      return { rows }

/-- Failure to compute a selected point key propagates before inspecting any
candidate row, including when the physical input is empty. -/
theorem joinSearchCandidates_point_error (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (exchanged : Bool) (outer : Core.Row) (key : JoinSearchKey)
    (inner : List (Core.Row × Nat)) (message : String)
    (failed : prepared.context.eval
      (CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer))
      key.value = .error message) :
    joinSearchCandidates context prepared source exchanged outer (.point key) inner = .error message := by
  simp [joinSearchCandidates, failed, bind, Except.bind]

/-- Rewind does not evaluate an ON expression on an absent candidate pair. -/
theorem joinSearchCandidates_scan_empty (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (exchanged : Bool) (outer : Core.Row) :
    joinSearchCandidates context prepared source exchanged outer .scan [] =
      .ok { rows := [], halt := !source.leftJoin } := by
  simp [joinSearchCandidates, pure, Except.pure]

/-- For an inner join, building an empty automatic index halts before its
search-key expressions. LEFT joins instead proceed to initialize their keys. -/
theorem joinSearchCandidates_automatic_empty (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (exchanged : Bool) (outer : Core.Row) (keys : List JoinSearchKey)
    (inner : source.leftJoin = false) :
    joinSearchCandidates context prepared source exchanged outer (.automatic keys) [] =
      .ok { rows := [], halt := true } := by
  simp [joinSearchCandidates, inner, pure, Except.pure]

/-- Source-local inner WHERE filters run after cursor initialization and
before dynamic ON. Outer joins retain their ON-before-WHERE match bookkeeping. -/
def joinSearchMatches (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (row : CoreJoin.JoinedRow) : Except String Bool := do
  let input := CoreJoin.projectRow (joinScalarInputs context) row
  unless ← plan.innerWhere.allM (fun term => prepared.context.matches input (some term)) do return false
  joinScalarMatches context prepared (source.leftJoin || source.rightJoin) row

theorem joinSearchMatches_without_inner_filter (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (row : CoreJoin.JoinedRow)
    (empty : plan.innerWhere = []) :
    joinSearchMatches context prepared source plan row =
      joinScalarMatches context prepared (source.leftJoin || source.rightJoin) row := by
  simp [joinSearchMatches, empty]

/-- The planned row producer preserves original right-row indices for outer
match bookkeeping. An empty Rewind finishes its cursor nest; a failed point
seek merely advances to the next outer row. -/
def joinSearchRowsGo (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (exchanged : Bool)
    (inner : List (Core.Row × Nat)) : List Core.Row → List CoreJoin.JoinedRow → List Nat →
      Except String (List CoreJoin.JoinedRow)
  | [], reversed, matched =>
      let suffix := if source.rightJoin then
        (inner.filter (fun (_, index) => !matched.contains index)).map
          (fun (row, _) => (CoreJoin.nullRow context.leftSchema.columns.length, row)) else []
      .ok (reversed.reverse ++ suffix)
  | outer :: rest, reversed, matched => do
      let input := CoreJoin.projectRow (joinScalarInputs context) (joinSearchPair context exchanged outer)
      unless ← joinFixedMatches prepared input plan.fixed plan.early do
        return ← joinSearchRowsGo context prepared source plan exchanged inner rest reversed matched
      let found ← joinSearchCandidates context prepared source exchanged outer plan.access inner
      if found.halt then return reversed.reverse
      let selected ← found.rows.filterM (fun (row, _) => joinSearchMatches context prepared source plan (joinSearchPair context exchanged outer row))
      let rows := if selected.isEmpty && source.leftJoin then [joinSearchPair context false outer]
        else selected.map (fun (row, _) => joinSearchPair context exchanged outer row)
      joinSearchRowsGo context prepared source plan exchanged inner rest
        (rows.reverse ++ reversed) (selected.map Prod.snd ++ matched)

/-- Keep the proved total-predicate producer for scans without early terms;
computed searches and filters use the effectful cursor producer. -/
def joinSearchRows (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (plan : JoinSearchPlan) (exchanged : Bool)
    (inner : List (Core.Row × Nat)) (outer : List Core.Row) : Except String (List CoreJoin.JoinedRow) :=
  if plan.early.isEmpty && plan.innerWhere.isEmpty && prepared.onExpression.isNone then
    match plan.access with
    | .scan => joinScalarRowsM context prepared source
        (if exchanged then inner.map Prod.fst else outer)
        (if exchanged then outer else inner.map Prod.fst) exchanged
    | _ => joinSearchRowsGo context prepared source plan exchanged inner outer [] []
  else joinSearchRowsGo context prepared source plan exchanged inner outer [] []

structure JoinReadReport where
  result : Core.Result := {}
  width : Nat := 0
  error : Option String := none

def JoinReadReport.toExcept (report : JoinReadReport) : Except String (Core.Result × Nat) :=
  match report.error with
  | none => .ok (report.result, report.width)
  | some message => .error message

def joinScalarMaterializedReport (state : Core.State) (select : Select) : Except String JoinReadReport := do
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
  let where_ := prepared.select.where_
  let source := joinScalarReducedSource context prepared originalRight
  let (on, _) := match originalRight.joinOn with
    | none => (none, none)
    | some expression => CoreOrder.resolveJoinOnAliases (joinHasColumn context) select.columns.toList expression
  let on ← on.mapM (joinScalarBind context)
  let enabled ← if select.limit == some 0 || joinScalarKnownEmpty context prepared source then pure false
    else joinFixedConstantMatches context prepared source on
  let enabled ← if enabled && !source.leftJoin && !source.rightJoin then prepared.context.constantMatches on else pure enabled
  let (rows, ordered) ← if enabled then do
      let terms ← CoreOrder.resolve prepared.context prepared.select.columns.toList prepared.select.orderBy.toList
      let traversal := joinScalarTraversal context prepared source terms on
      let outerSide := if traversal.exchanged then CoreJoin.Side.right else .left
      let early := if source.rightJoin then [] else
        (where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
          (fun term => joinScalarOnlySide context prepared outerSide term && !prepared.context.constantExpression term)
      let plan := joinSearchPlan context prepared source traversal on
      let plan := { plan with early := early ++ plan.early }
      let left := if traversal.reverseLeft then left.rows.reverse else left.rows
      let right := if traversal.reverseRight then right.rows.reverse else right.rows
      let outer := if traversal.exchanged then right else left
      let inner := if traversal.exchanged then left else right
      let outer ← match traversal.root with
        | none => pure outer
        | some access => do
            let empty := CoreJoin.nullRow (if traversal.exchanged then context.leftSchema.columns.length else context.rightSchema.columns.length)
            pure ((← joinSearchCandidates context prepared source (!traversal.exchanged) empty access outer.zipIdx).rows.map Prod.fst)
      let inner := inner.zipIdx
      let rows ← joinSearchRows context prepared source plan traversal.exchanged inner outer
      pure (rows, traversal.ordered)
    else pure ([], false)
  if !prepared.select.groupBy.isEmpty then
    let inputs := rows.map (CoreJoin.projectRow (joinScalarInputs context))
    let (report, width) ← CoreGrouped.observe prepared.context prepared.select inputs
    return { result := { rows := report.rows }, width, error := report.error }
  let (result, width) ← joinScalarRun context prepared rows ordered
  return { result, width }

def joinScalarMaterializedResult (state : Core.State) (select : Select) : Except String (Core.Result × Nat) := do
  (← joinScalarMaterializedReport state select).toExcept

structure JoinStreamState where
  aggregates : Option (Array (CoreAggregate.Term × CoreAggregate.Accumulator)) := none
  reversed : List (List Core.Value) := []
  seen : List (List Core.Value) := []
  skip : Nat := 0
  remaining : Option Nat := none
  error : Option String := none

def JoinStreamState.stopped (state : JoinStreamState) : Bool :=
  state.error.isSome || state.remaining == some 0

def joinStreamStep (context : JoinContext) (prepared : JoinScalarPrepared)
    (expressions : List Expr) (state : JoinStreamState) (row : CoreJoin.JoinedRow) : JoinStreamState := Id.run do
  if state.stopped then return state
  let ctx := prepared.context
  let input := CoreJoin.projectRow (joinScalarInputs context) row
  let selected := ctx.matches input prepared.select.where_
  match selected with
  | .error message => return { state with error := some message }
  | .ok false => return state
  | .ok true =>
      if let some states := state.aggregates then
        match states.mapM (fun (term, accumulator) => do
            return (term, ← accumulator.ingest term ctx input)) with
        | .error message => return { state with error := some message }
        | .ok states => return { state with aggregates := some states, reversed := input :: state.reversed }
      if state.skip > 0 && !prepared.select.distinct then return { state with skip := state.skip - 1 }
      match ctx.projectRow input expressions with
      | .error message => return { state with error := some message }
      | .ok output =>
          if prepared.select.distinct && state.seen.any (CoreExpr.distinctEqual expressions output) then return state
          let state := { state with seen := Core.distinctRowKey output :: state.seen }
          if state.skip > 0 then return { state with skip := state.skip - 1 }
          return { state with reversed := output :: state.reversed, remaining := state.remaining.map (· - 1) }

def joinStreamRight (context : JoinContext) (prepared : JoinScalarPrepared) (source : TableRef) (plan : JoinSearchPlan)
    (expressions : List Expr) (exchanged : Bool) (outer : Core.Row) :
    List (Core.Row × Nat) → JoinStreamState → Bool → List Nat → JoinStreamState × Bool × List Nat
  | [], state, found, matched => (state, found, matched)
  | (inner, index) :: rest, state, found, matched =>
      if state.stopped then (state, found, matched)
      else
        let row := if exchanged then (inner, outer) else (outer, inner)
        match joinSearchMatches context prepared source plan row with
        | .error message => ({ state with error := some message }, found, matched)
        | .ok false => joinStreamRight context prepared source plan expressions exchanged outer rest state found matched
        | .ok true => joinStreamRight context prepared source plan expressions exchanged outer rest
            (joinStreamStep context prepared expressions state row) true (index :: matched)

def joinStreamSuffix (context : JoinContext) (prepared : JoinScalarPrepared)
    (expressions : List Expr) : List Core.Row → JoinStreamState → JoinStreamState
  | [], state => state
  | row :: rows, state =>
      if state.stopped then state else
      joinStreamSuffix context prepared expressions rows
        (joinStreamStep context prepared expressions state (CoreJoin.nullRow context.leftSchema.columns.length, row))

def joinStreamLeft (context : JoinContext) (prepared : JoinScalarPrepared) (source : TableRef)
    (expressions early : List Expr) (exchanged : Bool) (inner : List (Core.Row × Nat))
    (plan : JoinSearchPlan) :
    List Core.Row → JoinStreamState → List Nat → JoinStreamState
  | [], state, matched =>
      if source.rightJoin then joinStreamSuffix context prepared expressions
        ((inner.filter (fun (_, index) => !matched.contains index)).map Prod.fst) state else state
  | outer :: rest, state, matched =>
      if state.stopped then state
      else
        let input := CoreJoin.projectRow (joinScalarInputs context)
          (if exchanged then (CoreJoin.nullRow context.leftSchema.columns.length, outer)
            else (outer, CoreJoin.nullRow context.rightSchema.columns.length))
        match joinFixedMatches prepared input plan.fixed early with
        | .error message => { state with error := some message }
        | .ok false => joinStreamLeft context prepared source expressions early exchanged inner plan rest state matched
        | .ok true =>
            match joinSearchCandidates context prepared source exchanged outer plan.access inner with
            | .error message => { state with error := some message }
            | .ok candidates =>
                if candidates.halt then state else
                let (state, found, matched) := joinStreamRight context prepared source plan expressions exchanged outer candidates.rows state false matched
                let state := if !found && source.leftJoin then joinStreamStep context prepared expressions state
                    (outer, CoreJoin.nullRow context.rightSchema.columns.length) else state
                joinStreamLeft context prepared source expressions early exchanged inner plan rest state matched

/-- An aggregate output is produced only after all input steps finish. A
recorded input error wins over finalization, HAVING and result expressions. -/
def joinAggregateStreamFinish (ctx : CoreExpr.Context)
    (select : Select) (prepared : CoreAggregateHaving.Prepared)
    (state : JoinStreamState) : Except String JoinReadReport := do
  if let some message := state.error then throw message
  let some states := state.aggregates | unsupported "missing joined aggregate accumulators"
  let values ← states.mapM fun (term, accumulator) => accumulator.finish term
  let row ← CoreAggregateHaving.representative ctx prepared.results.terms state.reversed.reverse
  let selected ← prepared.matches ctx values row
  let rows ← if !selected || select.offset > 0 then pure []
    else do pure [← prepared.finish ctx values row]
  return { result := { rows }, width := prepared.results.expressions.length }

theorem joinAggregateStreamFinish_error (ctx : CoreExpr.Context) (select : Select)
    (prepared : CoreAggregateHaving.Prepared) (state : JoinStreamState) (message : String)
    (failed : state.error = some message) :
    joinAggregateStreamFinish ctx select prepared state = .error message := by
  simp only [joinAggregateStreamFinish, failed] <;> rfl

/-- Use the same join cursors, ON bookkeeping and early predicates as scalar
streaming. Each accepted pair steps every aggregate before visiting a new pair. -/
def joinAggregateStreamResult (context : JoinContext) (prepared : JoinScalarPrepared)
    (source : TableRef) (traversal : JoinScalarTraversal) (on : Option Expr)
    (leftRows rightRows : List Core.Row) : Except String JoinReadReport := do
  let ctx := prepared.context
  let select := prepared.select
  if select.distinct then CoreExpr.validateDistinct (select.columns.toList.map (·.expr))
  let aggregate ← CoreAggregateHaving.prepare ctx select.columns.toList select.orderBy.toList select.having
  let _ ← select.where_.mapM ctx.validate
  let width := aggregate.results.expressions.length
  if select.limit == some 0 then return { width }
  let initial : JoinStreamState := {
    aggregates := some (aggregate.results.terms.map (fun term => (term, {}))) }
  let finish := joinAggregateStreamFinish ctx select aggregate
  if joinScalarKnownEmpty context prepared source then return ← finish initial
  unless ← joinFixedConstantMatches context prepared source on do return ← finish initial
  let right := if traversal.reverseRight then rightRows.reverse else rightRows
  let left := if traversal.reverseLeft then leftRows.reverse else leftRows
  let outerSide := if traversal.exchanged then CoreJoin.Side.right else .left
  let early := if source.rightJoin then [] else
    (select.where_.map SQLite.Scalar.conditionTerms |>.getD []).filter
      (fun term => joinScalarOnlySide context prepared outerSide term && !ctx.constantExpression term)
  let plan := joinSearchPlan context prepared source traversal on
  let early := early ++ plan.early
  unless source.leftJoin || source.rightJoin do
    unless ← ctx.constantMatches on do return ← finish initial
  let outer := if traversal.exchanged then right else left
  let inner := if traversal.exchanged then left else right
  let outer ← match traversal.root with
    | none => pure outer
    | some access => do
        let empty := CoreJoin.nullRow (if traversal.exchanged then context.leftSchema.columns.length else context.rightSchema.columns.length)
        pure ((← joinSearchCandidates context prepared source (!traversal.exchanged) empty access outer.zipIdx).rows.map Prod.fst)
  let result := joinStreamLeft context prepared source [] early traversal.exchanged inner.zipIdx plan outer initial []
  finish result

end CoreSQL

end SQLeanite
