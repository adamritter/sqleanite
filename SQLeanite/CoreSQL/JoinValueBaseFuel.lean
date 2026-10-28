import SQLeanite.CoreGrouped
import SQLeanite.CoreOptimizerBridge.SymbolicLeftOnPlan
import SQLeanite.CoreOuterJoin
import SQLeanite.CoreSQL.JoinResultExpr

namespace SQLeanite
namespace CoreSQL

/-- These leading wrappers preserve values. Their collation and CTAS affinity
metadata are read from the original expression separately. -/
def joinValueBaseFuel : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression => match expression with
    | .unary .plus argument | .collate argument _ => joinValueBaseFuel fuel argument
    | .call name arguments false => match SQLite.Probability.input? name arguments with
      | some argument => joinValueBaseFuel fuel argument
      | none => expression
    | _ => expression

def joinWrappedColumns (context : JoinContext) (columns : List ResultColumn) :
    Except String (List ResultColumn × List (Option String)) := do
  let parts ← columns.mapM fun column => do
    let bound := joinBindNames context column.expr
    let base := joinValueBaseFuel bound.height bound
    let references ← joinResultExpr context base
    let name := match bound with
      | .star _ => some "binary"
      | _ => SQLite.ExprCollation.effectiveName bound
    pure ({ column with expr := base }, List.replicate references.length name)
  return (parts.map Prod.fst, (parts.map Prod.snd).flatten)

/-- Top-level aliases/positions inherit their selected result's collation;
source expressions retain their own metadata. -/
def joinOrderOutputPosition? (columns : List (CoreJoin.Operand × Option String))
    (expression : Expr) : Option Nat :=
  let expression := SQLite.Scalar.prepare (CoreOrder.keyExpression expression)
  match (CoreOrder.bareName? expression).bind (fun name =>
      columns.findIdx? (fun output => output.2.any (fun alias => canonical alias == canonical name))) with
  | some position => some position
  | none => (CoreOrder.ordinal? expression).bind fun position =>
      if 1 ≤ position && position.toNat ≤ columns.length then some (position.toNat - 1) else none

def joinWrappedOrderReference (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (expression : Expr) :
    Except String (Option CoreJoin.ColumnRef) :=
  match joinOrderReference context columns expression with
  | .ok reference => .ok reference
  | .error message => do
      let key := SQLite.Scalar.prepare (CoreOrder.keyExpression expression)
      if (CoreOrder.ordinal? key).isSome then throw message
      let bound := joinBindNames context key
      let base := joinValueBaseFuel bound.height bound
      if base.any SQLite.StaticCondition.resolutionForbidden then throw message
      let reference ← joinOperand context base
      joinOrderOutputReference reference

def joinWrappedOrderBy (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (names : List (Option String))
    (terms : List OrderTerm) : Except String (List CoreJoin.OrderTerm) := do
  let terms ← terms.mapM fun term => do
    let selected := (joinOrderOutputPosition? columns term.expr).bind (fun position => names[position]?.getD none)
    let kind ← SQLite.ExprCollation.require (SQLite.ExprCollation.ofName
      ((SQLite.ExprCollation.name term.expr).orElse (fun _ => selected)))
    let reference ← joinWrappedOrderReference context columns term.expr
    pure (reference.map fun reference => ({
      reference := reference
      descending := term.descending
      nullsFirst := some (term.nullsFirst.getD (!term.descending))
      collation := kind } : CoreJoin.OrderTerm))
  return terms.filterMap id

/-- Normalize only value-preserving projection wrappers, then reuse the same
join predicates, source validation and row windows. Original output collations
control DISTINCT, alias/ordinal ordering and later compound metadata. -/
def joinWrappedQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query := do
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  let (columns, names) ← joinWrappedColumns context select.columns.toList
  let orderColumns ← joinOrderColumns context columns
  let orderBy ← joinWrappedOrderBy context orderColumns names select.orderBy.toList
  let kinds ← if select.distinct then names.mapM (fun name => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName name))
    else pure []
  let query ← joinQueryForRows { select with columns := columns.toArray, orderBy := #[] }
    leftTable rightTable leftSchema rightSchema leftRows rightRows
  let mayExchange := !rightSource.leftJoin && !rightSource.crossJoin
  return { query with
    orderBy
    distinctCollations := if kinds.all (· == .binary) then [] else kinds
    lookupScanOrder := joinLookupScanOrder leftSchema rightSchema mayExchange query.on query.where_ orderBy
    distinctScanOrder := joinDistinctScanOrder leftSchema rightSchema mayExchange
      (query.on.any (joinHasRowidEquality leftSchema rightSchema) ||
        query.where_.any (joinHasRowidEquality leftSchema rightSchema))
      (orderBy.map (fun term => (term.reference, term.descending))) }

def joinQueryComplete (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query :=
  match joinQueryForRows select leftTable rightTable leftSchema rightSchema leftRows rightRows with
  | .ok query => .ok query
  | .error message =>
      match joinWrappedQuery select leftTable rightTable leftSchema rightSchema leftRows rightRows with
      | .ok query => .ok query
      | .error _ => .error message

theorem joinQueryComplete_existing (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) (query : CoreJoin.Query)
    (success : joinQuery select leftTable rightTable leftSchema rightSchema = .ok query) :
    joinQueryComplete select leftTable rightTable leftSchema rightSchema leftRows rightRows = .ok query := by
  simp [joinQueryComplete, joinQueryForRows, joinQueryWithZero, success]

/-- The bound interpreter is also used by RIGHT shared-name queries, where
unqualified merged columns resolve to the right schema. Empty/zero-LIMIT
predicates retain the same preparation checks as the ordinary join path. -/
def joinRightBoundForRows (select : Select) (source : TableRef) (context : JoinContext)
    (leftRows rightRows : List Core.Row) : Except String CoreJoin.Query :=
  match joinQueryBound select source context with
  | .ok query => .ok query
  | .error message => do
      let zero := select.limit == some 0
      if !zero && select.where_.isSome then return ← throw message
      unless zero || leftRows.isEmpty || rightRows.isEmpty do throw message
      if !zero && source.joinOn.any (joinComputedCursorKey context) then throw message
      for expression in source.joinOn.toList do
        let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
        unless joinStaticAdmitted context prepared true do throw message
      if zero then
        for expression in select.where_.toList do
          let prepared := SQLite.Scalar.prepare (joinBindNames context expression)
          unless joinStaticAdmitted context prepared do throw message
      match joinQueryBound { select with where_ := if zero then none else select.where_ }
          { source with joinOn := none } context with
      | .ok query => .ok query
      | .error _ => .error message

/-- WHERE may remove the outer side and expose early ON evaluation. A failed
translation with WHERE must reach the general planner, not erase ON merely
because a source is empty. LIMIT zero retains its independent admission path. -/
theorem joinRightBoundForRows_where_failure (select : Select) (source : TableRef)
    (context : JoinContext) (left right : List Core.Row) (message : String)
    (failed : joinQueryBound select source context = .error message)
    (nonzero : (select.limit == some 0) = false) (present : select.where_.isSome = true) :
    joinRightBoundForRows select source context left right = .error message := by
  simp [joinRightBoundForRows, failed, nonzero, present]
  rfl

/-- FULL merged output operands need their actual coalesced value for sorting.
The original source reference remains available for ordinary column terms. -/
def joinFullOrderValue (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (expression : Expr) :
    Except String (Option CoreJoin.Operand) := do
  let key := SQLite.Scalar.prepare (CoreOrder.keyExpression expression)
  if let some name := CoreOrder.bareName? key then
    if let some output := columns.find? (fun output => output.2.any (fun alias => canonical alias == canonical name)) then
      return some output.1
  if let some position := CoreOrder.ordinal? key then
    unless 1 ≤ position && position.toNat ≤ columns.length do
      throw "ORDER BY position is outside the result columns"
    let some output := columns[position.toNat - 1]? | throw "ORDER BY position is out of range"
    return some output.1
  if joinOrderConstant key then return none
  let bound := joinBindNames context key
  let base := joinValueBaseFuel bound.height bound
  if base.any SQLite.StaticCondition.resolutionForbidden then unsupported "FULL JOIN order resolution"
  let operand ← joinOperand context base
  return some operand

def joinFullOrderBy (context : JoinContext)
    (columns : List (CoreJoin.Operand × Option String)) (names : List (Option String))
    (terms : List OrderTerm) : Except String (List CoreJoin.OrderTerm) := do
  let terms ← terms.mapM fun term => do
    let selected := (joinOrderOutputPosition? columns term.expr).bind (fun position => names[position]?.getD none)
    let kind ← SQLite.ExprCollation.require (SQLite.ExprCollation.ofName
      ((SQLite.ExprCollation.name term.expr).orElse (fun _ => selected)))
    let value ← joinFullOrderValue context columns term.expr
    match value with
    | none | some (.literal _) => pure none
    | some operand =>
        let reference ← match operand with
          | .column reference => pure reference
          | .mergedColumn none left _ => pure ⟨.left, left⟩
          | _ => unsupported "FULL JOIN coerced output ordering"
        pure (some ({
          reference
          descending := term.descending
          nullsFirst := some (term.nullsFirst.getD (!term.descending))
          collation := kind
          valueOperand := some operand } : CoreJoin.OrderTerm))
  return terms.filterMap id

def joinRightQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query := do
  if joinAliasesNeeded select leftSchema rightSchema then unsupported "unresolved joined result alias"
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  unless rightSource.rightJoin && leftSource.schema.isNone && leftSource.functionArgs.isNone && leftSource.subquerySql.isNone && rightSource.schema.isNone && rightSource.functionArgs.isNone && rightSource.subquerySql.isNone &&
      leftSource.joinOn.isNone && select.groupBy.isEmpty && select.having.isNone do
    unsupported "RIGHT/FULL join source shape"
  unless canonical leftSource.name = canonical leftTable && canonical rightSource.name = canonical rightTable do
    throw "join source/schema mismatch"
  let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
  let (columns, names) ← joinWrappedColumns context select.columns.toList
  let orderColumns ← joinOrderColumns context columns
  let orderBy ← if context.coalesceShared then joinFullOrderBy context orderColumns names select.orderBy.toList
    else joinWrappedOrderBy context orderColumns names select.orderBy.toList
  let kinds ← if select.distinct then names.mapM (fun name => SQLite.ExprCollation.require (SQLite.ExprCollation.ofName name))
    else pure []
  let query ← joinRightBoundForRows { select with columns := columns.toArray, orderBy := #[] }
    rightSource context leftRows rightRows
  return { query with orderBy, distinctCollations := if kinds.all (· == .binary) then [] else kinds }

/-- Retry unresolved ON/WHERE aliases against the original result expressions.
The established interpreter gets first refusal; aliases never shadow a source
name, and an inserted result expression is not recursively treated as aliases. -/
def joinAliasQuery (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) :
    Except String CoreJoin.Query :=
  let translate := if select.sources[1]?.any (fun source => source.rightJoin) then joinRightQuery else joinQueryComplete
  match translate select leftTable rightTable leftSchema rightSchema leftRows rightRows with
  | .ok query => .ok query
  | .error message => do
      let (leftSource, rightSource) ← match select.sources.toList with
        | [left, right] => .ok (left, right)
        | _ => .error message
      let context ← joinContext leftSource rightSource leftTable rightTable leftSchema rightSchema
      let needs := CoreOrder.needsAliasesWith (joinHasColumn context) select.columns.toList
      unless rightSource.joinOn.any needs || select.where_.any needs do throw message
      let resolve := CoreOrder.resolveAliasesWith (joinHasColumn context) select.columns.toList
      let (on, deferred) := match rightSource.joinOn with
        | none => (none, none)
        | some expression => CoreOrder.resolveJoinOnAliases (joinHasColumn context) select.columns.toList expression
      let source := { rightSource with joinOn := on }
      let ordering := select.orderBy.map fun term =>
        { term with expr := CoreOrder.resolveOrderAliasesWith (joinHasColumn context) select.columns.toList term.expr }
      let resolved := { select with
        sources := #[leftSource, source]
        where_ := CoreOrder.combineAliasConditions (select.where_.map resolve) deferred
        orderBy := ordering
        columns := select.columns.map (fun column => { column with alias := none }) }
      translate resolved leftTable rightTable leftSchema rightSchema leftRows rightRows

theorem joinAliasQuery_existing (select : Select) (leftTable rightTable : String)
    (leftSchema rightSchema : Core.Schema) (leftRows rightRows : List Core.Row) (query : CoreJoin.Query)
    (ordinary : select.sources[1]?.any (fun source => source.rightJoin) = false)
    (success : joinQueryComplete select leftTable rightTable leftSchema rightSchema leftRows rightRows = .ok query) :
    joinAliasQuery select leftTable rightTable leftSchema rightSchema leftRows rightRows = .ok query := by
  simp [joinAliasQuery, ordinary, success]

def rightJoinResult (state : Core.State) (select : Select)
    (leftSource rightSource : TableRef) : Except String (Core.Result × Nat) := do
  let leftTable := resolveTableName state leftSource.name
  let rightTable := resolveTableName state rightSource.name
  let some left := state.database.findTable? leftTable | throw s!"no such table: {leftSource.name}"
  let some right := state.database.findTable? rightTable | throw s!"no such table: {rightSource.name}"
  let query ← joinAliasQuery select leftTable rightTable left.schema right.schema left.rows right.rows
  let query := CoreOptimizerBridge.optimizeJoin leftTable rightTable query
  let rows := CoreOuterJoin.eval rightSource.leftJoin left.schema.columns.length query left.rows right.rows
  return ({ rows }, query.columns.length)

def executeRightJoin (state : Core.State) (select : Select)
    (leftSource rightSource : TableRef) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> rightJoinResult state select leftSource rightSource

theorem executeRightJoin_preserves_state {state : Core.State} {select : Select}
    {leftSource rightSource : TableRef} {execution : SelectExecution}
    (success : executeRightJoin state select leftSource rightSource = .ok execution) :
    execution.state = state := by
  unfold executeRightJoin at success
  cases result : rightJoinResult state select leftSource rightSource with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

def executeJoin (state : Core.State) (select : Select) :
    Except String SelectExecution := do
  let (leftSource, rightSource) ← match select.sources.toList with
    | [left, right] => .ok (left, right)
    | _ => unsupported "join source count"
  if rightSource.rightJoin then return ← executeRightJoin state select leftSource rightSource
  unless leftSource.schema.isNone && leftSource.functionArgs.isNone && leftSource.subquerySql.isNone && rightSource.schema.isNone && rightSource.functionArgs.isNone && rightSource.subquerySql.isNone &&
      leftSource.joinOn.isNone && !rightSource.rightJoin do
    throw "unsupported general verified-MVP SQL: only two-table INNER/CROSS/comma/LEFT JOIN"
  unless select.groupBy.isEmpty && select.having.isNone do
    throw "unsupported general verified-MVP SQL: join SELECT shape"
  let leftTable := resolveTableName state leftSource.name
  let rightTable := resolveTableName state rightSource.name
  let left ← match state.database.findTable? leftTable with
    | some table => .ok table
    | none => .error s!"no such table: {leftSource.name}"
  let right ← match state.database.findTable? rightTable with
    | some table => .ok table
    | none => .error s!"no such table: {rightSource.name}"
  let query ← joinAliasQuery select leftTable rightTable left.schema right.schema left.rows right.rows
  let query := CoreOptimizerBridge.optimizeJoin leftTable rightTable query
  let (next, result) ← Core.execute state (.join leftTable rightTable query)
  return ⟨next, result, query.columns.length⟩

/-- A SELECT without FROM has one implicit zero-column input row. Validate
all expressions before evaluating WHERE, LIMIT, and then the result row;
unselected expressions must not raise evaluation errors. -/
def scalarConstantRow (select : Select) : Except String (Option (List Core.Value)) := do
  unless select.sources.isEmpty && select.valueRows.isNone &&
      select.groupBy.isEmpty && select.having.isNone do
    unsupported "constant SELECT shape"
  for expression in select.columns.toList.map (·.expr) ++ select.where_.toList do
    if let some message := SQLite.Scalar.resolutionError (fun _ _ => false) expression then throw message
    let prepared := SQLite.Scalar.prepare expression
    if let some message := SQLite.Scalar.functionError prepared.height prepared then throw message
  unless select.columns.all (fun column => SQLite.Scalar.admitted column.expr) &&
      select.where_.all SQLite.Scalar.admitted do
    unsupported "constant SELECT expression"
  let ctx : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  if select.distinct then
    CoreExpr.validateDistinct (select.columns.toList.map (·.expr))
  -- SQLite validates aggregate calls in a source-free scalar ORDER BY but
  -- does not turn the scalar SELECT into an aggregate query or evaluate them.
  let _ ← CoreAggregateOrder.prepare ctx select.columns.toList select.orderBy.toList
  if select.limit == some 0 then return none
  if let some condition := select.where_ then
    unless ← SQLite.Scalar.testWhere condition do return none
  if select.offset > 0 then return none
  return some (← select.columns.toList.mapM (fun column => literal column.expr))

/-- A source-free aggregate consumes the SELECT's single implicit empty row,
unless WHERE rejects it. It still emits one aggregate row for empty input. -/
def constantRow (select : Select) : Except String (Option (List Core.Value)) := do
  let aliasContext : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  let select := { select with where_ := select.where_.map (CoreOrder.resolveAliases aliasContext select.columns.toList) }
  if !select.groupBy.isEmpty then
    unless select.sources.isEmpty && select.valueRows.isNone do unsupported "constant grouped SELECT shape"
    let ctx : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
    let (rows, _) ← CoreGrouped.run ctx select [[]]
    match rows with
    | [] => return none
    | [row] => return some row
    | _ => throw "source-free GROUP BY produced more than one group"
  unless select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) do
    return ← scalarConstantRow select
  unless select.sources.isEmpty && select.valueRows.isNone &&
      select.groupBy.isEmpty do
    unsupported "constant aggregate SELECT shape"
  let ctx : CoreExpr.Context := { schema := { name := "", columns := [], primaryKey := 0 }, sourceName := "" }
  if select.distinct then
    CoreExpr.validateDistinct (select.columns.toList.map (fun c => ctx.bindNames c.expr))
  let prepared ← CoreAggregateHaving.prepare ctx select.columns.toList select.orderBy.toList select.having
  unless prepared.results.terms.all (fun term => term.argument.all SQLite.Scalar.admitted) &&
      select.where_.all SQLite.Scalar.admitted do
    unsupported "unbound constant aggregate expression"
  if select.limit == some 0 then return none
  let enabled ← match select.where_ with
    | none => pure true
    | some condition => SQLite.Scalar.testWhere condition
  let values ← prepared.results.accumulate ctx (if enabled then [[]] else [])
  unless ← prepared.matches ctx values [] do return none
  if select.offset > 0 then return none
  return some (← prepared.finish ctx values [])

def executeConstantSelect (state : Core.State) (select : Select) :
    Except String SelectExecution :=
  (fun row => { state, result := { rows := row.toList }, width := select.columns.size }) <$>
    constantRow select

theorem executeConstantSelect_preserves_state {state : Core.State} {select : Select}
    {execution : SelectExecution} (success : executeConstantSelect state select = .ok execution) :
    execution.state = state := by
  unfold executeConstantSelect at success
  cases row : constantRow select with
  | error message => simp [row, Functor.map, Except.map] at success
  | ok value =>
      simp [row, Functor.map, Except.map] at success
      cases success
      rfl

theorem executeConstantSelect_at_most_one_row {state : Core.State} {select : Select}
    {execution : SelectExecution} (success : executeConstantSelect state select = .ok execution) :
    execution.result.rows.length ≤ 1 := by
  unfold executeConstantSelect at success
  cases row : constantRow select with
  | error message => simp [row, Functor.map, Except.map] at success
  | ok value =>
      simp [row, Functor.map, Except.map] at success
      cases success
      cases value <;> simp

/-- A scalar read can fail after emitting a typed row prefix. Preparation
and sorting failures have no published prefix. -/
structure ScalarReadReport where
  result : Core.Result := {}
  width : Nat := 0
  error : Option String := none

def ScalarReadReport.toExcept (report : ScalarReadReport) : Except String (Core.Result × Nat) :=
  match report.error with
  | none => .ok (report.result, report.width)
  | some message => .error message

/-- Fallback for row-dependent WHERE expressions. Source rows still come from
Core.execute. A primary-key order determines scan direction; other orderings
sort surviving outputs. LIMIT is applied during an ordered scan or after a
sort, and all names are bound before either path can skip evaluation. -/
def filteredSelectReadPrepared (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String ScalarReadReport := do
  unless select.groupBy.isEmpty do unsupported "row-expression grouped WHERE"
  let ctx : CoreExpr.Context := { schema := stored.schema, rowidAliases := !stored.withoutRowid, sourceName := source.alias.getD source.name, storedTexts := state.catalog.storedTexts }
  let expressions ← ctx.projection select.columns.toList
  if select.distinct then CoreExpr.validateDistinct expressions
  let _ ← select.where_.mapM ctx.validate
  let terms ← resolvedOrdering stored.schema source select
  let _ ← terms.mapM (CoreOrder.validateTerm ctx)
  let ordering := terms.head?.toList.flatMap fun term =>
    match ctx.bindNames (CoreOrder.keyExpression term.expr) with
    | .column qualifier name => (ctx.column? qualifier name).toList.map (·, term.descending)
    | _ => []
  if select.limit != some 0 then
    unless ← ctx.constantMatches select.where_ do return { width := expressions.length }
  let search ← if select.limit == some 0 then pure none
    else expressionSearch ctx stored select.where_
  let ctx := expressionSearchContext ctx search
  if select.limit != some 0 then
    unless ← expressionSearchReady ctx search select.where_ do return { width := expressions.length }
  let singleRow := search.any (fun predicate => match predicate with
    | .equal index _ => index == stored.schema.primaryKey
    | _ => false)
  let orderedScan := terms.isEmpty || singleRow ||
    (terms.head?.any (fun term => match ctx.bindNames (CoreOrder.keyExpression term.expr) with
      | .column qualifier name => ctx.column? qualifier name == some stored.schema.primaryKey
      | _ => false))
  let query : Core.Query := {
    columns := List.range stored.schema.columns.length
    predicate := search
    orderBy := if orderedScan then ordering else [] }
  let (_, result) ← Core.execute state (.query (resolveTableName state source.name) query)
  let projected ← if orderedScan then
      pure (ctx.scanWindowObserved select.where_ expressions select.distinct result.rows select.offset select.limit [])
    else do
      let rows ← CoreOrder.scan ctx select.where_ expressions terms select.distinct result.rows select.offset select.limit
      pure ({ rows } : CoreExpr.ScanReport)
  return {
    result := { result with rows := projected.rows.map (·.output) }
    width := expressions.length
    error := projected.error }

def filteredSelectReadReport (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : ScalarReadReport :=
  match filteredSelectReadPrepared state select source stored with
  | .ok report => report
  | .error message => { error := some message }

def filteredSelectResult (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String (Core.Result × Nat) :=
  (filteredSelectReadReport state select source stored).toExcept

def executeFilteredSelect (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> filteredSelectResult state select source stored

end CoreSQL

end SQLeanite
