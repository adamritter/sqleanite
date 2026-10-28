import SQLeanite.CoreSQL.JoinValueBaseFuel
import SQLeanite.SQLite.Values

namespace SQLeanite
namespace CoreSQL

theorem executeFilteredSelect_preserves_state {state : Core.State} {select : Select}
    {source : TableRef} {stored : Core.Table} {execution : SelectExecution}
    (success : executeFilteredSelect state select source stored = .ok execution) :
    execution.state = state := by
  unfold executeFilteredSelect at success
  cases result : filteredSelectResult state select source stored with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

/-- Direct Core queries sort before projection. When DISTINCT is ordered by
an unprojected source column, source representatives must be retained before
sorting; route those queries through the expression scan instead. -/
def queryNeedsRepresentatives (distinct : Bool) (columns : List Nat)
    (ordering : List (Nat × Bool)) : Bool :=
  distinct && !(ordering.all fun term => columns.contains term.1)

/-- Aggregate arguments bind before empty-input/LIMIT shortcuts. WHERE and
aggregate steps interleave over Core rows before the result is finalized. -/
def aggregateSelectResult (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String (Core.Result × Nat) := do
  unless select.groupBy.isEmpty do
    unsupported "aggregate grouping"
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name, storedTexts := state.catalog.storedTexts }
  let select := { select with where_ := select.where_.map (CoreOrder.resolveAliases ctx select.columns.toList) }
  if select.distinct then
    CoreExpr.validateDistinct (select.columns.toList.map (fun c => ctx.bindNames c.expr))
  let prepared ← CoreAggregateHaving.prepare ctx select.columns.toList select.orderBy.toList select.having
  let _ ← select.where_.mapM ctx.validate
  if select.limit == some 0 then return ({}, prepared.results.expressions.length)
  let enabled ← ctx.constantMatches select.where_
  let search ← if enabled then expressionSearch ctx stored select.where_ else pure none
  let ctx := expressionSearchContext ctx search
  let enabled ← if enabled then expressionSearchReady ctx search select.where_ else pure false
  let rows ← if !enabled then pure [] else do
    let (_, result) ← Core.execute state (.query (resolveTableName state source.name)
      { columns := List.range stored.schema.columns.length, predicate := search })
    pure result.rows
  let (values, inputs) ← prepared.results.accumulateSelected ctx select.where_ rows
  let values := values.val
  let representative ← CoreAggregateHaving.representative ctx prepared.results.terms inputs
  let selected ← prepared.matches ctx values representative
  let rows ← if !selected || select.offset > 0 then pure []
    else do pure [← prepared.finish ctx values representative]
  return ({ rows }, prepared.results.expressions.length)

def executeAggregateSelect (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> aggregateSelectResult state select source stored

theorem executeAggregateSelect_preserves_state {state : Core.State} {select : Select}
    {source : TableRef} {stored : Core.Table} {execution : SelectExecution}
    (success : executeAggregateSelect state select source stored = .ok execution) :
    execution.state = state := by
  unfold executeAggregateSelect at success
  cases result : aggregateSelectResult state select source stored with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

/-- The ordinary grouped Core path remains authoritative for its BINARY
column shape. This path adds explicit collation metadata to the same outputs. -/
def collatedGroupResult (select : Select) (source : TableRef) (stored : Core.Table) :
    Except String (Core.Result × Nat) := do
  let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name }
  let (rows, width) ← CoreGrouped.run ctx select (stored.rows.map (·.values))
  return ({ rows }, width)

def executeCollatedGroup (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> collatedGroupResult select source stored

theorem executeCollatedGroup_preserves_state {state : Core.State} {select : Select}
    {source : TableRef} {stored : Core.Table} {execution : SelectExecution}
    (success : executeCollatedGroup state select source stored = .ok execution) :
    execution.state = state := by
  unfold executeCollatedGroup at success
  cases result : collatedGroupResult select source stored with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

/-- Scalar and aggregate projections share bound Core source rows. A recognized
aggregate anywhere in a result expression selects the aggregate evaluator;
aggregate arguments and scalar output templates bind before evaluation. -/
def executeExpressionSelect (state : Core.State) (select : Select) (source : TableRef)
    (stored : Core.Table) (_wherePredicate : Option Core.Predicate) :
    Except String SelectExecution :=
  if !select.groupBy.isEmpty then executeCollatedGroup state select source stored
  else if select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) then
    executeAggregateSelect state select source stored
  else executeFilteredSelect state select source stored

/-- Direct Core commands require source-bound names without pending result-alias
substitution. Expression routes resolve WHERE aliases before scalar validation;
page-directed reads must decline the same unresolved alias shape. -/
def selectNamesBound (schema : Core.Schema) (source : TableRef) (select : Select) : Bool :=
  let ctx : CoreExpr.Context := { schema, sourceName := source.alias.getD source.name }
  !(select.where_.any (CoreOrder.needsAliases ctx select.columns.toList)) &&
    select.columns.all (fun result => ctx.namesBound result.expr) &&
    select.where_.all ctx.namesBound && select.groupBy.all ctx.namesBound &&
    select.having.all ctx.namesBound &&
    ((resolvedOrdering schema source select).toOption.any (fun terms => terms.all (fun term => ctx.namesBound term.expr)))

/-- Preserve a concrete resolver diagnostic when the optimized name-bound
route declines a SELECT. Alias rewriting remains in the ordinary SQL planner. -/
def selectResolutionError (schema : Core.Schema) (source : TableRef) (select : Select) : Option String :=
  let ctx : CoreExpr.Context := { schema, sourceName := source.alias.getD source.name }
  let ordering := ((resolvedOrdering schema source select).toOption.getD []).map (·.expr)
  let expressions := select.columns.toList.map (·.expr) ++ select.where_.toList ++
    select.groupBy.toList ++ select.having.toList ++ ordering
  (expressions.findSome? (SQLite.Scalar.resolutionError (fun q n => (ctx.column? q n).isSome))).orElse fun _ =>
    match resolvedOrdering schema source select with
    | .error message => some message
    | .ok _ => none

@[simp] theorem selectNamesBound_compounds (schema : Core.Schema) (source : TableRef)
    (select : Select) (compounds : Array (CompoundOp × Select)) :
    selectNamesBound schema source { select with compounds } =
      selectNamesBound schema source select := rfl

/-- Writes bind names before deciding whether a predicate/assignment is a
constant Core command or needs row-expression evaluation. -/
def writeNamesBound (schema : Core.Schema) (table : String) (alias : Option String)
    (assignments : Array (String × Expr)) (condition : Option Expr) : Bool :=
  let ctx : CoreExpr.Context := { schema, sourceName := alias.getD table }
  assignments.all (fun assignment => ctx.namesBound assignment.2) && condition.all ctx.namesBound

/-- A VALUES coroutine computes each yielded row before its parent applies
OFFSET. Its initial affinity-bearing direct SELECT rows and a one-row VALUES
core retain scalar SELECT's skip rule. LIMIT bounds the coroutine's yields. -/
def valuesResult (select : Select) : Except String (Core.Result × Nat) := do
  let some rows := select.valueRows | unsupported "VALUES rows"
  let some first := rows[0]? | throw "VALUES requires at least one row"
  unless !first.isEmpty && first.size ≤ SQLite.Limits.maxColumns do
    throw "invalid VALUES column count"
  unless select.sources.isEmpty && select.where_.isNone && select.groupBy.isEmpty &&
      select.having.isNone && select.orderBy.isEmpty && !select.distinct do
    unsupported "VALUES shape"
  for row in rows do
    unless row.size == first.size do throw "all VALUES must have the same number of terms"
  if rows.size == 1 then
    let row ← constantRow { select with valueRows := none }
    return ({ rows := row.toList }, first.size)
  for row in rows do
    for expression in row do
      if let some message := SQLite.Scalar.resolutionError (fun _ _ => false) expression then throw message
      let prepared := SQLite.Scalar.prepare expression
      if let some message := SQLite.Scalar.functionError prepared.height prepared then throw message
    unless row.all SQLite.Scalar.admitted do unsupported "VALUES expression"
  if select.limit == some 0 then return ({}, first.size)
  let selected := match select.limit with
    | none => rows.toList
    | some count => rows.toList.take (count + select.offset)
  let skipped := min select.offset (SQLite.Values.directCount rows.toList)
  let values ← (selected.drop skipped).mapM (fun row => row.toList.mapM literal)
  return ({ rows := values.drop (select.offset - skipped) }, first.size)

def executeValues (state : Core.State) (select : Select) : Except String SelectExecution :=
  (fun result => ⟨state, result.1, result.2⟩) <$> valuesResult select

theorem executeValues_preserves_state {state : Core.State} {select : Select}
    {execution : SelectExecution} (success : executeValues state select = .ok execution) :
    execution.state = state := by
  unfold executeValues at success
  cases result : valuesResult select with
  | error message => simp [result, Functor.map, Except.map] at success
  | ok value =>
      simp [result, Functor.map, Except.map] at success
      cases success
      rfl

def executeSelectBase (state : Core.State) (select : Select) :
    Except String SelectExecution :=
  if select.sources.size = 2 then executeJoin state select
  else if select.sources.isEmpty then
    if select.valueRows.isSome then executeValues state select
    else executeConstantSelect state select
  else do
    unless select.sources.size = 1 do
      throw "unsupported general verified-MVP SQL: SELECT shape"
    let source ← match select.sources[0]? with
      | some source => .ok source
      | none => .error "SELECT has no source table"
    unless source.schema.isNone && source.functionArgs.isNone && source.subquerySql.isNone && source.joinOn.isNone do
      throw "unsupported general verified-MVP SQL: SELECT source"
    let tableName := resolveTableName state source.name
    let stored ← match state.database.findTable? tableName with
      | some stored => .ok stored
      | none => .error s!"no such table: {source.name}"
    if select.having.isSome then
      if !select.groupBy.isEmpty then return ← executeCollatedGroup state select source stored
      unless select.columns.any (fun column => CoreAggregate.containsAggregate column.expr) do
        unsupported "HAVING requires a supported aggregate query"
      return ← executeAggregateSelect state select source stored
    unless selectNamesBound stored.schema source select do
      if !select.groupBy.isEmpty then return ← executeCollatedGroup state select source stored
      let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := source.alias.getD source.name, storedTexts := state.catalog.storedTexts }
      if select.where_.any (CoreOrder.needsAliases ctx select.columns.toList) then
        unless selectNamesBound stored.schema source { select with where_ := none } do
          if let some message := selectResolutionError stored.schema source { select with where_ := none } then throw message
          unsupported "unbound SELECT result or ordering name"
        let resolved := { select with where_ := select.where_.map (CoreOrder.resolveAliases ctx select.columns.toList) }
        return ← executeExpressionSelect state resolved source stored none
      if let some message := selectResolutionError stored.schema source select then throw message
      unsupported "unbound SELECT name"
    match select.where_.mapM (predicate stored.schema) with
    | .error _ => executeExpressionSelect state select source stored none
    | .ok wherePredicate => do
      if !select.groupBy.isEmpty then
        if select.distinct || !select.orderBy.isEmpty || select.limit.isSome || select.offset != 0 then
          executeCollatedGroup state select source stored
        else
          match groupColumns stored.schema select.groupBy.toList with
          | .error _ => executeCollatedGroup state select source stored
          | .ok groups =>
              match groupOutputs stored.schema groups select.columns.toList with
              | .error _ => executeCollatedGroup state select source stored
              | .ok outputs => do
                  let query : Core.GroupQuery := { groupBy := groups, outputs, predicate := wherePredicate }
                  let (next, result) ← Core.execute state (.group tableName query)
                  return ⟨next, result, query.outputs.length⟩
      else
        match ← countTarget? stored.schema select.columns.toList,
            ← sumColumn? stored.schema select.columns.toList,
            ← extremeColumn? stored.schema select.columns.toList with
        | some target, none, none =>
          if select.distinct || !select.orderBy.isEmpty || select.limit.isSome || select.offset != 0 then
            executeAggregateSelect state select source stored
          else
            let (next, result) ← Core.execute state (.count tableName target wherePredicate)
            return ⟨next, result, 1⟩
        | none, some column, none =>
          if select.distinct || !select.orderBy.isEmpty || select.limit.isSome || select.offset != 0 then
            executeAggregateSelect state select source stored
          else
            let (next, result) ← Core.execute state (.sum tableName column wherePredicate)
            return ⟨next, result, 1⟩
        | none, none, some (minimum, column) =>
          if select.distinct || !select.orderBy.isEmpty || select.limit.isSome || select.offset != 0 then
            executeAggregateSelect state select source stored
          else
            let (next, result) ← Core.execute state
              (.extreme tableName minimum column wherePredicate)
            return ⟨next, result, 1⟩
        | none, none, none =>
          match projection stored.schema select.columns.toList with
          | .error _ => executeExpressionSelect state select source stored wherePredicate
          | .ok columns =>
            match directOrdering stored.schema source select with
            | .error _ => executeFilteredSelect state select source stored
            | .ok ordering => do
              if select.offset != 0 || queryNeedsRepresentatives select.distinct columns ordering then
                executeFilteredSelect state select source stored
              else
                let query : Core.Query := {
                  columns
                  predicate := wherePredicate
                  orderBy := ordering
                  limit := select.limit
                  distinct := select.distinct }
                let (next, result) ← Core.execute state (.query tableName query)
                return ⟨next, result, query.columns.length⟩
        | _, _, _ => unsupported "ambiguous aggregate projection"

/-- Recognize the non-aggregate single-table SELECT shape used by the
persisted-index adapter. Returning `none` is only an optimization miss: normal
Core execution remains authoritative for every statement. -/
def simpleQuery? (state : Core.State) (select : Select) :
    Option (String × Core.Query) := do
  if select.compounds.isEmpty && select.sources.size = 1 &&
      select.groupBy.isEmpty && select.having.isNone && select.offset = 0 then
    let source ← select.sources[0]?
    if source.schema.isNone && source.functionArgs.isNone && source.subquerySql.isNone && source.joinOn.isNone then
      let tableName := resolveTableName state source.name
      let stored ← state.database.findTable? tableName
      unless selectNamesBound stored.schema source select do none
      let wherePredicate ← (select.where_.mapM (predicate stored.schema)).toOption
      let count ← (countTarget? stored.schema select.columns.toList).toOption
      let sum ← (sumColumn? stored.schema select.columns.toList).toOption
      let extreme ← (extremeColumn? stored.schema select.columns.toList).toOption
      if count.isNone && sum.isNone && extreme.isNone then
        let columns ← (projection stored.schema select.columns.toList).toOption
        let ordering ← (directOrdering stored.schema source select).toOption
        if queryNeedsRepresentatives select.distinct columns ordering then none
        else some (tableName, {
          columns
          predicate := wherePredicate
          orderBy := ordering
          limit := select.limit
          distinct := select.distinct })
      else none
    else none
  else none

/-- Explicit result collations are the only reason the currently supported
BINARY schemas need a different compound comparator. Predicate collations do
not affect the result-column collation. -/
def resultCollationFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, select =>
      select.columns.any (fun column => (SQLite.ExprCollation.name column.expr).isSome) ||
        (select.sources.isEmpty && select.valueRows.any (fun rows => rows.any (fun row =>
          row.any (fun expression => (SQLite.ExprCollation.name expression).isSome)))) ||
        select.compounds.any (fun arm => resultCollationFuel fuel arm.2)

/-- Bound declarations also choose the compound comparator. Keep the
explicit-only detector separate for source-free BINARY translation claims. -/
def declaredResultCollationFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, select =>
      select.columns.any (fun column =>
        (SQLite.ExprCollation.declaredNameFuel column.expr.height column.expr).isSome) ||
        (select.sources.isEmpty && select.valueRows.any (fun rows => rows.any (fun row =>
          row.any (fun expression => (SQLite.ExprCollation.declaredNameFuel expression.height expression).isSome)))) ||
        select.compounds.any (fun (_,arm) => declaredResultCollationFuel fuel arm)

def requiresCompoundCollation (select : Select) : Bool :=
  !select.compounds.isEmpty && (resultCollationFuel select.compoundHeight select ||
    declaredResultCollationFuel select.compoundHeight select)

theorem requiresCompoundCollation_no_compounds (select : Select)
    (ordinary : select.compounds.isEmpty = true) : requiresCompoundCollation select = false := by
  simp [requiresCompoundCollation, ordinary]

/-- These expression identities are internal bound slots, not SQL names.
FULL's merged column is distinct from either source and from an explicit
coalesce() call, as in SQLite's expression comparison. -/
def joinCompoundOperand : CoreJoin.Operand → Expr
  | .column reference | .coercedColumn _ reference =>
      .column (some (if reference.side == .left then "left" else "right")) (toString reference.column)
  | .mergedColumn _ left right => .column (some "merged") s!"{left}:{right}"
  | .literal value => .literal (match value with
      | .null => .null
      | .integer i => .integer i.value
      | .realBits bits => .real (Float.ofBits (UInt64.ofNat bits.val))
      | .blob payload => .blob payload.bytes.toArray
      | .text payload => match String.fromUTF8? (ByteArray.mk payload.bytes.toArray) with
          | some text => .text text
          | none => .textBytes payload.bytes.toArray)

theorem joinCompoundOperand_sides (left right : Nat) :
    joinCompoundOperand (.column ⟨.left, left⟩) ≠
      joinCompoundOperand (.column ⟨.right, right⟩) := by
  simp [joinCompoundOperand]

theorem joinCompoundOperand_merged (left right index : Nat) :
    joinCompoundOperand (.mergedColumn none left right) ≠
      joinCompoundOperand (.column ⟨.left, index⟩) := by
  simp [joinCompoundOperand]

/-- Bind every reference before comparing ASTs. Unknown and ambiguous source
names fail; qualifiers cannot accidentally name an internal result slot. -/
def joinCompoundBindFuel (context : JoinContext) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, expression => do
      let bind := joinCompoundBindFuel context fuel
      match expression with
      | .column qualifier name =>
          match joinNamedOperand context qualifier name with
          | .ok operand => some (joinCompoundOperand operand)
          | .error _ => none
      | .literal .. => some expression
      | .unary op arg => return .unary op (← bind arg)
      | .binary op left right => return .binary op (← bind left) (← bind right)
      | .call name args star => return .call name (← args.mapM bind) star
      | .isNull arg negated => return .isNull (← bind arg) negated
      | .inList arg values negated affinity =>
          return .inList (← bind arg) (← values.mapM bind) negated affinity
      | .collate arg name => return .collate (← bind arg) name
      | .case_ base branches otherwise =>
          return .case_ (← base.mapM bind)
            (← branches.mapM fun (condition, result) => do return (← bind condition, ← bind result))
            (← otherwise.mapM bind)
      | _ => none

def joinCompoundBind (context : JoinContext) (expression : Expr) : Option Expr :=
  let expression := SQLite.Scalar.prepare (joinBindNames context expression)
  joinCompoundBindFuel context expression.height expression

def joinCompoundStarReferences (context : JoinContext) (qualifier : Option String) :
    Except String (List CoreJoin.ColumnRef) :=
  match qualifier with
  | none => .ok (joinVisibleColumns .left context.leftSchema ++
      (joinVisibleColumns .right context.rightSchema).filter
        (fun reference => !CoreJoinUsing.suppressesRight context.shared reference.column))
  | some qualifier =>
      if canonical qualifier == context.leftName then
        .ok (joinVisibleColumns .left context.leftSchema)
      else if canonical qualifier == context.rightName then
        .ok (joinVisibleColumns .right context.rightSchema)
      else .error s!"no such table or alias: {qualifier}"

def joinCompoundStarColumns (context : JoinContext) (qualifier : Option String) :
    Except String (List ResultColumn) := do
  let references ← joinCompoundStarReferences context qualifier
  return references.map fun reference =>
    let schema := if reference.side == .left then context.leftSchema else context.rightSchema
    { expr := joinCompoundOperand (joinStarOperand context reference)
      alias := (schema.columns[reference.column]?).map (·.name) }

/-- Every expanded star has exactly the live join projection's bound values,
in the same positions; output labels do not change these identities. -/
theorem joinCompoundStarColumns_projection (context : JoinContext) (qualifier : Option String) :
    (joinCompoundStarColumns context qualifier).map (List.map (·.expr)) =
      (joinResultExpr context (.star qualifier)).map (List.map joinCompoundOperand) := by
  cases qualifier with
  | none => simp [joinCompoundStarColumns, joinCompoundStarReferences, joinResultExpr,
      bind, Except.bind, Except.map, pure, Except.pure, List.map_map, Function.comp_def]
  | some qualifier =>
      by_cases left : canonical qualifier == context.leftName
      · simp [joinCompoundStarColumns, joinCompoundStarReferences, joinResultExpr, left,
          bind, Except.bind, Except.map, pure, Except.pure, List.map_map, Function.comp_def]
      · by_cases right : canonical qualifier == context.rightName
        · simp [joinCompoundStarColumns, joinCompoundStarReferences, joinResultExpr, left, right,
            bind, Except.bind, Except.map, pure, Except.pure, List.map_map, Function.comp_def,
            joinVisibleColumns, joinStarOperand, joinMergedStar]
        · simp [joinCompoundStarColumns, joinCompoundStarReferences, joinResultExpr, left, right,
            bind, Except.bind, Except.map]

def joinCompoundColumns (context : JoinContext) : List ResultColumn → Except String (List ResultColumn)
  | [] => .ok []
  | column :: columns => do
      let head ← match column.expr with
        | .star qualifier => joinCompoundStarColumns context qualifier
        | expression => do
            let some bound := joinCompoundBind context expression
              | throw "unbound joined result expression"
            pure [{ column with expr := bound }]
      return head ++ (← joinCompoundColumns context columns)

def joinScalarInputs (context : JoinContext) : List CoreJoin.Operand :=
  (joinSideColumns .left context.leftSchema.columns.length ++
    joinSideColumns .right context.rightSchema.columns.length).map .column ++
  context.shared.map (fun shared => .mergedColumn none shared.left shared.right)

def joinScalarSlot (index : Nat) : Expr := .column none s!"__joined_{index}"

def joinScalarOperand (context : JoinContext) (operand : CoreJoin.Operand) : Option Expr :=
  (joinScalarInputs context).findIdx? (· == operand) |>.map joinScalarSlot

def joinScalarBindFuel (context : JoinContext) : Nat → Expr → Option Expr
  | 0, _ => none
  | fuel + 1, expression => do
      let bind := joinScalarBindFuel context fuel
      match expression with
      | .column qualifier name =>
          joinScalarOperand context (← (joinNamedOperand context qualifier name).toOption)
      | .literal .. => some expression
      | .unary op arg => return .unary op (← bind arg)
      | .binary op left right => return .binary op (← bind left) (← bind right)
      | .call name args star => return .call name (← args.mapM bind) star
      | .isNull arg negated => return .isNull (← bind arg) negated
      | .inList arg values negated affinity =>
          return .inList (← bind arg) (← values.mapM bind) negated affinity
      | .collate arg name => return .collate (← bind arg) name
      | .case_ base branches otherwise =>
          return .case_ (← base.mapM bind)
            (← branches.mapM fun (condition, result) => do return (← bind condition, ← bind result))
            (← otherwise.mapM bind)
      | _ => none

end CoreSQL

end SQLeanite
