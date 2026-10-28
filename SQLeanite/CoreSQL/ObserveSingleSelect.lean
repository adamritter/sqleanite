import SQLeanite.CoreAutoIncrement
import SQLeanite.CoreIndexPrepare
import SQLeanite.CoreInsertPrepare
import SQLeanite.CoreLastInsert
import SQLeanite.CoreSQL.JoinStreamPrepared

namespace SQLeanite
namespace CoreSQL

/-- Successful reads retain the existing optimized file route. On a failed
single-source read, publish its prefix only when the observation
reproduces that same failure. The original execution remains authoritative;
this consistency check cannot admit an unsupported query or suppress an error. -/
def observeSingleSelect? (state : Core.State) (select : Select) : Option ObservedSelect :=
  if select.sources.size = 1 ∧ select.compounds = #[] ∧ simpleQuery? state select = none then
    match executeSelectBase state select with
    | .ok _ => none
    | .error message =>
        let report := singleSourceReadReport state select
        if report.error = some message then
          some { execution := ⟨state, report.result, report.width⟩, error := report.error }
        else none
  else none

theorem observeSingleSelect_refines (state : Core.State) (select : Select)
    (report : ObservedSelect) (observed : observeSingleSelect? state select = some report) :
    report.toExcept = executeSelect state select := by
  unfold observeSingleSelect? at observed
  split at observed
  next supported =>
    cases base : executeSelectBase state select with
    | ok execution => simp [base] at observed
    | error message =>
        simp only [base] at observed
        split at observed
        next sameFailure =>
          cases Option.some.inj observed
          rw [executeSelect_without_compounds state select supported.2.1]
          simp [ObservedSelect.toExcept, sameFailure, executeSelectBaseComplete, supported.1, base]
        next different => simp at observed
  next unsupported => simp at observed

/-- A translated direct Core query keeps the existing file/index route
without evaluating the ordinary SELECT merely to obtain an observation. -/
theorem observeSingleSelect_direct (state : Core.State) (select : Select)
    (query : String × Core.Query) (direct : simpleQuery? state select = some query) :
    observeSingleSelect? state select = none := by
  simp [observeSingleSelect?, direct]

def observeReadSelect? (state : Core.State) (select : Select) : Option ObservedSelect :=
  (observeJoinedSelect? state select).orElse (fun _ => observeSingleSelect? state select)

theorem observeReadSelect_refines (state : Core.State) (select : Select)
    (report : ObservedSelect) (observed : observeReadSelect? state select = some report) :
    report.toExcept = executeSelect state select := by
  cases joined : observeJoinedSelect? state select with
  | none =>
      apply observeSingleSelect_refines state select report
      simpa [observeReadSelect?, joined] using observed
  | some result =>
      have equal : result = report := by simpa [observeReadSelect?, joined] using observed
      subst result
      exact observeJoinedSelect_refines state select report joined

/-- A declared non-rowid key also needs the allocate-before-delete REPLACE
trace, even when its automatic index is the only unique index. -/
def hasReplaceKeys (stored : Core.Table) : Bool :=
  (stored.schema.hasHiddenRowid && stored.schema.declaredPrimaryKey?.isSome) ||
    stored.indexes.any (·.unique) || stored.schema.columns.any (fun column => column.notNull && column.defaultValue.isSome)

/-- Allocate the replacement rowid against the original table, then remove
all rows conflicting with the primary key or any explicit UNIQUE index. -/
def uniqueReplacePlan (stored : Core.Table) (values : List Core.Value) :
    Except String (List Core.Command) := do
  CoreNullConflict.validate stored.schema (List.range stored.schema.columns.length) (some .replace)
  let some values ← CoreNullConflict.prepare stored.schema values false (some .replace)
    | throw "unexpected ignored REPLACE row"
  let row ← stored.createRow values
  let declared := stored.findDeclaredPrimary? row
  let conflicts := stored.rows.filter fun existing =>
    existing.rowid == row.rowid || declared.any (fun old => old.rowid == existing.rowid) ||
      stored.indexes.any (fun index => index.rowConflict row existing)
  let deletes := conflicts.map fun old => Core.Command.deleteWhere stored.schema.name
    (some (.equal stored.schema.primaryKey (.integer old.rowid)))
  return deletes ++ [.insert stored.schema.name row.values]

def replaceUniqueRows (state : Core.State) (table : String)
    (schema : Core.Schema) (columns : Option (Array String))
    (inputs : List (Array Expr)) (evaluateAll : Bool := false) :
    Except String (Core.State × List Core.Result) :=
  match inputs with
  | [] => .ok (state, [])
  | expressions :: rows => do
      let values ← inputRowValues schema columns evaluateAll expressions
      let stored ← match state.database.findTable? table with
        | some stored => .ok stored
        | none => .error s!"no such table: {table}"
      let commands ← uniqueReplacePlan stored values
      let (next, _) ← runCoreCommands state commands
      let (finalState, results) ← replaceUniqueRows next table schema columns rows evaluateAll
      return (finalState, { changes := 1 } :: results)

/-- Validate target arity even if the source SELECT yields no rows. -/
def checkInsertSelectColumns (schema : Core.Schema) (columns : Option (Array String))
    (width : Nat) (implicitWidth : Option Nat := none) : Except String Unit := do
  if let some expected := implicitWidth then
    unless width == expected do
      throw s!"table {schema.name} has {expected} columns but {width} values were supplied"
    return ()
  match columns with
  | none =>
      unless width == schema.visibleColumns.length do
        throw s!"table {schema.name} has {schema.visibleColumns.length} columns but {width} values were supplied"
  | some names =>
      let _ ← names.toList.mapM (column schema)
      unless width == names.size do throw s!"{width} values for {names.size} columns"

/-- Convert an already evaluated source row without rendering SQL text. This
retains storage classes and malformed TEXT bytes through the existing bridge. -/
def selectedRowExpressions (values : List Core.Value) : Except String (Array Expr) := do
  let values ← values.mapM CoreExpr.value
  return (values.map (fun value => Expr.literal value)).toArray

def insertSelection (state : Core.State) (table : String) (stored : Core.Table)
    (columns : Option (Array String)) (replacing : Bool)
    (rows : List (Array Expr)) : Except String (Core.State × List Core.Result) :=
  if replacing && hasReplaceKeys stored then
    replaceUniqueRows state table stored.schema columns rows
  else insertRows state table stored.schema columns replacing rows

theorem insertSelection_empty (state : Core.State) (table : String) (stored : Core.Table)
    (columns : Option (Array String)) (replacing : Bool) :
    insertSelection state table stored columns replacing [] = .ok (state, []) := by
  unfold insertSelection
  split <;> rfl

/-- Constant omitted defaults are initialized even for an empty SELECT source.
Replacement defaults are prepared without executing their runtime expressions. -/
def prepareInsertSelectionDefaults (schema : Core.Schema) (columns : Option (Array String))
    (conflict : ConflictAction) : Except String Unit := do
  if let some names := columns then
    let positions ← names.toList.mapM (column schema)
    for (target, position) in schema.columns.zipIdx do
      unless positions.contains position do discard <| target.defaultForInsert
  if conflict == .default || conflict == .replace then
    CoreNullConflict.validate schema (List.range schema.columns.length) (if conflict == .replace then some .replace else none)

/-- Evaluate the SELECT against the pre-statement database before inserting
its rows, including when the source is the destination table. All writes then
use the ordinary INSERT affinity, rowid and conflict-policy machinery. -/
def executeInsertSelect (state : Core.State) (table : String)
    (columns : Option (Array String)) (query : Select) (conflict : ConflictAction) :
    Except String (Core.State × List Core.Result) := do
  unless conflict == .default || conflict == .abort || conflict == .replace || conflict == .ignore do
    throw "unsupported general verified-MVP SQL: INSERT conflict policy"
  let tableName := resolveTableName state table
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  let selection ← executeSelect state query
  checkInsertSelectColumns stored.schema columns selection.width
  prepareInsertSelectionDefaults stored.schema columns conflict
  let rows ← selection.result.rows.mapM selectedRowExpressions
  if conflict == .default && CoreDefaultConflict.active stored.schema then
    schemaInsertRows state tableName stored.schema columns rows
  else if conflict == .ignore then ignoreInsertRows state tableName stored.schema columns rows
  else insertSelection state tableName stored columns (conflict == .replace) rows

theorem checkInsertSelectColumns_all {schema : Core.Schema} {width : Nat}
    (same : width = schema.visibleColumns.length) :
    checkInsertSelectColumns schema none width = .ok () := by
  simp [checkInsertSelectColumns, same, pure, Except.pure]

/-- Materialize RETURNING immediately for each accepted insertion. REPLACE
may later delete that row, but it must not erase its already collected output.
Ignored rows produce no output and do not evaluate RETURNING expressions. -/
def insertReturningValues (state : Core.State) (tableName : String) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (cells : List CoreReturning.Cell)
    (preparation : Option RowPreparation := none) :
    Except String (Core.State × Option (List Core.Value)) := do
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {tableName}"
  let some input ← (match preparation with
    | none => pure (some ({ cells, converted := List.range stored.schema.columns.length } : RowInput))
    | some prepare => prepare.row state stored conflict { cells, converted := List.range stored.schema.columns.length })
    | return (state, none)
  let cells := input.cells
  let values := cells.map (·.value)
  if conflict == .default then
    CoreDefaultConflict.validate stored none
    let some cells ← CoreReturning.prepareValues stored.schema cells false | return (state, none)
    let prepared ← CoreDefaultConflict.plan stored (cells.map (·.value)) none
    match prepared with
    | none => return (state, none)
    | some (row, trace) =>
        let (next, _) ← runCoreCommands state trace
        let output ← CoreReturning.project ctx (CoreReturning.withValues cells row.values)
          (projection.map (CoreLastInsert.bind next))
        return (next.recordForeignWrite tableName row.rowid none, some output)
  if conflict == .ignore then
    unless ← CoreInsertIgnore.shouldInsert stored values do return (state, none)
  let cells ← if conflict == .replace || conflict == .abort then do
      let some prepared ← CoreReturning.prepareValues stored.schema cells false
        (some (if conflict == .replace then .replace else .abort))
        | throw "unexpected ignored checked insertion"
      pure prepared
    else pure cells
  let row ← stored.createRow (cells.map (·.value))
  let trace ← if conflict == .replace then uniqueReplacePlan stored row.values
    else pure [Core.Command.insert tableName row.values]
  let (next, _) ← runCoreCommands state trace
  let output ← CoreReturning.project ctx (CoreReturning.withValues cells row.values)
          (projection.map (CoreLastInsert.bind next))
  return (next.recordForeignWrite tableName row.rowid none, some output)

/-- Only omitted target fields share default registers. Source values and
NOT NULL replacement defaults are evaluated in their own row registers. -/
def insertDefaultRegisters (schema : Core.Schema) (columns : Option (Array String))
    (input : Array Expr) (cells : List CoreReturning.Cell) : List (Option CoreReturning.Cell) :=
  let supplied := if input.isEmpty then [] else
    match columns with
    | none => schema.visibleColumnIndices
    | some names => names.toList.filterMap schema.column?
  cells.zipIdx.map fun (value,index) => if supplied.contains index then none else some value

def insertReturningStep (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (input : Array Expr)
    (evaluateAll : Bool) (defaults : List (Option CoreReturning.Cell))
    (preparation : Option RowPreparation := none) :
    Except String (Core.State × Option (List Core.Value) × List (Option CoreReturning.Cell)) := do
  let cells ← inputRowValuesTyped schema columns evaluateAll (input.map (CoreLastInsert.bind state)) defaults
  let (next, output) ← insertReturningValues state tableName conflict ctx projection cells preparation
  let defaults := if output.isSome then insertDefaultRegisters schema columns input cells else defaults
  return (next, output, defaults)

def insertReturningRow (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (input : Array Expr)
    (evaluateAll : Bool := false) (preparation : Option RowPreparation := none) :
    Except String (Core.State × Option (List Core.Value)) :=
  (fun result => (result.1,result.2.1)) <$>
    insertReturningStep state tableName schema columns conflict ctx projection input evaluateAll [] preparation

theorem insertReturningRow_ignored (state : Core.State) (tableName : String)
    (schema : Core.Schema) (columns : Option (Array String)) (ctx : CoreExpr.Context)
    (projection : List Expr) (input : Array Expr) (values : List CoreReturning.Cell) (stored : Core.Table)
    (converted : rowValuesTyped schema columns (input.map (CoreLastInsert.bind state)) = .ok values)
    (found : state.database.findTable? tableName = some stored)
    (skip : CoreInsertIgnore.shouldInsert stored (values.map (·.value)) = .ok false) :
    insertReturningRow state tableName schema columns .ignore ctx projection input = .ok (state, none) := by
  simp [insertReturningRow, insertReturningStep, inputRowValuesTyped, insertReturningValues,
    converted, found, skip, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

def insertReturningRows (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr)
    (inputs : List (Array Expr)) (evaluateAll : Bool := false)
    (defaults : List (Option CoreReturning.Cell) := []) (preparation : Option RowPreparation := none) :
    Except String (Core.State × List (List Core.Value)) :=
  match inputs with
  | [] => .ok (state, [])
  | input :: inputs => do
      let (next, output, defaults) ← insertReturningStep state tableName schema columns conflict
        ctx projection input evaluateAll defaults preparation
      let (finalState, outputs) ← insertReturningRows next tableName schema columns conflict
        ctx projection inputs evaluateAll defaults preparation
      return (finalState, output.toList ++ outputs)

theorem insertReturningRows_length_le (state : Core.State) (tableName : String)
    (schema : Core.Schema) (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (inputs : List (Array Expr))
    (next : Core.State) (outputs : List (List Core.Value)) (evaluateAll : Bool)
    (defaults : List (Option CoreReturning.Cell))
    (success : insertReturningRows state tableName schema columns conflict ctx projection inputs evaluateAll defaults = .ok (next, outputs)) :
    outputs.length ≤ inputs.length := by
  induction inputs generalizing state next outputs defaults with
  | nil =>
      simp [insertReturningRows] at success
      rcases success with ⟨_, rfl⟩
      simp
  | cons input inputs ih =>
      cases head : insertReturningStep state tableName schema columns conflict ctx projection input evaluateAll defaults with
      | error message => simp [insertReturningRows, head, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨middle, output, registers⟩
          cases tail : insertReturningRows middle tableName schema columns conflict ctx projection inputs evaluateAll registers with
          | error message => simp [insertReturningRows, head, tail, bind, Except.bind] at success
          | ok pair =>
              rcases pair with ⟨finalState, more⟩
              simp [insertReturningRows, head, tail, bind, Except.bind, pure, Except.pure] at success
              rcases success with ⟨_, rfl⟩
              have bound := ih middle finalState more registers tail
              cases output <;> simp_all <;> omega

def executeInsertReturning (state : Core.State) (table : String) (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) (conflict : ConflictAction) (returning : Array ResultColumn)
    (preparation : Option RowPreparation := none) :
    Except String (Core.State × List Core.Result) := do
  unless conflict == .default || conflict == .abort || conflict == .replace || conflict == .ignore do
    throw "unsupported general verified-MVP SQL: INSERT conflict policy"
  let tableName := resolveTableName state table
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  let ctx : CoreExpr.Context := { schema := stored.schema, rowidAliases := !stored.withoutRowid, sourceName := tableName, internalProjection := state.internalReturning }
  let targets ← prepareInsertTargets columns source preparation
  let columns := targets.columns
  if let .inl rows := source then CoreInsertPrepare.check stored.schema columns rows targets.implicitWidth
  let projection ← CoreLastInsert.prepareReturning state ctx returning.toList
  let inputs ← match source with
    | .inl rows => pure (if returning.isEmpty then rows.toList else
        rows.toList.map (·.map (CoreLastInsert.bind state)))
    | .inr query => do
        let selection ← executeSelect state query
        checkInsertSelectColumns stored.schema columns selection.width targets.implicitWidth
        prepareInsertSelectionDefaults stored.schema columns conflict
        selection.result.rows.mapM selectedRowExpressions
  let evaluateAll := match source with
    | .inl rows => 1 < rows.size
    | .inr _ => false
  let (next, outputs) ← insertReturningRows state tableName stored.schema columns conflict ctx projection inputs evaluateAll [] preparation
  return (next, [{ rows := if returning.isEmpty then [] else outputs, changes := outputs.length }])

/-- AUTOINCREMENT candidates use the existing checked conflict/RETURNING
executor after an explicit rowid has been allocated. The private counter is
threaded through ignored rows, without exposing it to the statement's SELECT. -/
def autoInsertRows (state : Core.State) (tableName : String) (schema : Core.Schema)
    (columns : Option (Array String)) (conflict : ConflictAction)
    (ctx : CoreExpr.Context) (projection : List Expr) (counter : CoreAutoIncrement.Context)
    (inputs : List (Array Expr)) (evaluateAll : Bool)
    (defaults : List (Option CoreReturning.Cell) := []) (preparation : Option RowPreparation := none) :
    Except String (Core.State × CoreAutoIncrement.Context × List (Option (List Core.Value))) :=
  match inputs with
  | [] => .ok (state, counter, [])
  | input :: inputs => do
      let cells ← inputRowValuesTyped schema columns evaluateAll (input.map (CoreLastInsert.bind state)) defaults
      let stored ← match state.database.findTable? tableName with
        | some stored => pure stored
        | none => throw s!"no such table: {tableName}"
      let (counter, values) ← CoreAutoIncrement.prepare stored counter (cells.map (·.value))
      let (next, output) ← insertReturningValues state tableName conflict ctx projection
        (CoreReturning.withValues cells values) preparation
      let defaults := if output.isSome then insertDefaultRegisters schema columns input cells else defaults
      let (finalState, finalCounter, outputs) ← autoInsertRows next tableName schema columns conflict
        ctx projection counter inputs evaluateAll defaults preparation
      return (finalState, finalCounter, output :: outputs)

def executeAutoInsert (state : Core.State) (table : String) (columns : Option (Array String))
    (source : Sum (Array (Array Expr)) Select) (conflict : ConflictAction) (returning : Array ResultColumn)
    (preparation : Option RowPreparation := none) :
    Except String (Core.State × List Core.Result) := do
  unless conflict == .default || conflict == .abort || conflict == .replace || conflict == .ignore do
    throw "unsupported general verified-MVP SQL: INSERT conflict policy"
  let tableName := resolveTableName state table
  let stored ← match state.database.findTable? tableName with
    | some stored => pure stored
    | none => throw s!"no such table: {table}"
  let counter ← CoreAutoIncrement.beginContext state tableName
  let ctx : CoreExpr.Context := { schema := stored.schema, rowidAliases := !stored.withoutRowid, sourceName := tableName, internalProjection := state.internalReturning }
  let targets ← prepareInsertTargets columns source preparation
  let columns := targets.columns
  if let .inl rows := source then CoreInsertPrepare.check stored.schema columns rows targets.implicitWidth
  let projection ← CoreLastInsert.prepareReturning state ctx returning.toList
  let inputs ← match source with
    | .inl rows => pure (if returning.isEmpty then rows.toList else
        rows.toList.map (·.map (CoreLastInsert.bind state)))
    | .inr query => do
        let selection ← executeSelect state query
        checkInsertSelectColumns stored.schema columns selection.width targets.implicitWidth
        prepareInsertSelectionDefaults stored.schema columns conflict
        selection.result.rows.mapM selectedRowExpressions
  let evaluateAll := match source with
    | .inl rows => 1 < rows.size
    | .inr _ => false
  let (next, counter, outputs) ← autoInsertRows state tableName stored.schema columns conflict ctx projection
    counter inputs evaluateAll [] preparation
  let next ← CoreAutoIncrement.finish next counter
  if returning.isEmpty then
    let results : List Core.Result := outputs.map fun output => { changes := if output.isSome then 1 else 0 }
    return (next, results)
  else
    let rows := outputs.flatMap Option.toList
    return (next, [{ rows, changes := rows.length }])

def automaticTable (state : Core.State) (name : String) : Bool :=
  (state.database.findTable? (resolveTableName state name)).any (fun stored => stored.schema.autoIncrement)

/-- The checked source loop shares one interpreter across pure and effectful
callers. The emitter owns actual writes; source rows remain immutable. -/
def insertRegisterRowsWith {m : Type → Type} [Monad m] [MonadLiftT (Except String) m]
    (emit : Core.State → Array Expr → m (Core.State × List Core.Result))
    (state : Core.State) (ctx : CoreExpr.Context) (projection : List Expr)
    (condition : Option Expr) (rows : List Core.Row) (offset : Nat) (remaining : Option Nat)
    (distinct : Bool := false) (seen : List (List Core.Value) := []) :
    m (Core.State × List Core.Result) :=
  match rows with
  | [] => return (state, [])
  | row :: rows => do
      if remaining == some 0 then return (state, [])
      unless ← ctx.matches row.values (condition.map (CoreLastInsert.bind state)) do
        return ← insertRegisterRowsWith emit state ctx projection condition rows offset remaining distinct seen
      if offset > 0 && !distinct then
        return ← insertRegisterRowsWith emit state ctx projection condition rows (offset-1) remaining distinct seen
      let values ← ctx.projectRow row.values (projection.map (CoreLastInsert.bind state))
      if distinct && seen.any (CoreExpr.distinctEqual projection values) then
        return ← insertRegisterRowsWith emit state ctx projection condition rows offset remaining distinct seen
      let seen := if distinct then Core.distinctRowKey values :: seen else seen
      if offset > 0 then
        return ← insertRegisterRowsWith emit state ctx projection condition rows (offset-1) remaining distinct seen
      let input ← selectedRowExpressions values
      let (next, results) ← emit state input
      let (finalState, more) ← insertRegisterRowsWith emit next ctx projection condition rows 0
        (remaining.map (·-1)) distinct seen
      return (finalState, results ++ more)

/-- The ordinary Except API specializes the same source loop. -/
def insertRegisterRows (state : Core.State) (table : String) (columns : Option (Array String))
    (conflict : ConflictAction) (ctx : CoreExpr.Context) (projection : List Expr)
    (condition : Option Expr) (rows : List Core.Row) (offset : Nat) (remaining : Option Nat)
    (preparation : Option RowPreparation := none) (distinct : Bool := false) : Except String (Core.State × List Core.Result) :=
  insertRegisterRowsWith (fun current input =>
    if automaticTable current table then
      executeAutoInsert current table columns (.inl #[input]) conflict #[] preparation
    else executeInsertReturning current table columns (.inl #[input]) conflict #[] preparation)
    state ctx projection condition rows offset remaining distinct

theorem insertRegisterRows_limit_zero (state : Core.State) (table : String)
    (columns : Option (Array String)) (conflict : ConflictAction) (ctx : CoreExpr.Context)
    (projection : List Expr) (condition : Option Expr) (rows : List Core.Row) (offset : Nat) :
    insertRegisterRows state table columns conflict ctx projection condition rows offset (some 0) =
      .ok (state, []) := by
  cases rows <;> simp [insertRegisterRows, insertRegisterRowsWith, pure, Except.pure]

/-- A rowid-first order is satisfied by the source cursor, including aliases
and ordinals resolved by the ordinary ORDER compiler. Other orders need a sorter. -/
def registerDirection? (schema : Core.Schema) (source : TableRef) (query : Select) : Option Bool := do
  let terms ← (resolvedOrdering schema source query).toOption
  let some term := terms.head? | return false
  let ctx : CoreExpr.Context := { schema, sourceName := source.alias.getD source.name }
  match ctx.bindNames (CoreOrder.keyExpression term.expr) with
  | .column qualifier name =>
      unless ctx.column? qualifier name == some schema.primaryKey do none
      return term.descending
  | _ => none

structure RegisterSelection where
  columns : Option (Array String)
  context : CoreExpr.Context
  projection : List Expr
  rows : List Core.Row
  distinct : Bool := false

/-- Shared preparation for the external plain-table register coroutine. -/
def prepareRegisterSelection (state : Core.State) (table : String)
    (columns : Option (Array String)) (query : Select) (conflict : ConflictAction)
    (preparation : Option RowPreparation := none) : Except String RegisterSelection := do
  let source? := query.sources[0]?
  unless query.sources.size == 1 && query.compounds.isEmpty && query.valueRows.isNone &&
      query.groupBy.isEmpty && query.having.isNone && (!query.distinct || query.orderBy.isEmpty) do
    throw "unsupported connection-register INSERT SELECT plan"
  let some source := source? | throw "missing INSERT SELECT source"
  unless source.schema.isNone && source.functionArgs.isNone && source.subquerySql.isNone && source.joinOn.isNone do
    throw "unsupported connection-register INSERT SELECT source"
  let some stored := state.database.findTable? (resolveTableName state source.name)
    | throw s!"no such table: {source.name}"
  let some target := state.database.findTable? (resolveTableName state table)
    | throw s!"no such table: {table}"
  let ctx : CoreExpr.Context := { schema := stored.schema, rowidAliases := !stored.withoutRowid, sourceName := source.alias.getD source.name, storedTexts := state.catalog.storedTexts }
  let projection ← CoreLastInsert.prepareProjection state ctx query.columns.toList
  if query.distinct then CoreExpr.validateDistinct (projection.map (CoreLastInsert.bind state))
  let some reverse := registerDirection? stored.schema source query
    | throw "unsupported connection-register INSERT SELECT ordering"
  if let some condition := query.where_ then ctx.validate (CoreLastInsert.bind state condition)
  let targets ← prepareInsertTargets columns (.inr query) preparation
  let columns := targets.columns
  checkInsertSelectColumns target.schema columns projection.length targets.implicitWidth
  prepareInsertSelectionDefaults target.schema columns conflict
  return { columns, context := ctx, projection, rows := if reverse then stored.rows.reverse else stored.rows, distinct := query.distinct }

/-- RETURNING and a source reading its own destination require materialization.
External plain scans can interleave reading and writing, so binding the register
once at statement entry would give the wrong values. -/
def executeRegisterInsertSelect (state : Core.State) (table : String)
    (columns : Option (Array String)) (query : Select) (conflict : ConflictAction)
    (returning : Array ResultColumn) (preparation : Option RowPreparation := none) : Except String (Core.State × List Core.Result) := do
  let source? := query.sources[0]?
  let materialized := !returning.isEmpty || source?.any (fun source =>
    resolveTableName state source.name == resolveTableName state table)
  if materialized || (query.sources.isEmpty && query.compounds.isEmpty) then
    let bound := CoreLastInsert.select state query
    if automaticTable state table then return ← executeAutoInsert state table columns (.inr bound) conflict returning preparation
    if returning.isEmpty && preparation.isNone then return ← executeInsertSelect state table columns bound conflict
    return ← executeInsertReturning state table columns (.inr bound) conflict returning preparation
  let selection ← prepareRegisterSelection state table columns query conflict preparation
  insertRegisterRows state table selection.columns conflict selection.context selection.projection query.where_
    selection.rows query.offset query.limit preparation selection.distinct

abbrev indexNameExists := CoreIndexPrepare.indexNameExists

def prepareCreateTable (state : Core.State) (name : String) (ifNotExists : Bool) :
    Except String Bool := do
  if (canonical name).startsWith "sqlite_" then throw s!"object name reserved for internal use: {name}"
  if (CoreNames.table? state.database name).isSome then
    if ifNotExists then return false else throw s!"table already exists: {name}"
  if indexNameExists state name then throw s!"there is already an index named {name}"
  return true

end CoreSQL

end SQLeanite
