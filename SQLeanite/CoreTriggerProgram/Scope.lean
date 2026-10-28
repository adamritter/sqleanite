import SQLeanite.CoreTriggerProgram.Effects
import SQLeanite.CoreTriggerProgram.ReturnPrepare
import SQLeanite.CoreGeneratedSQL

namespace SQLeanite.CoreTriggerProgram

abbrev PrepareExecutor := Core.State → List CoreScalarQuery.Frame → Statement → Except String Unit

def conflict : Statement → ConflictAction
  | .insert _ _ _ action _ | .insertSelect _ _ _ action _ | .update _ _ _ _ action _ => action
  | _ => .default

/-- An explicit outer OR policy controls statements in its trigger programs.
With no outer policy, each body statement keeps its own declared policy. -/
def inheritConflict (outer : ConflictAction) (statement : Statement) : Statement :=
  if outer == .default then statement else match statement with
  | .insert table columns rows _ outputs => .insert table columns rows outer outputs
  | .insertSelect table columns query _ outputs => .insertSelect table columns query outer outputs
  | .update table alias assignments condition _ outputs => .update table alias assignments condition outer outputs
  | other => other

def captured (statement : Statement) : Bool :=
  let has := fun expression => !(CoreScalarQuery.captures expression.height expression).isEmpty
  match statement with
  | .insert _ _ rows .. => rows.any (·.any has)
  | .update _ _ assignments condition .. => assignments.any (fun pair => has pair.2) || condition.any has
  | .delete _ _ condition .. => condition.any has
  | _ => false

def tableFor (state : Core.State) (name : String) : Except String Core.Table := do
  let some table := CoreNames.table? state.database name | throw s!"no such table: main.{name}"
  return table

def insertArity (state : Core.State) (table : Core.Table) (columns : Option (Array String))
    (query : Select) (width : Nat) : Except String Unit := do
  let preparation ← CoreGeneratedSQL.preparation state table.schema.name
  let targets ← CoreSQL.prepareInsertTargets columns (.inr query) preparation
  CoreSQL.checkInsertSelectColumns table.schema targets.columns width targets.implicitWidth

/-- Preparation executes no projected values. Captured SQL is compiled with
actual lexical parent schemas, rather than rewritten into generated SQL text. -/
def prepareBody (base : Executor) (read : ScopedRead) (state : Core.State)
    (parents : List CoreScalarQuery.Frame) (original : Statement) : Except String Unit := do
  let state := if parents.any (·.qualifiedOnly) then { state with triggerDepth := max 1 state.triggerDepth } else state
  match original with
  | .select query =>
      discard <| read true state parents { query with limit := some 0 }
      return ()
  | .insertSelect target columns query _ outputs =>
      let table ← tableFor state target
      let selected ← read true state parents { query with limit := some 0 }
      insertArity state table columns query selected.width
      discard <| prepareReturning read state table target outputs
      return ()
  | _ => pure ()
  if captured original then
    match original with
    | .insert target columns rows _ outputs =>
        let table ← tableFor state target
        let dummy := rows.map (·.map fun _ => Expr.literal .null)
        let preparation ← CoreGeneratedSQL.preparation state target
        let targets ← CoreSQL.prepareInsertTargets columns (.inl rows) preparation
        CoreInsertPrepare.check table.schema targets.columns dummy targets.implicitWidth
        for row in rows do
          discard <| read true state parents { columns := row.map fun expr => { expr }, limit := some 0 }
        discard <| prepareReturning read state table target outputs
    | .update target alias assignments condition action outputs =>
        discard <| read true state parents {
          columns := assignments.map fun pair => { expr := pair.2 }
          sources := #[{ name := target, alias }]
          where_ := condition
          limit := some 0 }
        let dummy := assignments.map fun pair => (pair.1,Expr.literal .null)
        let table ← tableFor state target
        discard <| prepareReturning read state table target outputs
        discard <| base state (.update target alias dummy (some (.literal (.integer 0))) action #[]) ""
    | .delete target alias condition outputs =>
        discard <| read true state parents {
          columns := #[{ expr := .literal (.integer 1) }]
          sources := #[{ name := target, alias }]
          where_ := condition
          limit := some 0 }
        let table ← tableFor state target
        discard <| prepareReturning read state table target outputs
        discard <| base state (.delete target alias (some (.literal (.integer 0))) #[]) ""
    | _ => throw "unsupported captured trigger preparation"
    return ()
  let statement := CoreConnectionSQL.statement state (← bindStatement state parents original)
  match statement with
  | .update target alias assignments _ action outputs =>
      let table ← tableFor state target
      discard <| prepareReturning read state table target outputs
      discard <| base state (.update target alias assignments (some (.literal (.integer 0))) action #[]) ""
  | .delete target alias _ outputs =>
      let table ← tableFor state target
      discard <| prepareReturning read state table target outputs
      discard <| base state (.delete target alias (some (.literal (.integer 0))) #[]) ""
  | .insert target columns rows _ outputs =>
      let table ← tableFor state target
      let preparation ← CoreGeneratedSQL.preparation state target
      let targets ← CoreSQL.prepareInsertTargets columns (.inl rows) preparation
      CoreInsertPrepare.check table.schema targets.columns rows targets.implicitWidth
      discard <| prepareReturning read state table target outputs
  | _ => throw "unsupported trigger body preparation"

/-- A plain SELECT * over VALUES is a SQLite coroutine: later rows observe
last_insert_rowid from earlier insertions. Sorting/grouping and other read
shapes stay on the existing materialization path. -/
def streamingInput (query : Select) : Option (Array (Array Expr)) := do
  unless query.valueRows.isNone && query.where_.isNone && query.groupBy.isEmpty &&
      query.having.isNone && query.orderBy.isEmpty && !query.distinct &&
      query.limit.isNone && query.offset == 0 && query.compounds.isEmpty do none
  let [source] := query.sources.toList | none
  let [column] := query.columns.toList | none
  let .star qualifier := column.expr | none
  unless column.alias.isNone && qualifier.all (fun name => name.toLower == (source.alias.getD source.name).toLower) do none
  let sql ← source.subquerySql
  let parsed ← (CoreTokenGrammar.parseCertified sql).toOption
  match parsed.statements.toList with
  | [.values rows] => return rows
  | [.select inner] =>
      unless inner.sources.isEmpty && inner.where_.isNone && inner.groupBy.isEmpty &&
          inner.having.isNone && inner.orderBy.isEmpty && !inner.distinct &&
          inner.limit.isNone && inner.offset == 0 && inner.compounds.isEmpty do none
      inner.valueRows
  | _ => none

theorem streamingInput_ordered (query : Select) (ordered : query.orderBy.isEmpty = false) :
    streamingInput query = none := by
  simp [streamingInput, ordered]


/-- SELECT input is consumed as actual values by the ordinary INSERT executor.
Its private source state cannot replace the caller's database or registers. -/
def selectInput (read : ScopedRead) (state : Core.State) (parents : List CoreScalarQuery.Frame)
    (statement : Statement) : Except String Statement := do
  match statement with
  | .insertSelect target columns query action outputs =>
      if (programs state statement).isEmpty && outputs.isEmpty then
        if let some rows := streamingInput query then
          return .insert target columns rows action outputs
      let selected ← read false state parents query
      let rows ← selected.result.rows.mapM CoreSQL.selectedRowExpressions
      return .insert target columns rows.toArray action outputs
  | other => return other

def pointCondition (name : String) (key : Core.Integer) : Option Expr :=
  some (.binary .eq (.column none name) (.literal (.integer key.value)))

/-- Every target is resolved during preparation; runtime evaluates only the
last assignment to an actual column, including aliases of the same rowid. -/
def effectiveAssignments (schema : Core.Schema) (assignments : Array (String × Expr)) :
    Except String (Array (String × Expr)) := do
  let resolved ← assignments.toList.mapM fun pair => do
    return (← CoreSQL.column schema pair.1, pair)
  return (resolved.zipIdx.filterMap fun (entry,index) =>
    if (resolved.drop (index+1)).any (fun later => later.1 == entry.1) then none
    else some entry.2).toArray

def executeCapturedRows (execute : EffectExecutor) (read : ScopedRead) (state : Core.State)
    (parents : List CoreScalarQuery.Frame) (statement : Statement) : ExecutionM Core.State := do
  Execution.remember state
  let some target := CoreViewSQL.target? statement | throw "captured DML has no target"
  let table ← tableFor state target
  let keyName ← rowidName table
  let (alias,condition) := match statement with
    | .update _ alias _ condition .. | .delete _ alias condition .. => (alias,condition)
    | _ => (none,none)
  let selected ← read false state parents {
    columns := #[{ expr := .column none keyName }]
    sources := #[{ name := target, alias }]
    where_ := condition }
  let keys ← selected.result.rows.mapM fun row => do
    let some (.integer key) := row.head? | throw "captured DML RowSet key is not an integer"
    return key
  let mut current := state
  let mut direct := 0
  for key in keys.mergeSort (fun a b => a.value ≤ b.value) do
    Execution.remember current
    let stored ← tableFor current target
    if (stored.findRowid? key).isNone then continue
    let point := pointCondition keyName key
    let command ← match statement with
      | .update _ _ assignments _ action outputs => do
          let originalAssignments := assignments
          let assignments ← effectiveAssignments stored.schema assignments
          let values ← read false current parents {
            columns := assignments.map fun pair => { expr := pair.2 }
            sources := #[{ name := target, alias }]
            where_ := point }
          let [row] := values.result.rows | throw "captured UPDATE lost its actual row"
          let expressions ← CoreSQL.selectedRowExpressions row
          unless expressions.size == assignments.size do throw "captured UPDATE width mismatch"
          let evaluated ← assignments.mapIdxM fun i pair => do
            return (← CoreSQL.column stored.schema pair.1, expressions[i]!)
          let assignments ← originalAssignments.mapM fun pair => do
            let position ← CoreSQL.column stored.schema pair.1
            let some value := evaluated.find? (fun value => value.1 == position)
              | throw "captured UPDATE lost an assigned column"
            return (pair.1,value.2)
          pure (.update target alias assignments point action outputs)
      | .delete _ _ _ outputs => pure (.delete target alias point outputs)
      | _ => throw "unsupported captured DML row"
    let (next,results) ← execute { current with lastChanges := state.lastChanges } command ""
    let changed := (results.map (·.changes)).sum
    current := { next with totalChanges := next.totalChanges - changed, lastChanges := state.lastChanges }
    direct := direct + changed
    Execution.remember current
  let finished := {
    current with
    lastChanges := direct
    totalChanges := current.totalChanges + direct
    lastInsertRowid := state.lastInsertRowid }
  Execution.remember finished
  return finished

def executeBody (execute : EffectExecutor) (read : ScopedRead) (state : Core.State)
    (parents : List CoreScalarQuery.Frame) (statement : Statement) : ExecutionM Core.State := do
  Execution.remember state
  if let .select query := statement then
    discard <| read false state parents query
    return state
  let statement ← selectInput read state parents statement
  if let .insert .. := statement then
    return (← execute state statement "").1
  if captured statement then
    return ← executeCapturedRows execute read state parents statement
  let bound ← bindStatement state parents statement
  return (← execute state bound "").1

theorem effectiveAssignments_empty (schema : Core.Schema) :
    effectiveAssignments schema #[] = .ok #[] := rfl

theorem inheritConflict_default (statement : Statement) : inheritConflict .default statement = statement := rfl

theorem selectInput_ordinary_insert (read : ScopedRead) (state : Core.State)
    (parents : List CoreScalarQuery.Frame) (target : String) (columns : Option (Array String))
    (rows : Array (Array Expr)) (action : ConflictAction) (outputs : Array ResultColumn) :
    selectInput read state parents (.insert target columns rows action outputs) =
      .ok (.insert target columns rows action outputs) := rfl

end SQLeanite.CoreTriggerProgram
