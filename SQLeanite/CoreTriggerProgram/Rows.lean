import SQLeanite.CoreTriggerProgram.ForeignCounter
import SQLeanite.CoreTriggerProgram.InsertBefore
import SQLeanite.CoreTriggerProgram.Replacement
import SQLeanite.CoreTriggerProgram.ReturningOutput

namespace SQLeanite.CoreTriggerProgram

structure RowStep where
  statement : Statement
  rowid : Option Core.Integer := none

/-- Triggered UPDATE/DELETE use SQLite's preselected RowSet. Subsequent writes
visit its original keys and skip keys removed by an earlier trigger. -/
def steps (base : Executor) (state : Core.State) (table : Core.Table) (statement : Statement) :
    Except String (List RowStep) := do
  let rowid ← rowidName table
  match statement with
  | .insert target columns rows conflict outputs =>
      return rows.toList.map fun row => { statement := .insert target columns #[row] conflict outputs }
  | .update target alias _ condition .. | .delete target alias condition .. =>
      let query : Select := {
        columns := #[{ expr := .column none rowid }]
        sources := #[{ name := target, alias }]
        where_ := condition }
      let (_,selected) ← base state (.select query) ""
      let keys ← (selected.flatMap (·.rows)).mapM fun values => do
        let some (.integer key) := values.head? | throw "trigger RowSet key is not an integer"
        return key
      let keys := keys.mergeSort (fun a b => a.value ≤ b.value)
      return keys.map fun key =>
        let condition := some (Expr.binary .eq (.column none rowid) (.literal (.integer key.value)))
        let point := match statement with
          | .update target alias assignments _ conflict outputs => .update target alias assignments condition conflict outputs
          | .delete target alias _ outputs => .delete target alias condition outputs
          | other => other
        { statement := point, rowid := some key }
  | _ => throw "unsupported triggered DML shape"

/-- The existing RETURNING machinery captures the accepted post-affinity row
before AFTER programs run. User expressions remain in their original order. -/
def capture (table : Core.Table) (statement : Statement) : Except String Statement := do
  let rowid ← rowidName table
  let image : Array ResultColumn := (table.schema.columns.mapIdx fun index column =>
    { expr := Expr.column none (if index == table.schema.primaryKey then rowid else column.name) }).toArray
  let types : Array ResultColumn := image.map fun column => { expr := .call "subtype" #[column.expr] false }
  let outputs := image ++ types ++ returning statement
  match statement with
  | .insert target columns rows conflict _ => return .insert target columns rows conflict outputs
  | .update target alias assignments condition conflict _ => return .update target alias assignments condition conflict outputs
  | .delete target alias condition _ => return .delete target alias condition outputs
  | _ => throw "unsupported trigger row capture"

def executeRows (point : PointExecutor) (execute : String → ScopedEffectExecutor) (remove : ScopedEffectExecutor) (read : ScopedRead) (state : Core.State)
    (table : Core.Table) (statement : Statement) (source : String)
    (programs : List CoreCatalogData.Trigger) (parents : List CoreScalarQuery.Frame := []) : ExecutionM (Core.State × List Core.Result) := do
  Execution.remember state
  let base := point none
  let inputRead := inputScope read parents
  let statement := bindCounters state statement
  let statement ← selectInput inputRead state [] statement
  let streamingValues := match statement with
    | .insert _ _ rows .. => rows.size > 1 && (CoreTriggerProgram.programs state statement).isEmpty && (returning statement).isEmpty
    | _ => false
  let statement ← insertInput inputRead state statement
  let plan ← steps base state table statement
  let before := programs.filter (fun program => program.definition.timing == .before)
  let after := programs.filter (fun program => program.definition.timing == .after)
  let beforeColumns ← if before.isEmpty then pure [] else match statement with
    | .update .. => newColumns read state table statement
    | _ => pure []
  let mut current := state
  let mut direct := 0
  let mut outputs : List (List Core.Value) := []
  for step in plan do
    Execution.remember current
    let some stored := CoreNames.table? current.database table.schema.name
      | throw "trigger owner disappeared during row execution"
    let old := step.rowid.bind stored.findRowid?
    if step.rowid.isSome && old.isNone then continue
    let oldValues := (old.map (·.values)).getD []
    let input ← if streamingValues then match step.statement with
        | .insert target columns rows action projection => do
            let rows ← rows.mapM fun row => do
              let selected ← inputRead false current [] { columns := row.map fun expr => { expr } }
              let [values] := selected.result.rows | throw "streamed INSERT lost its source row"
              CoreSQL.selectedRowExpressions values
            pure (.insert target columns rows action projection)
        | other => pure other
      else pure step.statement
    let candidate ← match input with
      | .insert .. => some <$> insertCandidate inputRead current stored input (!before.isEmpty)
      | .update .. => if before.isEmpty && (Replacement.preparation current input).isNone then pure none else do
          let some row := old | throw "BEFORE UPDATE lost its actual old row"
          let columns := if before.isEmpty then List.range stored.schema.columns.length else beforeColumns
          some <$> updateCandidate current stored row input columns
      | _ => pure none
    unless before.isEmpty do
      current ← runPrograms execute read { current with lastChanges := state.lastChanges }
        stored statement oldValues (candidate.map (·.values) |>.getD []) before
        (candidate.map (·.subtypes) |>.getD [])
      let pending ← tableFor current table.schema.name
      if step.rowid.any (fun key => (pending.findRowid? key).isNone) then continue
    let command ← match candidate with
      | some candidate => finishInsertInput inputRead current stored candidate.command
      | none => pure (if before.isEmpty then step.statement else withoutDeleteOutput step.statement)
    let (afterVictims,command,registers) ← Replacement.beforeWrite base remove (capture stored) current stored command step.rowid
    current := afterVictims
    Execution.remember current
    let (next,results) ← point registers current (← capture stored (withoutOutput command)) source
    Execution.remember { next with totalChanges := current.totalChanges, lastChanges := state.lastChanges }
    let changed := (results.map (·.changes)).sum
    if changed == 0 then
      current := { next with totalChanges := current.totalChanges, lastChanges := state.lastChanges }
      Execution.remember current
      continue
    let [image] := results.flatMap (·.rows) | throw "trigger row capture returned an invalid row count"
    let new := image.take table.schema.columns.length
    unless new.length == table.schema.columns.length do throw "trigger row capture width mismatch"
    let subtypeValues := (image.drop table.schema.columns.length).take table.schema.columns.length
    unless subtypeValues.length == table.schema.columns.length do throw "trigger subtype capture width mismatch"
    let subtypes ← subtypeValues.mapM fun value => do
      let .integer value := value | throw "trigger subtype register is not an integer"
      unless 0 ≤ value.value && value.value < 256 do throw "trigger subtype register is outside its byte range"
      pure (UInt8.ofNat value.value.toNat)
    let next := { next with totalChanges := current.totalChanges, lastChanges := state.lastChanges }
    let deleting := match step.statement with | .delete .. => true | _ => false
    let next ← ForeignCounter.account current next step.statement
      (if step.rowid.isSome then some oldValues else none) (if deleting then none else some new)
    Execution.remember next
    if !(returning statement).isEmpty then
      let output ← if deleting then deleteOutput read next stored statement oldValues
        else returningOutput read next stored statement new subtypes
      outputs := outputs ++ [output]
    current ← runPrograms execute read next stored statement oldValues new after subtypes
    direct := direct + changed
  current := { current with lastChanges := direct, totalChanges := current.totalChanges + direct }
  Execution.remember current
  return (current,[{ rows := outputs, changes := direct }])

theorem capture_insert (table : Core.Table) (target : String) (columns : Option (Array String))
    (rows : Array (Array Expr)) (conflict : ConflictAction) (outputs : Array ResultColumn)
    (name : String) (found : rowidName table = .ok name) :
    (capture table (.insert target columns rows conflict outputs)).map (fun statement =>
      match statement with | .insert target columns rows conflict _ => (target,columns,rows,conflict) | _ => ("",none,#[],.default)) =
      .ok (target,columns,rows,conflict) := by
  simp [capture, found, returning, bind, Except.bind, pure, Except.pure]
  rfl

end SQLeanite.CoreTriggerProgram
