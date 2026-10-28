import SQLeanite.CoreTriggerProgram.Effects
import SQLeanite.CoreUpsertSQL

namespace SQLeanite.CoreTriggerProgram.Replacement

/-- REPLACE invokes DELETE programs only with recursive_triggers enabled. -/
def preparation (state : Core.State) (statement : Statement) : Option Statement := do
  unless state.recursiveTriggers do none
  let (target,action) ← match statement with
    | .insert target _ _ action _ | .insertSelect target _ _ action _ | .update target _ _ _ action _ => some (target,action)
    | _ => none
  let table ← CoreNames.table? state.database target
  unless action == .replace || (action == .default && CoreDefaultConflict.primaryPolicy table.schema == .replace) do none
  let deletion := Statement.delete target none (some (.literal (.integer 0))) #[]
  unless !(programs state deletion).isEmpty do none
  return deletion

def withoutReturning : Statement → Statement
  | .insert target columns rows action _ => .insert target columns rows action #[]
  | .update target alias assignments condition action _ => .update target alias assignments condition action #[]
  | other => other

def freezeInsertedRowid (table : Core.Table) (value : Core.Value) (statement : Statement) : Except String Statement := do
  match statement with
  | .insert target (some columns) rows action outputs =>
      let indices ← columns.toList.mapM (CoreSQL.column table.schema)
      let some position := CoreSQL.insertValueIndex table.schema.primaryKey table.schema.primaryKey indices
        | throw "REPLACE lost its computed rowid register"
      let expression := Expr.literal (← CoreExpr.value value)
      return .insert target (some columns) (rows.map (·.set! position expression)) action outputs
  | other => return other

/-- A pure checked point supplies its accepted candidate and actual victims.
Its temporary state is discarded. DELETE programs execute on the real pending
state; their body effects remain, while auxiliary deletion counts are removed. -/
def beforeWrite (base : Executor) (remove : ScopedEffectExecutor)
    (capture : Statement → Except String Statement) (state : Core.State)
    (table : Core.Table) (statement : Statement) (old : Option Core.Integer) :
    ExecutionM (Core.State × Statement × Option CoreSQL.RowInput) := do
  Execution.remember state
  if (preparation state statement).isNone then return (state,statement,none)
  let (accepted,results) ← base state (← capture (withoutReturning statement)) ""
  if (results.map (·.changes)).sum == 0 then return (state,statement,none)
  let [image] := results.flatMap (·.rows) | throw "REPLACE preflight lost its candidate"
  let values := image.take table.schema.columns.length
  let candidate ← Core.Row.create table.schema values
  let some actual := CoreNames.table? accepted.database table.schema.name | throw "REPLACE preflight lost its target"
  let victims := table.rows.filter fun row =>
    !old.any (· == row.rowid) && (candidate.rowid == row.rowid || (actual.findRowid? row.rowid).isNone)
  let columns := CoreUpsertSQL.conflictColumns table
  let rank := fun row => (columns.findIdx? fun column =>
    (CoreUpsertSQL.conflictingRow table candidate column).any (fun other => other.rowid == row.rowid)).getD columns.length
  let victims := victims.mergeSort (fun a b => rank a ≤ rank b)
  let key ← rowidName table
  let mut current := state
  for victim in victims do
    let caller := current
    let (next,deleted) ← remove [] current (.delete table.schema.name none
      (some (.binary .eq (.column none key) (.literal (.integer victim.rowid.value)))) #[]) ""
    current := { next with
      totalChanges := next.totalChanges - (deleted.map (·.changes)).sum
      lastChanges := caller.lastChanges
      lastInsertRowid := caller.lastInsertRowid }
    Execution.remember current
  let frozen ← match statement with
    | .update _ _ assignments .. => do
        let positions ← assignments.toList.mapM fun (name,_) => CoreSQL.column table.schema name
        let tags := (image.drop table.schema.columns.length).take table.schema.columns.length
        let cells ← (values.zip tags).mapM fun (value,tag) => do
          let .integer tag := tag | throw "REPLACE lost a typed register"
          unless 0 ≤ tag.value && tag.value < 256 do throw "REPLACE register subtype is outside its byte range"
          pure ({ value, subtype := UInt8.ofNat tag.value.toNat } : CoreReturning.Cell)
        unless cells.length == table.schema.columns.length do throw "REPLACE lost its full UPDATE register image"
        pure (some ({ cells, assigned := some positions, converted := List.range cells.length } : CoreSQL.RowInput))
    | _ => pure none
  let some rowid := values[table.schema.primaryKey]? | throw "REPLACE candidate lost its rowid"
  return (current, ← freezeInsertedRowid table rowid statement,frozen)

theorem preparation_disabled (state : Core.State) (statement : Statement)
    (disabled : state.recursiveTriggers = false) : preparation state statement = none := by
  simp [preparation, disabled]

end SQLeanite.CoreTriggerProgram.Replacement
