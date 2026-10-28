import SQLeanite.CoreTriggerProgram.Scope

namespace SQLeanite.CoreTriggerProgram

def preparePrograms (prepare : String → PrepareExecutor) (read : ScopedRead) (state : Core.State)
    (table : Core.Table) (statement : Statement) (programs : List CoreCatalogData.Trigger) : Except String Unit := do
  let dummy : List Core.Value := List.replicate table.schema.columns.length .null
  let parents ← frames state table statement dummy dummy
  for program in programs do
    let beforeSupported := match statement with | .delete .. | .update .. | .insert .. | .insertSelect .. => true | _ => false
    unless program.definition.timing == .after || (program.definition.timing == .before && beforeSupported) do
      throw "unsupported BEFORE or INSTEAD OF trigger execution"
    if let some condition := program.definition.when_ then
      discard <| read true state parents { columns := #[{ expr := condition }], limit := some 0 }
    for action in program.definition.body do
      prepare program.definition.name state parents (inheritConflict (conflict statement) action)

/-- Returning from a trigger frame preserves the caller's rowid register and
last-statement count; the actual body writes retain their accumulated total. -/
def restoreFrame (caller body : Core.State) : Core.State :=
  { body with lastChanges := caller.lastChanges, lastInsertRowid := caller.lastInsertRowid, schemaProgram := caller.schemaProgram, triggerDepth := caller.triggerDepth }


def runPrograms (execute : String → ScopedEffectExecutor) (read : ScopedRead) (state : Core.State)
    (table : Core.Table) (statement : Statement) (old new : List Core.Value)
    (programs : List CoreCatalogData.Trigger) (newSubtypes : List UInt8 := []) : ExecutionM Core.State := do
  Execution.remember state
  let mut current := state
  for program in programs do
    if current.triggerDepth >= 1000 then throw "too many levels of trigger recursion"
    let caller := current
    current := { current with triggerDepth := current.triggerDepth + 1 }
    Execution.remember current
    try
      let parents ← frames current table statement old new newSubtypes
      if let some condition := program.definition.when_ then
        let tested ← read false current parents {
          columns := #[{ expr := .literal (.integer 1) }]
          where_ := some condition }
        if tested.result.rows.isEmpty then
          current := restoreFrame caller current
          Execution.remember current
          continue
      for action in program.definition.body do
        current ← executeBody (execute program.definition.name parents) read current parents
          (inheritConflict (conflict statement) action)
      current := restoreFrame caller current
      Execution.remember current
    catch message =>
      Execution.remember (restoreFrame caller (← Execution.current))
      throw message
  return current


theorem restoreFrame_context (caller body : Core.State) :
    (restoreFrame caller body).schemaProgram = caller.schemaProgram := rfl

theorem restoreFrame_database (caller body : Core.State) :
    (restoreFrame caller body).database = body.database := rfl

theorem restoreFrame_total (caller body : Core.State) :
    (restoreFrame caller body).totalChanges = body.totalChanges := rfl

theorem restoreFrame_registers (caller body : Core.State) :
    (restoreFrame caller body).lastChanges = caller.lastChanges ∧
      (restoreFrame caller body).lastInsertRowid = caller.lastInsertRowid := ⟨rfl,rfl⟩

theorem restoreFrame_depth (caller body : Core.State) :
    (restoreFrame caller body).triggerDepth = caller.triggerDepth := rfl

end SQLeanite.CoreTriggerProgram
