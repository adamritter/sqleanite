import SQLeanite.CoreTriggerProgram.Scope

namespace SQLeanite.CoreTriggerProgram

def preparePrograms (prepare : String → PrepareExecutor) (read : ScopedRead) (state : Core.State)
    (table : Core.Table) (statement : Statement) (programs : List CoreCatalogData.Trigger) : Except String Unit := do
  let dummy : List Core.Value := List.replicate table.schema.columns.length .null
  let parents ← frames state table statement dummy dummy
  for program in programs do
    unless program.definition.timing == .after do throw "unsupported BEFORE or INSTEAD OF trigger execution"
    if let some condition := program.definition.when_ then
      discard <| read true state parents { columns := #[{ expr := condition }], limit := some 0 }
    for action in program.definition.body do
      prepare program.definition.name state parents (inheritConflict (conflict statement) action)

/-- Returning from a trigger frame preserves the caller's rowid register and
last-statement count; the actual body writes retain their accumulated total. -/
def restoreFrame (caller body : Core.State) : Core.State :=
  { body with lastChanges := caller.lastChanges, lastInsertRowid := caller.lastInsertRowid }


def runPrograms (execute : String → Executor) (read : ScopedRead) (state : Core.State)
    (table : Core.Table) (statement : Statement) (old new : List Core.Value)
    (programs : List CoreCatalogData.Trigger) : Except String Core.State := do
  let mut current := state
  for program in programs do
    let parents ← frames current table statement old new
    if let some condition := program.definition.when_ then
      let tested ← read false current parents {
        columns := #[{ expr := .literal (.integer 1) }]
        where_ := some condition }
      if tested.result.rows.isEmpty then continue
    let caller := current
    for action in program.definition.body do
      current ← executeBody (execute program.definition.name) read current parents
        (inheritConflict (conflict statement) action)
    current := restoreFrame caller current
  return current


theorem restoreFrame_database (caller body : Core.State) :
    (restoreFrame caller body).database = body.database := rfl

theorem restoreFrame_total (caller body : Core.State) :
    (restoreFrame caller body).totalChanges = body.totalChanges := rfl

theorem restoreFrame_registers (caller body : Core.State) :
    (restoreFrame caller body).lastChanges = caller.lastChanges ∧
      (restoreFrame caller body).lastInsertRowid = caller.lastInsertRowid := ⟨rfl,rfl⟩

end SQLeanite.CoreTriggerProgram
