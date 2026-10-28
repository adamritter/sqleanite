import SQLeanite.CoreTriggerProgram.Binding

namespace SQLeanite.CoreTriggerProgram

/-- Preparation visits every program even for zero selected rows or a false
WHEN. It validates expressions without running their value-dependent effects. -/
def prepareBody (base : Executor) (read : ScopedRead) (state : Core.State)
    (parents : List CoreScalarQuery.Frame) (statement : Statement) : Except String Unit := do
  if let .select query := statement then
    discard <| read true state parents { query with limit := some 0 }
    return ()
  let statement ← bindStatement state parents statement
  match statement with
  | .update table alias assignments _ conflict outputs =>
      discard <| base state (.update table alias assignments (some (.literal (.integer 0))) conflict outputs) ""
  | .delete table alias _ outputs =>
      discard <| base state (.delete table alias (some (.literal (.integer 0))) outputs) ""
  | .insert table columns rows _ outputs =>
      let some stored := CoreNames.table? state.database table | throw s!"no such table: main.{table}"
      if let some names := columns then discard <| names.toList.mapM (CoreSQL.column stored.schema)
      for values in rows do
        unless values.isEmpty do
          CoreSQL.checkInsertSelectColumns stored.schema columns values.size
          discard <| read true state [] {
            columns := values.map fun expr => { expr }
            limit := some 0 }
      let ctx : CoreExpr.Context := { schema := stored.schema, sourceName := table }
      discard <| CoreLastInsert.prepareReturning state ctx outputs.toList
  | _ => throw "unsupported trigger body preparation"

def preparePrograms (base : Executor) (read : ScopedRead) (state : Core.State)
    (table : Core.Table) (statement : Statement) (programs : List CoreCatalogData.Trigger) : Except String Unit := do
  let dummy : List Core.Value := List.replicate table.schema.columns.length .null
  let parents ← frames state table statement dummy dummy
  for program in programs do
    unless program.definition.timing == .after do throw "unsupported BEFORE or INSTEAD OF trigger execution"
    if let some condition := program.definition.when_ then
      discard <| read true state parents { columns := #[{ expr := condition }], limit := some 0 }
    for action in program.definition.body do prepareBody base read state parents action

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
      if tested.rows.isEmpty then continue
    let caller := current
    for action in program.definition.body do
      if let .select query := action then
        discard <| read false current parents query
      else
        let bound ← bindStatement current parents action
        let (next,_) ← execute program.definition.name current bound ""
        current := next
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
