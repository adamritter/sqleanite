import SQLeanite.CoreViewSQL

namespace SQLeanite.CoreTriggerSQL

def find? (state : Core.State) (name : String) : Option CoreCatalogData.Trigger :=
  state.catalog.current.triggers.find? (fun trigger => trigger.definition.name.toLower == name.toLower)

def guard (state : Core.State) (statement : Statement) : Except String Unit := do
  if state.catalog.current.triggers.isEmpty then return ()
  match statement with
  | .alterRenameTable .. | .alterRenameColumn .. | .alterDropColumn .. =>
      throw "unsupported trigger-aware ALTER TABLE"
  | _ => pure ()

def executeDDL (state : Core.State) (statement : Statement) (source : String) :
    Except String (Core.State × List Core.Result) := do
  match statement with
  | .createTrigger name table _ timing _ _ ifNotExists temporary display original =>
      if temporary then throw "unsupported temporary trigger"
      let view := CoreViewSQL.find? state table
      let system := ["sqlite_schema","sqlite_master"].contains table.toLower
      unless view.isSome || (CoreNames.table? state.database table).isSome || system do
        throw s!"no such table: main.{table}"
      if name.toLower.startsWith "sqlite_" then throw s!"object name reserved for internal use: {name}"
      if (find? state name).isSome then
        if ifNotExists then return (state,[{}])
        else throw s!"trigger {if display.isEmpty then name else display} already exists"
      if table.toLower.startsWith "sqlite_" then throw "cannot create trigger on system table"
      if view.isSome then
        unless timing == .insteadOf do
          throw s!"cannot create {if timing == .before then "BEFORE" else "AFTER"} trigger on view: {table}"
      else if timing == .insteadOf then throw s!"cannot create INSTEAD OF trigger on table: {table}"
      let owner := table
      let text := if original.isEmpty then source else original
      let some text := CoreCatalogData.normalizeTrigger text | throw "invalid trigger source normalization"
      let compiled ← CoreCatalogData.triggerAtOwner text owner
      unless compiled.definition.name == name && compiled.definition.table.toLower == table.toLower do
        throw "trigger source target mismatch"
      let current := { state.catalog.current with triggers := state.catalog.current.triggers ++ [compiled] }
      return ({ state with catalog := { state.catalog with current } },[{}])
  | .dropTrigger name ifExists =>
      match find? state name with
      | none => if ifExists then return (state,[{}]) else throw s!"no such trigger: {name}"
      | some found =>
          let triggers := state.catalog.current.triggers.filter (fun trigger => trigger.definition.name != found.definition.name)
          let current := { state.catalog.current with triggers }
          return ({ state with catalog := { state.catalog with current } },[{}])
  | _ => throw "not a trigger DDL statement"

/-- Dropping an owner removes its persistent triggers with the same statement.
Other table/view source declarations may remain deferred, as in SQLite. -/
def removeDroppedOwners (state : Core.State) (statement : Statement) : Core.State :=
  match statement with
  | .dropTable .. | .dropView .. =>
      let triggers := state.catalog.current.triggers.filter fun trigger =>
        (CoreNames.table? state.database trigger.owner).isSome ||
          (CoreViewSQL.find? state trigger.owner).isSome
      { state with catalog := { state.catalog with current := { state.catalog.current with triggers } } }
  | _ => state

theorem removeDroppedOwners_database (state : Core.State) (statement : Statement) :
    (removeDroppedOwners state statement).database = state.database := by
  cases statement <;> rfl

end SQLeanite.CoreTriggerSQL
