import SQLeanite.CoreSourceSQL
import SQLeanite.SQLite.ForeignKeyCatalog

/-! Propagate admitted parent renames through retained REFERENCES programs.
Each edited source must parse to its unchanged child Core schema before use. -/
namespace SQLeanite.CoreForeignKeyRename

structure Request where
  parent : String
  column : Option String
  newName : String
  forceQuote : Bool

def quotedInput (source : String) : Bool :=
  let chars := source.toList
  match (SQLite.CreateCatalog.spans (chars.length + 1) 0 chars []).toOption with
  | none => false
  | some spans =>
      match (spans.takeWhile (fun span => span.token != .symbol ";")).getLast? with
      | some span => match span.token with | .ident _ => false | _ => true
      | none => false

def request (state : Core.State) (statement : Statement) (source : String) : Option Request :=
  match statement with
  | .alterRenameTable name newName =>
      some { parent := CoreSQL.resolveTableName state name, column := none, newName, forceQuote := true }
  | .alterRenameColumn name oldName newName =>
      some {
        parent := CoreSQL.resolveTableName state name
        column := some oldName
        newName
        forceQuote := quotedInput source }
  | _ => none

def execute (before after : Core.State) (statement : Statement) (source : String) : Except String Core.State := do
  let some change := request before statement source | return after
  let mut current := after
  for child in after.database.tables do
    let keys ← CoreForeignKeyData.keys child
    unless keys.any (fun (_, key) => key.table.toLower == change.parent.toLower &&
        change.column.all (fun oldName => key.column.any (fun name => name.toLower == oldName.toLower))) do continue
    let some sql := SQLite.ForeignKeyCatalog.rewrite child.catalogSQL change.parent change.column change.newName change.forceQuote |
      throw "cannot retain renamed foreign-key source"
    current ← CoreSourceSQL.retain current child.schema.name sql
  return current

theorem execute_unrelated (before after : Core.State) (statement : Statement) (source : String)
    (unchanged : request before statement source = none) :
    execute before after statement source = .ok after := by
  simp [execute, unchanged, pure, Except.pure]

end SQLeanite.CoreForeignKeyRename
