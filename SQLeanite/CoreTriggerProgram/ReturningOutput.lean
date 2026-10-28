import SQLeanite.CoreTriggerProgram.DeleteBefore

namespace SQLeanite.CoreTriggerProgram

def withoutOutput : Statement → Statement
  | .insert target columns rows action _ => .insert target columns rows action #[]
  | .update target alias assignments condition action _ => .update target alias assignments condition action #[]
  | .delete target alias condition _ => .delete target alias condition #[]
  | other => other

/-- User RETURNING runs after the accepted point and before AFTER programs.
The accepted typed image supplies values; current connection state supplies
counters and scalar subquery reads. DELETE uses the original OLD registers. -/
def returningOutput (read : ScopedRead) (state : Core.State) (table : Core.Table)
    (statement : Statement) (values : List Core.Value) (subtypes : List UInt8) :
    Except String (List Core.Value) := do
  let columns := returning statement
  if columns.isEmpty then return []
  let state := returningContext state
  let target := (CoreViewSQL.target? statement).getD table.schema.name
  let ctx : CoreExpr.Context := { schema := table.schema, sourceName := target }
  let expressions := CoreLastInsert.expandProjection ctx columns.toList
  let parent ← frame state table target values true false
  let parent := { parent with subtypes }
  let selected ← read false state [parent] { columns := (expressions.map fun expr => { expr }).toArray }
  let [output] := selected.result.rows | throw "RETURNING did not produce one register row"
  return output

theorem withoutOutput_insert (target : String) (columns : Option (Array String))
    (rows : Array (Array Expr)) (action : ConflictAction) (outputs : Array ResultColumn) :
    withoutOutput (.insert target columns rows action outputs) = .insert target columns rows action #[] := rfl

end SQLeanite.CoreTriggerProgram
