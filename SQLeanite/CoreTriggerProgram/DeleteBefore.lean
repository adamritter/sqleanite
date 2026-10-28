import SQLeanite.CoreTriggerProgram.Preparation

namespace SQLeanite.CoreTriggerProgram

def withoutDeleteOutput : Statement → Statement
  | .delete target alias condition _ => .delete target alias condition #[]
  | other => other

/-- DELETE's OLD register array is populated before BEFORE programs. The
RETURNING program consumes those same registers after the actual deletion,
with the current connection registers and current database for subqueries. -/
def deleteOutput (read : ScopedRead) (state : Core.State) (table : Core.Table)
    (statement : Statement) (old : List Core.Value) : Except String (List Core.Value) := do
  let columns := returning statement
  if columns.isEmpty then return []
  let target := (CoreViewSQL.target? statement).getD table.schema.name
  let ctx : CoreExpr.Context := { schema := table.schema, sourceName := target }
  let expressions := CoreLastInsert.expandProjection ctx columns.toList
  let parent ← frame state table target old
  let selected ← read false state [parent] { columns := (expressions.map fun expr => { expr }).toArray }
  let [output] := selected.result.rows | throw "DELETE RETURNING did not produce one register row"
  return output

theorem withoutDeleteOutput_empty (target : String) (alias : Option String)
    (condition : Option Expr) (columns : Array ResultColumn) :
    returning (withoutDeleteOutput (.delete target alias condition columns)) = #[] := rfl

end SQLeanite.CoreTriggerProgram
