import SQLeanite.CoreTriggerProgram.Binding

namespace SQLeanite.CoreTriggerProgram

def returningContext (state : Core.State) : Core.State := { state with raiseContext := true }

theorem returningContext_schemaProgram (state : Core.State) :
    (returningContext state).schemaProgram = state.schemaProgram := rfl

/-- Compile actual RETURNING source scopes without evaluating rows. Reuse the
real scalar-query compiler context for subquery admission/affinity, while
retaining the ordinary RETURNING-only wildcard/aggregate/width rules. -/
def prepareReturning (read : ScopedRead) (state : Core.State) (table : Core.Table)
    (target : String) (outputs : Array ResultColumn) : Except String (List Expr) := do
  if outputs.isEmpty then return []
  let state := returningContext state
  let outputs := outputs.map fun column => { column with expr := CoreConnectionSQL.expression state column.expr }
  for column in outputs do
    if column.expr.any (fun expression => match expression with | .star (some _) => true | _ => false) then
      throw "RETURNING may not use \"TABLE.*\" wildcards"
    if let some message := SQLite.Scalar.aggregateMisuseFuel column.expr.height column.expr then throw message
  let prepared ← read true state [] {
    columns := outputs
    sources := #[{ name := target }]
    limit := some 0 }
  let ctx := prepared.preparedContext.getD { schema := table.schema, sourceName := target }
  CoreLastInsert.prepareReturning state ctx outputs.toList

theorem prepareReturning_empty (read : ScopedRead) (state : Core.State) (table : Core.Table) (target : String) :
    prepareReturning read state table target #[] = .ok [] := rfl

end SQLeanite.CoreTriggerProgram
