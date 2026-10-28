import SQLeanite.CoreTriggerProgram.DeleteBefore
import SQLeanite.CoreTriggerProgram.NewColumns

namespace SQLeanite.CoreTriggerProgram

structure UpdateCandidate where
  command : Statement
  values : List Core.Value
  subtypes : List UInt8

/-- A private bound-value node reifies an already evaluated register. The
public token matcher rejects this name, including its typed three-field form. -/
def registerExpression (cell : CoreReturning.Cell) : Except String Expr := do
  let literal := Expr.literal (← CoreExpr.value cell.value)
  if cell.subtype == 0 then return literal
  return .call "__sqlean_bound_value"
    #[literal,.literal (.text "BLOB"),.literal (.integer cell.subtype.toNat)] false

/-- BEFORE UPDATE sees affinity-adjusted NEW values before constraints.
Only SET registers are frozen for the write; the existing point executor
reloads unassigned physical columns and recomputes stored generated fields. -/
def updateCandidate (state : Core.State) (table : Core.Table) (row : Core.Row)
    (statement : Statement) (columns : List Nat) : Except String UpdateCandidate := do
  let declared ← CoreDeclaredCollationSQL.statement state statement
  let bound := CoreConnectionSQL.statement state declared
  let .update target alias original condition action _ := bound | throw "BEFORE UPDATE requires an UPDATE"
  let ctx : CoreExpr.Context := {
    schema := table.schema
    sourceName := alias.getD target
    storedTexts := state.catalog.storedTexts }
  let assignments ← CoreSQL.expressionAssignmentsWith true ctx original.toList
  let rowidAssignments := assignments.filter (fun pair => pair.1 == table.schema.primaryKey)
  let rowidUpdates ← CoreSQL.evaluateAssignmentsTyped ctx row rowidAssignments
  for (_,cell) in rowidUpdates do
    match cell.value with
    | .integer _ => pure ()
    | _ => throw "datatype mismatch"
  let ordinary := (assignments.filter (fun pair => pair.1 != table.schema.primaryKey)).mergeSort (fun a b => a.1 ≤ b.1)
  let ordinaryUpdates ← CoreSQL.evaluateAssignmentsTyped ctx row ordinary
  let updates := rowidUpdates ++ ordinaryUpdates
  let initial := row.values.zipIdx.map fun (value,position) =>
    if position == table.schema.primaryKey || position > 31 || columns.any (· > 31) || columns.contains position then
      CoreReturning.Cell.plain value
    else CoreReturning.Cell.plain .null
  let cells : List CoreReturning.Cell := updates.foldl (fun values (position,cell) => values.set position cell) initial
  let definitions ← CoreGeneratedSQL.specs table
  let program ← CoreGeneratedSyntax.order definitions
  let candidate ← CoreGeneratedSQL.calculate table program {
    cells
    assigned := some (assignments.map Prod.fst)
    converted := List.range table.schema.columns.length }
  if let some source := table.catalogSource then
    if let some types ← source.compiledStrictColumns then
      let pairs := types.zip (candidate.cells.map (·.value))
      CoreStrictSyntax.require table.schema.name (pairs.map Prod.fst) (pairs.map Prod.snd)
  let frozen ← updates.mapM fun (position,cell) => do return (position, ← registerExpression cell)
  let expressions ← original.mapM fun pair => do
    let position ← CoreSQL.column table.schema pair.1
    let some value := frozen.find? (fun value => value.1 == position) | throw "BEFORE UPDATE lost a SET register"
    return (pair.1,value.2)
  return {
    command := .update target alias expressions condition action (returning statement)
    values := candidate.cells.map (·.value)
    subtypes := candidate.cells.map (·.subtype) }

theorem registerExpression_zero (cell : CoreReturning.Cell) (value : Value)
    (converted : CoreExpr.value cell.value = .ok value) (zero : cell.subtype = 0) :
    registerExpression cell = .ok (.literal value) := by
  simp [registerExpression, converted, zero, bind, Except.bind, pure, Except.pure]

end SQLeanite.CoreTriggerProgram
