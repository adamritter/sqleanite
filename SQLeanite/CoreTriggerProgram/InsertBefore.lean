import SQLeanite.CoreTriggerProgram.InputRegisters

namespace SQLeanite.CoreTriggerProgram

/-- Matching INSERT programs make multi-VALUES a materialized input source.
All original source expressions execute before the first BEFORE program. -/
def insertInput (read : ScopedRead) (state : Core.State) (statement : Statement) : Except String Statement := do
  match statement with
  | .insert target columns rows action outputs =>
      if rows.size ≤ 1 || ((programs state statement).isEmpty && outputs.isEmpty) then return statement
      let inputs ← rows.toList.mapM fun row => do
        let selected ← read false state [] { columns := row.map fun expr => { expr } }
        let [values] := selected.result.rows | throw "INSERT input did not return one source row"
        CoreSQL.selectedRowExpressions values
      return .insert target columns inputs.toArray action outputs
  | other => return other

/-- Ordinary input registers are computed once. The separate IPK expression
is retained for its actual post-BEFORE evaluation, except a cached subquery. -/
def insertCandidate (read : ScopedRead) (state : Core.State) (table : Core.Table)
    (statement : Statement) (makeImage : Bool := true) : Except String BeforeCandidate := do
  let .insert target columns rows action outputs := statement | throw "BEFORE INSERT requires VALUES input"
  let [original] := rows.toList | throw "BEFORE INSERT requires one planned input row"
  let preparation ← CoreGeneratedSQL.preparation state target
  let targets ← CoreSQL.prepareInsertTargets columns (.inl rows) preparation
  let indices ← match targets.columns with
    | none => pure table.schema.visibleColumnIndices
    | some names => names.toList.mapM (CoreSQL.column table.schema)
  let rowidInput := if original.isEmpty then none else CoreSQL.insertValueIndex table.schema.primaryKey table.schema.primaryKey indices
  let used := if original.isEmpty then [] else (List.range table.schema.columns.length).filterMap fun position =>
    if position == table.schema.primaryKey then none else CoreSQL.insertValueIndex table.schema.primaryKey position indices
  let evaluated ← used.mapM fun index => do
    let some expression := original[index]? | throw "INSERT lost an ordinary input"
    pure (index, ← registerExpression (← inputCell read state expression))
  let prepared := original.mapIdx fun index _ =>
    ((evaluated.find? (fun pair => pair.1 == index)).map Prod.snd).getD (.literal .null)
  let cells ← CoreSQL.rowValuesTyped table.schema targets.columns prepared
  let rowidExpression ← (rowidInput.bind (fun index => original[index]?)).mapM fun expression =>
    if makeImage then cacheInputQueries read state (expression.height+1) expression else pure expression
  let rowidCell ← if !makeImage then pure (CoreReturning.Cell.plain .null) else match rowidExpression with
    | none => pure (CoreReturning.Cell.plain .null)
    | some expression => do
        let some column := table.schema.columns[table.schema.primaryKey]? | throw "missing INSERT rowid column"
        let cell ← inputCell read state expression
        pure (cell.writeAffinity column.affinity)
  let newRowid ← match rowidCell.value with
    | .null => CoreReturning.Cell.plain <$> SQLSurface.value (.integer (-1))
    | .integer _ => pure { rowidCell with subtype := 0 }
    | _ => throw "datatype mismatch"
  let cells := cells.set table.schema.primaryKey rowidCell
  let provisional := cells.set table.schema.primaryKey newRowid
  let definitions ← CoreGeneratedSQL.specs table
  let program ← CoreGeneratedSyntax.order definitions
  let candidate ← if makeImage then CoreGeneratedSQL.calculate table program {
    cells := provisional
    converted := List.range table.schema.columns.length }
    else pure ({ cells := provisional } : CoreSQL.RowInput)
  if makeImage then
   if let some source := table.catalogSource then
    if let some types ← source.compiledStrictColumns then
      let pairs := types.zip (candidate.cells.map (·.value))
      CoreStrictSyntax.require table.schema.name (pairs.map Prod.fst) (pairs.map Prod.snd)
  let keyName ← rowidName table
  let positions := (List.range table.schema.columns.length).filter fun position =>
    !(table.withoutRowid && position == table.schema.primaryKey) && !definitions.any (fun definition => definition.position == position)
  let names := positions.map fun position => if position == table.schema.primaryKey then keyName
    else (table.schema.columns[position]?.map (·.name)).getD ""
  let expressions ← positions.mapM fun position => do
    if position == table.schema.primaryKey then
      if let some expression := rowidExpression then
        return expression
    let some cell := cells[position]? | throw "INSERT lost a computed column register"
    registerExpression cell
  return {
    command := .insert target (some names.toArray) #[expressions.toArray] action outputs
    values := candidate.cells.map (·.value)
    subtypes := candidate.cells.map (·.subtype) }

/-- The second IPK evaluation runs after BEFORE programs. Still-unreached
subqueries execute in that actual state, while Once registers already reached
by NEW evaluation have been replaced by their actual typed values. -/
def finishInsertInput (read : ScopedRead) (state : Core.State) (table : Core.Table)
    (statement : Statement) : Except String Statement := do
  match statement with
  | .insert target (some columns) rows action outputs =>
      if (CoreNames.table? state.database target).any (·.withoutRowid) then return statement
      let indices ← columns.toList.mapM (CoreSQL.column table.schema)
      let some position := CoreSQL.insertValueIndex table.schema.primaryKey table.schema.primaryKey indices
        | throw "INSERT candidate lost its rowid input"
      let rows ← rows.mapM fun row => row.mapIdxM fun index expression => do
        if index == position then registerExpression (← inputCell read state expression) else pure expression
      return .insert target (some columns) rows action outputs
  | other => return other

theorem finishInsertInput_update (read : ScopedRead) (state : Core.State) (table : Core.Table)
    (target : String) (alias : Option String) (assignments : Array (String × Expr))
    (condition : Option Expr) (action : ConflictAction) (outputs : Array ResultColumn) :
    finishInsertInput read state table (.update target alias assignments condition action outputs) =
      .ok (.update target alias assignments condition action outputs) := rfl

end SQLeanite.CoreTriggerProgram
