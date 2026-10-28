import SQLeanite.CoreTriggerProgram.RegisterInput

namespace SQLeanite.CoreTriggerProgram.ValuesInput

/-- A VALUES coroutine yields its complete real source registers before the
outer projection. Keep clauses needing another producer on their own plans. -/
def rows? (state : Core.State) : Statement → Option (Array (Array Expr))
  | .insertSelect _ _ query _ outputs => do
      unless state.catalog.current.textEncoding == 1 && outputs.isEmpty &&
          query.valueRows.isNone && query.where_.isNone && query.groupBy.isEmpty &&
          query.having.isNone && query.orderBy.isEmpty && !query.distinct &&
          query.limit.isNone && query.offset == 0 && query.compounds.isEmpty &&
          !CoreWindow.has query && !CoreScalarQuery.has query.compoundHeight query &&
          !query.columns.any (fun column => CoreAggregate.containsAggregate column.expr) do none
      let [source] := query.sources.toList | none
      unless source.columnAliases.isEmpty && source.functionArgs.isNone && source.joinOn.isNone do none
      let sql ← source.subquerySql
      let parsed ← (CoreTokenGrammar.parseCertified sql).toOption
      match parsed.statements.toList with
      | [.values rows] => some rows
      | [.select input] =>
          unless input.sources.isEmpty && input.where_.isNone && input.groupBy.isEmpty &&
              input.having.isNone && input.orderBy.isEmpty && !input.distinct &&
              input.limit.isNone && input.offset == 0 && input.compounds.isEmpty do none
          input.valueRows
      | _ => none
  | _ => none

structure Prepared where
  target : String
  columns : Option (Array String)
  rows : Array (Array Expr)
  outputs : Array ResultColumn
  context : CoreExpr.Context
  action : ConflictAction
  table : Core.Table

/-- Reuse actual source metadata from ordinary checked preparation. Source
rows are evaluated only after execution starts; no placeholder values are used. -/
def prepare (read : ScopedRead) (state : Core.State) (statement : Statement)
    (rows : Array (Array Expr)) : Except String Prepared := do
  let .insertSelect target columns query action _ := statement | throw "VALUES input requires INSERT SELECT"
  let prepared ← read true state [] { query with limit := some 0 }
  let context ← CoreScalarQuery.localContext prepared.inputState prepared.inputQuery
  let outputs ← CoreOrder.expandResults context query.columns.toList
  let table ← tableFor state target
  let preparation ← CoreGeneratedSQL.preparation state target
  let targets ← CoreSQL.prepareInsertTargets columns (.inr query) preparation
  return { target, columns := targets.columns, rows, outputs := outputs.toArray, context, action, table }

def execute (point : PointExecutor) (execute : String → ScopedEffectExecutor)
    (remove : ScopedEffectExecutor) (read : ScopedRead) (state : Core.State)
    (prepared : Prepared) (source : String) : ExecutionM (Core.State × List Core.Result) := do
  let mut current := state
  let mut direct := 0
  for row in prepared.rows do
    Execution.remember current
    let input ← read false current [] { columns := row.map fun expr => { expr } }
    let [values] := input.result.rows | throw "VALUES coroutine did not yield one real source row"
    -- VALUES coroutine columns have no expression affinity, including when
    -- an input expression was CAST. The actual source registers are unchanged.
    let frame : CoreScalarQuery.Frame := { context := prepared.context, row := values, columnAffinity := false }
    let output ← read false current [frame] { columns := prepared.outputs }
    let [values] := output.result.rows | throw "VALUES outer projection did not yield one source row"
    let input ← CoreSQL.selectedRowExpressions values
    let command := Statement.insert prepared.target prepared.columns #[input] prepared.action #[]
    let (next,results) ← executeRows point execute remove read current prepared.table command source []
    current := RegisterInput.pending state next
    direct := direct + (results.map (·.changes)).sum
    Execution.remember current
  current := { current with lastChanges := direct, totalChanges := state.totalChanges + direct }
  Execution.remember current
  return (current,[{ changes := direct }])

theorem rows?_utf8_only (state : Core.State) (statement : Statement)
    (other : state.catalog.current.textEncoding ≠ 1) : rows? state statement = none := by
  have encoding : (state.catalog.current.textEncoding == 1) = false := by simp [other]
  cases statement <;> simp [rows?, encoding]

end SQLeanite.CoreTriggerProgram.ValuesInput
