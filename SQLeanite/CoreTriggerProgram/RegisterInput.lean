import SQLeanite.CoreTriggerProgram.Rows

namespace SQLeanite.CoreTriggerProgram.RegisterInput

/-- The existing external plain-table coroutine is independent of target
writes. Other SELECT plans retain their own materialization and compilation. -/
def eligible (state : Core.State) : Statement → Bool
  | .insertSelect target _ query _ outputs =>
      outputs.isEmpty && query.sources.size == 1 && query.compounds.isEmpty &&
        query.valueRows.isNone && query.groupBy.isEmpty &&
        query.having.isNone && (!query.distinct || query.orderBy.isEmpty) &&
        !CoreWindow.has query && !CoreScalarQuery.has query.compoundHeight query &&
        !query.columns.any (fun column => CoreAggregate.containsAggregate column.expr) &&
        (query.sources[0]?).any fun source =>
          source.schema.isNone && source.functionArgs.isNone && source.subquerySql.isNone &&
            source.joinOn.isNone && CoreSQL.resolveTableName state source.name != CoreSQL.resolveTableName state target &&
            (CoreNames.table? state.database source.name).any fun table =>
              table.indexes.isEmpty && CoreSQL.selectNamesBound table.schema source query
  | _ => false

/-- Direct counts finish at the statement boundary; yielded points preserve
only their actual rowid effects while the source coroutine is still running. -/
def pending (entry next : Core.State) : Core.State :=
  { next with lastChanges := entry.lastChanges, totalChanges := entry.totalChanges }

theorem pending_database (entry next : Core.State) :
    (pending entry next).database = next.database := rfl

structure Prepared where
  target : String
  query : Select
  action : ConflictAction
  selection : Option CoreSQL.RegisterSelection
  columns : Option (Array String)
  table : Core.Table

/-- Source/target compilation completes before execution starts, even if the
source is empty. The result contains actual checked schemas and source rows. -/
def prepare (state : Core.State) (statement : Statement) : Except String Prepared := do
  let compiled ← CoreGeneratedSQL.statement state statement
  let compiled ← CoreDeclaredCollationSQL.statement state compiled
  let .insertSelect target columns query action _ := CoreConnectionSQL.statement state compiled
    | throw "register input requires INSERT SELECT"
  let preparation ← CoreGeneratedSQL.preparation state target
  let some table := CoreNames.table? state.database target | throw s!"no such table: {target}"
  let some source := query.sources[0]? | throw "missing INSERT SELECT source"
  let some input := CoreNames.table? state.database source.name | throw s!"no such table: {source.name}"
  let targets ← CoreSQL.prepareInsertTargets columns (.inr query) preparation
  let columns := targets.columns
  let selection ← if (CoreSQL.registerDirection? input.schema source query).isSome then
      some <$> CoreSQL.prepareRegisterSelection state target columns query action preparation
    else do
      CoreSQL.prepareInsertSelectionDefaults table.schema columns action
      pure none
  return { target, query, action, selection, columns, table }

def execute (point : PointExecutor) (execute : String → ScopedEffectExecutor)
    (remove : ScopedEffectExecutor) (read : ScopedRead) (state : Core.State)
    (prepared : Prepared) (source : String) : ExecutionM (Core.State × List Core.Result) := do
  let { target, query, action, selection, columns, table } := prepared
  let (next,results) ← match selection with
    | some selection => do
        let emit := fun current input => do
          let command := Statement.insert target selection.columns #[input] action #[]
          let (next,results) ← executeRows point execute remove read current table command source []
          let next := pending state next
          Execution.remember next
          return (next,results)
        CoreSQL.insertRegisterRowsWith (m := ExecutionM) emit state selection.context selection.projection
          query.where_ selection.rows query.offset query.limit selection.distinct
    | none => do
        let selected ← read false state [] query
        let rows ← (selected.result.rows.mapM CoreSQL.selectedRowExpressions : Except String (List (Array Expr)))
        executeRows point execute remove read state table (.insert target columns rows.toArray action #[]) source []
  let next ← if table.schema.autoIncrement then do
      let counter ← CoreAutoIncrement.beginContext next table.schema.name
      CoreAutoIncrement.finish next counter
    else pure next
  let count := (results.map (·.changes)).sum
  let next := { next with lastChanges := count, totalChanges := state.totalChanges + count }
  Execution.remember next
  return (next,[{ changes := count }])

end SQLeanite.CoreTriggerProgram.RegisterInput
