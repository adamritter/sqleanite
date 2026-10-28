import SQLeanite.CoreTriggerProgram.Rows

namespace SQLeanite.CoreTriggerProgram.RegisterInput

/-- The existing external plain-table coroutine is independent of target
writes. Other SELECT plans retain their own materialization and compilation. -/
def eligible (state : Core.State) : Statement → Bool
  | .insertSelect target _ query _ outputs =>
      outputs.isEmpty && query.sources.size == 1 && query.compounds.isEmpty &&
        query.valueRows.isNone && query.orderBy.isEmpty && query.groupBy.isEmpty &&
        query.having.isNone && !query.distinct && !CoreScalarQuery.has query.compoundHeight query &&
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
  selection : CoreSQL.RegisterSelection
  table : Core.Table

/-- Source/target compilation completes before execution starts, even if the
source is empty. The result contains actual checked schemas and source rows. -/
def prepare (state : Core.State) (statement : Statement) : Except String Prepared := do
  let compiled ← CoreGeneratedSQL.statement state statement
  let compiled ← CoreDeclaredCollationSQL.statement state compiled
  let .insertSelect target columns query action _ := CoreConnectionSQL.statement state compiled
    | throw "register input requires INSERT SELECT"
  let preparation ← CoreGeneratedSQL.preparation state target
  let selection ← CoreSQL.prepareRegisterSelection state target columns query action preparation
  let some table := CoreNames.table? state.database target | throw s!"no such table: {target}"
  return { target, query, action, selection, table }

def execute (point : PointExecutor) (execute : String → ScopedEffectExecutor)
    (remove : ScopedEffectExecutor) (read : ScopedRead) (state : Core.State)
    (prepared : Prepared) (source : String) : ExecutionM (Core.State × List Core.Result) := do
  let { target, query, action, selection, table } := prepared
  let (next,results) ← CoreSQL.insertRegisterRowsWith (m := ExecutionM) (fun current input => do
      let command := Statement.insert target selection.columns #[input] action #[]
      let (next,results) ← executeRows point execute remove read current table command source []
      let next := pending state next
      Execution.remember next
      return (next,results))
    state selection.context selection.projection query.where_ selection.rows query.offset query.limit
  let next ← if table.schema.autoIncrement then do
      let counter ← CoreAutoIncrement.beginContext next table.schema.name
      CoreAutoIncrement.finish next counter
    else pure next
  let count := (results.map (·.changes)).sum
  let next := { next with lastChanges := count, totalChanges := state.totalChanges + count }
  Execution.remember next
  return (next,[{ changes := count }])

end SQLeanite.CoreTriggerProgram.RegisterInput
