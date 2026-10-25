import SQLeanite.CoreWriteBytes
import SQLeanite.CoreDurability

namespace SQLeanite
namespace CoreEndToEnd

/-!
# Core write semantics composed with durable recovery

This module packages the seven persisted Core commands without weakening their
individual postconditions.  It then composes those postconditions with the
representation-parametric rollback theorem.  The result starts at a parsed
Core command; the separate SQL-text front-end theorem remains the final link.
-/

/-- Exactly the Core commands whose successful result may have to be persisted.
`commit` is included even though it leaves the logical database unchanged. -/
inductive WriteCommand where
  | createTable (schema : Core.Schema)
  | createIndex (table : String) (index : Core.Index)
  | insert (table : String) (values : List Core.Value)
  | replace (table : String) (values : List Core.Value)
  | deleteWhere (table : String) (predicate : Option Core.Predicate)
  | updateWhere (table : String) (assignments : List (Nat × Core.Value))
      (predicate : Option Core.Predicate)
  | commit

def WriteCommand.toCore : WriteCommand → Core.Command
  | .createTable schema => .createTable schema
  | .createIndex table index => .createIndex table index
  | .insert table values => .insert table values
  | .replace table values => .replace table values
  | .deleteWhere table predicate => .deleteWhere table predicate
  | .updateWhere table assignments predicate =>
      .updateWhere table assignments predicate
  | .commit => .commit

/-- The exact logical effect of each persisted command.  In particular, every
table-targeting operation carries the frame condition for all other tables. -/
def WriteEffect (command : WriteCommand) (state next : Core.State)
    (result : Core.Result) : Prop :=
  match command with
  | .createTable schema =>
      ∃ table,
        Core.emptyTable schema = .ok table ∧
        next.database.tables = table :: state.database.tables ∧
        next.database.findTable? schema.name = some table ∧
        next.transactionSnapshot = state.transactionSnapshot ∧
        result = {} ∧
        ∀ other, other ≠ schema.name →
          next.database.findTable? other = state.database.findTable? other
  | .createIndex tableName index =>
      ∃ table replacement,
        state.database.findTable? tableName = some table ∧
        replacement.schema = table.schema ∧
        replacement.indexes = table.indexes ++ [index] ∧
        replacement.rows = table.rows ∧
        next.database.findTable? tableName = some replacement ∧
        next.transactionSnapshot = state.transactionSnapshot ∧
        result = {} ∧
        ∀ other, other ≠ tableName →
          next.database.findTable? other = state.database.findTable? other
  | .insert tableName values =>
      ∃ table replacement row,
        state.database.findTable? tableName = some table ∧
        table.createRow values = .ok row ∧
        row.WellFormed table.schema ∧
        (∀ existing ∈ table.rows, existing.rowid.value ≠ row.rowid.value) ∧
        table.findDeclaredPrimary? row = none ∧
        replacement.rows = Core.orderedUpsert row table.rows ∧
        next.database.findTable? tableName = some replacement ∧
        next.transactionSnapshot = state.transactionSnapshot ∧
        result = { changes := 1 } ∧
        ∀ other, other ≠ tableName →
          next.database.findTable? other = state.database.findTable? other
  | .replace tableName values =>
      ∃ table replacement row,
        state.database.findTable? tableName = some table ∧
        table.createReplacementRow values = .ok row ∧
        replacement.rows = Core.orderedUpsert row table.rows ∧
        next.database.findTable? tableName = some replacement ∧
        next.transactionSnapshot = state.transactionSnapshot ∧
        result = { changes := 1 } ∧
        ∀ other, other ≠ tableName →
          next.database.findTable? other = state.database.findTable? other
  | .deleteWhere tableName predicate =>
      ∃ table replacement,
        state.database.findTable? tableName = some table ∧
        replacement.rows = table.rows.filter
          (fun row => !Core.selects predicate row) ∧
        next.database.findTable? tableName = some replacement ∧
        next.transactionSnapshot = state.transactionSnapshot ∧
        result = { changes := table.rows.length - replacement.rows.length } ∧
        ∀ other, other ≠ tableName →
          next.database.findTable? other = state.database.findTable? other
  | .updateWhere tableName assignments predicate =>
      ∃ table replacement changes,
        state.database.findTable? tableName = some table ∧
        table.updateWhere assignments predicate = .ok (replacement, changes) ∧
        next.database.findTable? tableName = some replacement ∧
        next.transactionSnapshot = state.transactionSnapshot ∧
        result = { changes } ∧
        ∀ other, other ≠ tableName →
          next.database.findTable? other = state.database.findTable? other
  | .commit =>
      state.transactionSnapshot.isSome = true ∧
        next.database = state.database ∧
        next.transactionSnapshot = none ∧ result = {} ∧
        ∀ tableName,
          next.database.findTable? tableName =
            state.database.findTable? tableName

/-- The single dispatcher does not erase the command-specific logical
postcondition: it is obtained directly from the corresponding live executor
theorem in every case. -/
theorem execute_write_exact (command : WriteCommand)
    {state next : Core.State} {result : Core.Result}
    (success : Core.execute state command.toCore = .ok (next, result)) :
    WriteEffect command state next result := by
  cases command with
  | createTable schema => exact Core.execute_createTable_exact success
  | createIndex table index => exact Core.execute_createIndex_exact success
  | insert table values => exact Core.execute_insert_exact success
  | replace table values => exact Core.execute_replace_exact success
  | deleteWhere table predicate => exact Core.execute_deleteWhere_exact success
  | updateWhere table assignments predicate =>
      exact Core.execute_updateWhere_exact success
  | commit => exact Core.execute_commit_exact success

/-- Parsed Core write execution followed by an arbitrary exact page delta is
crash atomic at the public SQLite byte decoder. -/
theorem executeCommand_commit_crash_atomic
    (command : WriteCommand) (state next : Core.State) (result : Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (success : Core.execute state command.toCore = .ok (next, result))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain recoveredJournal) :
    WriteEffect command state next result ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some next.database.canonicalize) := by
  exact ⟨execute_write_exact command success,
    CoreDurability.rollbackWrites_represents_crash_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain recoveredJournal outcome⟩

/-- Once commit has returned, the same composition excludes the old state. -/
theorem executeCommand_returned_recovers_new
    (command : WriteCommand) (state next : Core.State) (result : Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (success : Core.execute state command.toCore = .ok (next, result))
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes .committed)
      recoveredMain recoveredJournal) :
    WriteEffect command state next result ∧
      CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some next.database.canonicalize := by
  exact ⟨execute_write_exact command success,
    CoreDurability.rollbackWrites_represents_returned_recovers_new
      next.database oldImage writes newRepresents recoveredMain
      recoveredJournal outcome⟩

/-- A finite sequence of crashes while copying journal pre-images preserves
the same command-level old-or-new result. -/
theorem executeCommand_recovery_crash_trace_atomic
    (command : WriteCommand) (state next : Core.State) (result : Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (success : Core.execute state command.toCore = .ok (next, result))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain finalMain :
      GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain (some journal))
    (recoveryCrashes : GrowableStorage.RecoveryCrashTrace journal
      recoveredMain finalMain) :
    WriteEffect command state next result ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some next.database.canonicalize) := by
  exact ⟨execute_write_exact command success,
    CoreDurability.rollbackWrites_represents_recovery_crash_trace_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain finalMain journal outcome recoveryCrashes⟩

end CoreEndToEnd
end SQLeanite
