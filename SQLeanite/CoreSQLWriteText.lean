import SQLeanite.CoreSQLText
import SQLeanite.CoreEndToEnd

namespace SQLeanite
namespace CoreSQLWriteText

/-!
# Supported SQL write text to durable Core commands

This module makes the write side of the text boundary explicit.  The relation
below is independent of execution success: its premises are parser and
translation equations plus the syntactic restrictions of the supported Core
surface.  The first version covers one persisted command per SQL statement;
multi-row INSERT and multi-statement transaction traces are composed later.
-/

private def oneResult
    (execution : Except String (Core.State × Core.Result)) :
    Except String (Core.State × List Core.Result) :=
  (fun outcome => (outcome.1, [outcome.2])) <$> execution

/-- A parsed statement translates to exactly one persisted Core command. -/
inductive TranslatedWrite (state : Core.State) :
    Statement → CoreEndToEnd.WriteCommand → Prop where
  | createTable (name : String) (columns : Array ColumnDef)
      (constraints : Array TableConstraintDef) (ifNotExists : Bool)
      (schema : Core.Schema)
      (translated : CoreSQL.schema name columns constraints = .ok schema) :
      TranslatedWrite state
        (.createTable name columns constraints ifNotExists)
        (.createTable schema)
  | createIndex (name table : String) (expression : Expr)
      (ifNotExists : Bool) (stored : Core.Table) (columnName : String)
      (columnIndex : Nat)
      (found : state.database.findTable? (CoreSQL.canonical table) =
        some stored)
      (expressionName : CoreSQL.indexColumnName? expression = some columnName)
      (columnFound : CoreSQL.column stored.schema columnName = .ok columnIndex) :
      TranslatedWrite state
        (.createIndex name table #[expression] false none ifNotExists)
        (.createIndex (CoreSQL.canonical table)
          { name := CoreSQL.canonical name, column := columnIndex })
  | insert (table : String) (columns : Option (Array String))
      (expressions : Array Expr) (conflict : ConflictAction)
      (allowed : conflict = .default ∨ conflict = .abort)
      (stored : Core.Table) (values : List Core.Value)
      (found : state.database.findTable? (CoreSQL.canonical table) =
        some stored)
      (translated : CoreSQL.rowValues stored.schema columns expressions =
        .ok values) :
      TranslatedWrite state (.insert table columns #[expressions] conflict)
        (.insert (CoreSQL.canonical table) values)
  | replace (table : String) (columns : Option (Array String))
      (expressions : Array Expr) (stored : Core.Table)
      (values : List Core.Value)
      (found : state.database.findTable? (CoreSQL.canonical table) =
        some stored)
      (translated : CoreSQL.rowValues stored.schema columns expressions =
        .ok values) :
      TranslatedWrite state
        (.insert table columns #[expressions] .replace)
        (.replace (CoreSQL.canonical table) values)
  | delete (table : String) (alias : Option String) (where_ : Option Expr)
      (stored : Core.Table) (predicate : Option Core.Predicate)
      (found : state.database.findTable? (CoreSQL.canonical table) =
        some stored)
      (translated : where_.mapM (CoreSQL.predicate stored.schema) =
        .ok predicate) :
      TranslatedWrite state (.delete table alias where_ #[])
        (.deleteWhere (CoreSQL.canonical table) predicate)
  | update (table : String) (alias : Option String)
      (assignments : Array (String × Expr)) (where_ : Option Expr)
      (conflict : ConflictAction)
      (allowed : conflict = .default ∨ conflict = .abort)
      (stored : Core.Table) (updates : List (Nat × Core.Value))
      (predicate : Option Core.Predicate)
      (found : state.database.findTable? (CoreSQL.canonical table) =
        some stored)
      (assignmentsTranslated :
        CoreSQL.updateAssignments stored.schema assignments.toList =
          .ok updates)
      (predicateTranslated : where_.mapM
        (CoreSQL.predicate stored.schema) = .ok predicate) :
      TranslatedWrite state
        (.update table alias assignments where_ conflict)
        (.updateWhere (CoreSQL.canonical table) updates predicate)
  | commit : TranslatedWrite state .commit .commit

theorem executeStatement_eq_core
    {state : Core.State} {statement : Statement}
    {command : CoreEndToEnd.WriteCommand}
    (translated : TranslatedWrite state statement command) :
    CoreSQL.executeStatement state statement =
      oneResult (Core.execute state command.toCore) := by
  cases translated with
  | createTable name columns constraints ifNotExists schema translation =>
      simp [CoreSQL.executeStatement, translation,
        CoreSQL.executeCommand_eq_core, CoreEndToEnd.WriteCommand.toCore,
        Except.instMonad, Except.bind, Except.pure, pure, oneResult]
  | createIndex name table expression ifNotExists stored columnName
      columnIndex found expressionName columnFound =>
      simp [CoreSQL.executeStatement, found, expressionName, columnFound,
        CoreSQL.executeCommand_eq_core, CoreEndToEnd.WriteCommand.toCore,
        Except.instMonad, Except.bind, Except.pure, pure, oneResult]
  | insert table columns expressions conflict allowed stored values found
      translation =>
      rcases allowed with rfl | rfl <;>
        simp [CoreSQL.executeStatement, found,
          CoreSQL.insertRows_singleton, translation,
          CoreSQL.executeCommand_eq_core, CoreEndToEnd.WriteCommand.toCore,
          Except.instMonad, Except.bind, Except.pure, pure, oneResult]
  | replace table columns expressions stored values found translation =>
      simp [CoreSQL.executeStatement, found, CoreSQL.insertRows_singleton,
        translation, CoreSQL.executeCommand_eq_core,
        CoreEndToEnd.WriteCommand.toCore, Except.instMonad, Except.bind, pure,
        Except.pure, oneResult]
  | delete table alias where_ stored predicate found translation =>
      simp [CoreSQL.executeStatement, found, translation,
        CoreSQL.executeCommand_eq_core, CoreEndToEnd.WriteCommand.toCore,
        Except.instMonad, Except.bind, Except.pure, pure, oneResult]
  | update table alias assignments where_ conflict allowed stored updates
      predicate found assignmentsTranslated predicateTranslated =>
      rcases allowed with rfl | rfl <;>
        simp [CoreSQL.executeStatement, found, assignmentsTranslated,
          predicateTranslated, CoreSQL.executeCommand_eq_core,
          CoreEndToEnd.WriteCommand.toCore, Except.instMonad, Except.bind,
          Except.pure, pure, oneResult]
  | commit => rfl

/-- A single supported write statement beginning at an actual SQL string. -/
inductive SupportedWriteText (state : Core.State) (text : String)
    (command : CoreEndToEnd.WriteCommand) : Prop where
  | intro (statement : Statement)
      (parsed : parse text = .ok #[statement])
      (translated : TranslatedWrite state statement command) :
      SupportedWriteText state text command

theorem execute_eq_core
    {state : Core.State} {text : String}
    {command : CoreEndToEnd.WriteCommand}
    (supported : SupportedWriteText state text command) :
    CoreSQL.execute state text = oneResult
      (Core.execute state command.toCore) := by
  rcases supported with ⟨statement, parsed, translated⟩
  simp only [CoreSQL.execute, parsed, Except.instMonad, Except.bind,
    CoreSQL.runStatements]
  rw [executeStatement_eq_core translated]
  unfold oneResult
  cases Core.execute state command.toCore <;> rfl

theorem core_success_of_execute
    {state next : Core.State} {text : String}
    {command : CoreEndToEnd.WriteCommand} {result : Core.Result}
    (supported : SupportedWriteText state text command)
    (success : CoreSQL.execute state text = .ok (next, [result])) :
    Core.execute state command.toCore = .ok (next, result) := by
  have mapped : oneResult (Core.execute state command.toCore) =
      .ok (next, [result]) := (execute_eq_core supported).symm.trans success
  unfold oneResult at mapped
  cases execution : Core.execute state command.toCore with
  | error message =>
      rw [execution] at mapped
      change (Except.error message :
        Except String (Core.State × List Core.Result)) =
          .ok (next, [result]) at mapped
      cases mapped
  | ok outcome =>
      rcases outcome with ⟨actualNext, actualResult⟩
      rw [execution] at mapped
      change Except.ok (actualNext, [actualResult]) =
        Except.ok (next, [result]) at mapped
      have pairEqual : (actualNext, [actualResult]) = (next, [result]) :=
        Except.ok.inj mapped
      have stateEqual : actualNext = next := congrArg Prod.fst pairEqual
      have listEqual : [actualResult] = [result] := congrArg Prod.snd pairEqual
      have resultEqual : actualResult = result := (List.cons.inj listEqual).1
      rw [stateEqual, resultEqual]

/-- Supported SQL write text, not a pre-parsed command, composes with the
concrete page-level rollback theorem.  The representation premises are the
remaining localized-codec link; no parser or execution equation is assumed by
the caller beyond the transparent `SupportedWriteText` witness. -/
theorem executeText_commit_crash_atomic
    (text : String) (command : CoreEndToEnd.WriteCommand)
    (state next : Core.State) (result : Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteText state text command)
    (success : CoreSQL.execute state text = .ok (next, [result]))
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
    CoreEndToEnd.WriteEffect command state next result ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some next.database.canonicalize) := by
  exact CoreEndToEnd.executeCommand_commit_crash_atomic command state next
    result oldImage writes (core_success_of_execute supported success)
    oldRepresents newRepresents phase recoveredMain recoveredJournal outcome

end CoreSQLWriteText
end SQLeanite
