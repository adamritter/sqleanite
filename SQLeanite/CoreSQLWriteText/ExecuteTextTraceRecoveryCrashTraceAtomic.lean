import SQLeanite.CoreSQLWriteText.OneResult

namespace SQLeanite
namespace CoreSQLWriteText

theorem executeText_trace_recovery_crash_trace_atomic
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteTraceText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain finalMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain (some journal))
    (recoveryCrashes : GrowableStorage.RecoveryCrashTrace journal
      recoveredMain finalMain) :
    WriteTraceEffect commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some next.database.canonicalize) := by
  exact ⟨writeTrace_success supported success,
    CoreDurability.rollbackWrites_represents_recovery_crash_trace_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain finalMain journal outcome recoveryCrashes⟩

inductive SupportedInsertRowsText (state : Core.State) (text : String)
    (commands : List CoreEndToEnd.WriteCommand) : Prop where
  | intro (statement : Statement)
      (parsed : CoreTokenGrammar.Parses text #[statement])
      (translated : TranslatedInsertRows state statement commands) :
      SupportedInsertRowsText state text commands

theorem execute_insertRows_eq_core
    {state : Core.State} {text : String}
    {commands : List CoreEndToEnd.WriteCommand}
    (supported : SupportedInsertRowsText state text commands) :
    CoreSQL.execute state text = executeWriteCommands state commands := by
  rcases supported with ⟨statement, parsed, translated⟩
  rcases parsed with ⟨certificate, certified, statements⟩
  simp only [CoreSQL.execute, certified, statements, bind, Functor.map, Except.bind,
    CoreSQL.runStatements]
  rw [executeStatement_insertRows_eq_core translated]
  cases execution : executeWriteCommands state commands <;>
    simp [execution, bind, Functor.map, Except.bind, pure, Except.pure, pure]

theorem insertRows_trace_success
    {state next : Core.State} {text : String}
    {commands : List CoreEndToEnd.WriteCommand} {results : List Core.Result}
    (supported : SupportedInsertRowsText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results)) :
    WriteTraceEffect commands state next results := by
  exact executeWriteCommands_exact commands state next results
    ((execute_insertRows_eq_core supported).symm.trans success)

theorem executeText_insertRows_commit_crash_atomic
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedInsertRowsText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
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
    WriteTraceEffect commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some next.database.canonicalize) := by
  exact ⟨insertRows_trace_success supported success,
    CoreDurability.rollbackWrites_represents_crash_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain recoveredJournal outcome⟩

theorem executeText_insertRows_returned_recovers_new
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedInsertRowsText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes .committed)
      recoveredMain recoveredJournal) :
    WriteTraceEffect commands state next results ∧
      CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some next.database.canonicalize := by
  exact ⟨insertRows_trace_success supported success,
    CoreDurability.rollbackWrites_represents_returned_recovers_new
      next.database oldImage writes newRepresents recoveredMain
      recoveredJournal outcome⟩

theorem executeText_insertRows_recovery_crash_trace_atomic
    (text : String) (commands : List CoreEndToEnd.WriteCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedInsertRowsText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain finalMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain (some journal))
    (recoveryCrashes : GrowableStorage.RecoveryCrashTrace journal
      recoveredMain finalMain) :
    WriteTraceEffect commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some next.database.canonicalize) := by
  exact ⟨insertRows_trace_success supported success,
    CoreDurability.rollbackWrites_represents_recovery_crash_trace_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain finalMain journal outcome recoveryCrashes⟩

/-- A single supported write statement beginning at an actual SQL string. -/
inductive SupportedWriteText (state : Core.State) (text : String)
    (command : CoreEndToEnd.WriteCommand) : Prop where
  | intro (statement : Statement)
      (parsed : CoreTokenGrammar.Parses text #[statement])
      (translated : TranslatedWrite state statement command) :
      SupportedWriteText state text command

theorem execute_eq_core
    {state : Core.State} {text : String}
    {command : CoreEndToEnd.WriteCommand}
    (supported : SupportedWriteText state text command) :
    CoreSQL.execute state text = oneResult
      (Core.execute state command.toCore) := by
  rcases supported with ⟨statement, parsed, translated⟩
  rcases parsed with ⟨certificate, certified, statements⟩
  simp only [CoreSQL.execute, certified, statements, bind, Functor.map, Except.bind,
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
concrete page-level rollback theorem.  The post-image evidence must identify
the actual construction path (ordinary localized, bulk, or freelist-padded);
an opaque decoder equality is no longer an admissible premise. -/
theorem executeText_commit_crash_atomic
    (text : String) (command : CoreEndToEnd.WriteCommand)
    (state next : Core.State) (result : Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteText state text command)
    (success : CoreSQL.execute state text = .ok (next, [result]))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (postImage : CoreDurability.PostImageCertificate oldImage writes
      next.database)
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
    oldRepresents postImage.representsDatabase phase recoveredMain
    recoveredJournal outcome

theorem executeText_returned_recovers_new
    (text : String) (command : CoreEndToEnd.WriteCommand)
    (state next : Core.State) (result : Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedWriteText state text command)
    (success : CoreSQL.execute state text = .ok (next, [result]))
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes .committed)
      recoveredMain recoveredJournal) :
    CoreEndToEnd.WriteEffect command state next result ∧
      CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some next.database.canonicalize := by
  exact CoreEndToEnd.executeCommand_returned_recovers_new command state next
    result oldImage writes (core_success_of_execute supported success)
    newRepresents recoveredMain recoveredJournal outcome

theorem executeText_recovery_crash_trace_atomic
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
    (recoveredMain finalMain :
      GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain (some journal))
    (recoveryCrashes : GrowableStorage.RecoveryCrashTrace journal
      recoveredMain finalMain) :
    CoreEndToEnd.WriteEffect command state next result ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some next.database.canonicalize) := by
  exact CoreEndToEnd.executeCommand_recovery_crash_trace_atomic command state
    next result oldImage writes (core_success_of_execute supported success)
    oldRepresents newRepresents phase recoveredMain finalMain journal outcome
    recoveryCrashes

end CoreSQLWriteText

end SQLeanite
