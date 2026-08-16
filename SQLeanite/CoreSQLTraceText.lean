import SQLeanite.CoreSQLWriteText

namespace SQLeanite
namespace CoreSQLTraceText

/-!
# Transactional SQL write traces

This layer extends persisted write commands with BEGIN and ROLLBACK.  They do
not themselves require a disk delta, but they cannot be erased: both change
the transaction snapshot that determines the meaning of later commands.
-/

inductive TraceCommand where
  | write (command : CoreEndToEnd.WriteCommand)
  | begin
  | rollback

def TraceCommand.toCore : TraceCommand → Core.Command
  | .write command => command.toCore
  | .begin => .begin
  | .rollback => .rollback

def TraceEffect (command : TraceCommand) (state next : Core.State)
    (result : Core.Result) : Prop :=
  match command with
  | .write command => CoreEndToEnd.WriteEffect command state next result
  | .begin =>
      state.transactionSnapshot = none ∧
        next.database = state.database ∧
        next.transactionSnapshot = some state.database ∧ result = {}
  | .rollback =>
      state.transactionSnapshot.isSome = true ∧
        next.database = state.transactionSnapshot.getD state.database ∧
        next.transactionSnapshot = none ∧ result = {}

theorem execute_exact (command : TraceCommand)
    {state next : Core.State} {result : Core.Result}
    (success : Core.execute state command.toCore = .ok (next, result)) :
    TraceEffect command state next result := by
  cases command with
  | write command => exact CoreEndToEnd.execute_write_exact command success
  | begin =>
      unfold TraceCommand.toCore Core.execute at success
      cases snapshot : state.transactionSnapshot with
      | none =>
          simp [snapshot] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨snapshot, rfl, rfl, rfl⟩
      | some database => simp [snapshot] at success
  | rollback =>
      unfold TraceCommand.toCore Core.execute at success
      cases snapshot : state.transactionSnapshot with
      | none => simp [snapshot] at success
      | some database =>
          simp [snapshot] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨by simp [snapshot], by simp [snapshot], rfl, rfl⟩

def executeCommands (state : Core.State) (commands : List TraceCommand) :
    Except String (Core.State × List Core.Result) :=
  CoreSQL.runCoreCommands state (commands.map (·.toCore))

theorem executeCommands_append (state : Core.State)
    (left right : List TraceCommand) :
    executeCommands state (left ++ right) =
      match executeCommands state left with
      | .error message => .error message
      | .ok (middle, leftResults) =>
          match executeCommands middle right with
          | .error message => .error message
          | .ok (next, rightResults) =>
              .ok (next, leftResults ++ rightResults) := by
  unfold executeCommands
  rw [List.map_append, CoreSQL.runCoreCommands_append]
  rfl

theorem map_write_toCore (commands : List CoreEndToEnd.WriteCommand) :
    (commands.map TraceCommand.write).map (·.toCore) =
      commands.map (·.toCore) := by
  induction commands with
  | nil => rfl
  | cons command commands induction =>
      simp [TraceCommand.toCore, induction]

theorem executeCommands_write (state : Core.State)
    (commands : List CoreEndToEnd.WriteCommand) :
    executeCommands state (commands.map TraceCommand.write) =
      CoreSQLWriteText.executeWriteCommands state commands := by
  unfold executeCommands CoreSQLWriteText.executeWriteCommands
  rw [map_write_toCore]

inductive TranslatedBlock (state : Core.State) :
    Statement → List TraceCommand → Prop where
  | write {statement : Statement} {command : CoreEndToEnd.WriteCommand}
      (translated : CoreSQLWriteText.TranslatedWrite state statement command) :
      TranslatedBlock state statement [.write command]
  | insertRows {statement : Statement}
      {commands : List CoreEndToEnd.WriteCommand}
      (translated : CoreSQLWriteText.TranslatedInsertRows
        state statement commands) :
      TranslatedBlock state statement (commands.map .write)
  | begin : TranslatedBlock state .begin [.begin]
  | rollback : TranslatedBlock state .rollback [.rollback]

theorem executeStatement_eq_commands
    {state : Core.State} {statement : Statement} {commands : List TraceCommand}
    (translated : TranslatedBlock state statement commands) :
    CoreSQL.executeStatement state statement = executeCommands state commands := by
  cases translated with
  | write translated =>
      exact (CoreSQLWriteText.executeStatement_block_eq_core
        (.single translated)).trans (executeCommands_write state [_]).symm
  | insertRows translated =>
      rw [CoreSQLWriteText.executeStatement_insertRows_eq_core translated,
        executeCommands_write]
  | begin => rfl
  | rollback => rfl

inductive TranslatedTrace : Core.State → List Statement →
    List TraceCommand → Prop where
  | nil (state : Core.State) : TranslatedTrace state [] []
  | cons {state : Core.State} {statement : Statement}
      {statements : List Statement} {headCommands tailCommands : List TraceCommand}
      (head : TranslatedBlock state statement headCommands)
      (tail : ∀ next results,
        executeCommands state headCommands = .ok (next, results) →
        TranslatedTrace next statements tailCommands) :
      TranslatedTrace state (statement :: statements)
        (headCommands ++ tailCommands)

theorem runStatements_eq_commands
    {state : Core.State} {statements : List Statement}
    {commands : List TraceCommand}
    (translated : TranslatedTrace state statements commands) :
    CoreSQL.runStatements state statements = executeCommands state commands := by
  induction translated with
  | nil state => rfl
  | @cons state statement statements headCommands tailCommands head tail
      induction =>
      unfold CoreSQL.runStatements
      rw [executeStatement_eq_commands head, executeCommands_append]
      cases headExecution : executeCommands state headCommands with
      | error message => simp [headExecution]
      | ok outcome =>
          rcases outcome with ⟨middle, headResults⟩
          have tailEquality := induction middle headResults headExecution
          simp only
          rw [tailEquality]
          cases tailExecution : executeCommands middle tailCommands with
          | error message =>
              simp [headExecution, tailExecution, Except.instMonad,
                Except.bind, Except.pure, pure]
          | ok outcome =>
              rcases outcome with ⟨next, tailResults⟩
              simp [headExecution, tailExecution, Except.instMonad,
                Except.bind, Except.pure, pure]

inductive TraceEffects : List TraceCommand → Core.State → Core.State →
    List Core.Result → Prop where
  | nil (state : Core.State) : TraceEffects [] state state []
  | cons {command : TraceCommand} {commands : List TraceCommand}
      {state middle next : Core.State} {result : Core.Result}
      {results : List Core.Result}
      (head : TraceEffect command state middle result)
      (tail : TraceEffects commands middle next results) :
      TraceEffects (command :: commands) state next (result :: results)

theorem executeCommands_exact : ∀ (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result),
    executeCommands state commands = .ok (next, results) →
    TraceEffects commands state next results
  | [], state, next, results, success => by
      simp [executeCommands, CoreSQL.runCoreCommands] at success
      rcases success with ⟨rfl, rfl⟩
      exact .nil state
  | command :: commands, state, next, results, success => by
      unfold executeCommands at success
      simp only [List.map_cons, CoreSQL.runCoreCommands] at success
      cases headExecution : Core.execute state command.toCore with
      | error message =>
          simp [headExecution, Except.instMonad, Except.bind] at success
      | ok headOutcome =>
          rcases headOutcome with ⟨middle, result⟩
          cases tailExecution : CoreSQL.runCoreCommands middle
              (commands.map (·.toCore)) with
          | error message =>
              simp [headExecution, tailExecution, Except.instMonad,
                Except.bind] at success
          | ok tailOutcome =>
              rcases tailOutcome with ⟨actualNext, actualResults⟩
              simp [headExecution, tailExecution, Except.instMonad,
                Except.bind, Except.pure, pure] at success
              rcases success with ⟨rfl, rfl⟩
              exact .cons (execute_exact command headExecution)
                (executeCommands_exact commands middle actualNext
                  actualResults tailExecution)

inductive SupportedText (state : Core.State) (text : String)
    (commands : List TraceCommand) : Prop where
  | intro (statements : Array Statement)
      (parsed : CoreTokenGrammar.Parses text statements)
      (translated : TranslatedTrace state statements.toList commands) :
      SupportedText state text commands

theorem execute_eq_commands
    {state : Core.State} {text : String} {commands : List TraceCommand}
    (supported : SupportedText state text commands) :
    CoreSQL.execute state text = executeCommands state commands := by
  rcases supported with ⟨statements, parsed, translated⟩
  rcases parsed with ⟨certificate, certified, statementList⟩
  simp only [CoreSQL.execute, certified, statementList,
    Except.instMonad, Except.bind]
  exact runStatements_eq_commands translated

theorem execute_success
    {state next : Core.State} {text : String} {commands : List TraceCommand}
    {results : List Core.Result}
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results)) :
    TraceEffects commands state next results := by
  exact executeCommands_exact commands state next results
    ((execute_eq_commands supported).symm.trans success)

/-- A supported multi-statement transaction, including BEGIN/ROLLBACK, has
its exact logical trace and the FSCQ-style old-or-new recovery guarantee. -/
theorem executeText_commit_crash_atomic
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
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
    TraceEffects commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some next.database.canonicalize) := by
  exact ⟨execute_success supported success,
    CoreDurability.rollbackWrites_represents_crash_atomic
      state.database next.database oldImage writes oldRepresents
      postImage.representsDatabase phase recoveredMain recoveredJournal
      outcome⟩

/-- Stronger localized form of the headline write theorem.  The post-image is
not admitted as one opaque decoder equation: catalog, table, index, and header
facts are supplied separately and composed by the storage refinement. -/
theorem executeText_localized_commit_crash_atomic
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (localized : CoreDurability.LocalizedRepresentation oldImage writes
      next.database)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain recoveredJournal) :
    TraceEffects commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
          some next.database.canonicalize) := by
  exact executeText_commit_crash_atomic text commands state next results
    oldImage writes supported success oldRepresents (.components localized)
    phase recoveredMain recoveredJournal outcome

/-- End-to-end localized point-update theorem over the exact value returned by
the live rollback writer.  The SQL trace, logical state transition, physical
table/index delta, post-image certificate, crash outcome, and POSIX request
list all share `committed.prepared.writes`; no caller-selected replacement
write list appears in the conclusion. -/
theorem executeText_committedLocalizedIndexedSingle_crash_atomic
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (chunkState : CoreChunkPageState.State)
    (delta : CoreChunkPageDelta.StateDelta)
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta
      chunkState next.database delta)
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (indexed : delta.table.before.table.indexes ≠ [])
    (single : chunkState.tables = [delta.table.before])
    (noFree : delta.after.freePages = [])
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) chunkState)
    (onImage : committed.prepared.OnImage oldImage)
    (oldHeader : CoreDurability.SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
    (beforeInline :
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem
          prepared.updated).1)).encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem prepared.updated).1)).nextOverflow =
        some afterEncoding)
    (afterInline : afterEncoding.overflowPages = [])
    (journalExact : committed.journal =
      GrowableStorage.makeJournal oldImage committed.prepared.writes)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        committed.prepared.writes phase) recoveredMain recoveredJournal) :
    TraceEffects commands state next results ∧
      ((CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some state.database.canonicalize ∨
        CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some next.database.canonicalize) ∧
       committed.requests =
         POSIXVFS.persistentCommitPlan oldImage committed.prepared.writes) := by
  have postImage : CoreDurability.PostImageCertificate oldImage
      committed.prepared.writes next.database := by
    have certificate :=
      CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingle
        prepared indexed single noFree committed oldImage physical onImage
        oldHeader emptyFreelist beforeInline afterEncoding afterEncoded
        afterInline
    have endpoints := CoreChunkPageDelta.updateState?_endpoints prepared.updated
    simpa [endpoints.2] using certificate
  have atomic := executeText_commit_crash_atomic text commands state next
    results oldImage committed.prepared.writes supported success oldRepresents
    postImage phase recoveredMain recoveredJournal outcome
  exact ⟨atomic.1, atomic.2,
    committed.trace_eq_commitPlan oldImage journalExact⟩

/-- Semantic-row form of the live localized SQL-text theorem.  Inline storage
is derived from the pre/post logical trees; the only remaining encoding
argument is the equation returned by the executable encoder itself. -/
theorem executeText_committedLocalizedIndexedSingleOfRowsInline_crash_atomic
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (chunkState : CoreChunkPageState.State)
    (delta : CoreChunkPageDelta.StateDelta)
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta
      chunkState next.database delta)
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (indexed : delta.table.before.table.indexes ≠ [])
    (single : chunkState.tables = [delta.table.before])
    (noFree : delta.after.freePages = [])
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) chunkState)
    (onImage : committed.prepared.OnImage oldImage)
    (oldHeader : CoreDurability.SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
    (beforeRowsInline : CorePageCodec.NodeRowsInline
      delta.table.before.table.schema delta.table.before.tree.root)
    (afterRowsInline : CorePageCodec.NodeRowsInline
      delta.table.after.table.schema delta.table.after.tree.root)
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      (Classical.choose (physical.exists_table delta.table.before
        (CoreChunkPageDelta.updateState?_selected_mem prepared.updated).1)).nextOverflow =
        some afterEncoding)
    (journalExact : committed.journal =
      GrowableStorage.makeJournal oldImage committed.prepared.writes)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        committed.prepared.writes phase) recoveredMain recoveredJournal) :
    TraceEffects commands state next results ∧
      ((CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some state.database.canonicalize ∨
        CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some next.database.canonicalize) ∧
       committed.requests =
         POSIXVFS.persistentCommitPlan oldImage committed.prepared.writes) := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  have beforeInline : before.encoding.overflowPages = [] :=
    CorePageCodec.encodeChunkNodeWithOverflow_inline
      delta.table.before.table.schema delta.table.before.tree.root
        before.nextOverflow before.encoding beforeRowsInline before.encoded
  have afterEncoded' : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding := by
    simpa [before, selected] using afterEncoded
  have afterInline : afterEncoding.overflowPages = [] :=
    CorePageCodec.encodeChunkNodeWithOverflow_inline
      delta.table.after.table.schema delta.table.after.tree.root
        before.nextOverflow afterEncoding afterRowsInline afterEncoded'
  exact executeText_committedLocalizedIndexedSingle_crash_atomic text commands
    state next results chunkState delta prepared committed oldImage supported
    success oldRepresents indexed single noFree physical onImage oldHeader
    emptyFreelist (by simpa [before, selected] using beforeInline) afterEncoding
    afterEncoded afterInline journalExact phase recoveredMain recoveredJournal
    outcome

/-- Multi-table end-to-end SQL-text crash theorem.  Every unchanged table is
framed by allocator page separation, while the selected table is justified by
the same semantic inline-row and live encoder facts as the YCSB theorem. -/
theorem executeText_committedLocalizedIndexedInlineTables_crash_atomic
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (chunkState : CoreChunkPageState.State)
    (delta : CoreChunkPageDelta.StateDelta)
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta
      chunkState next.database delta)
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (indexed : delta.table.before.table.indexes ≠ [])
    (noFree : delta.after.freePages = [])
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) chunkState)
    (onImage : committed.prepared.OnImage oldImage)
    (oldHeader : CoreDurability.SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
    (allRowsInline : ∀ old ∈ chunkState.tables,
      CorePageCodec.NodeRowsInline old.table.schema old.tree.root)
    (afterRowsInline : CorePageCodec.NodeRowsInline
      delta.table.after.table.schema delta.table.after.tree.root)
    (journalExact : committed.journal =
      GrowableStorage.makeJournal oldImage committed.prepared.writes)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        committed.prepared.writes phase) recoveredMain recoveredJournal) :
    TraceEffects commands state next results ∧
      ((CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some state.database.canonicalize ∨
        CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some next.database.canonicalize) ∧
       committed.requests =
         POSIXVFS.persistentCommitPlan oldImage committed.prepared.writes) := by
  have postImage : CoreDurability.PostImageCertificate oldImage
      committed.prepared.writes next.database := by
    have certificate :=
      CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedInlineOfInlineRows
        prepared indexed noFree committed oldImage physical onImage oldHeader
          emptyFreelist allRowsInline afterRowsInline
    have endpoints := CoreChunkPageDelta.updateState?_endpoints prepared.updated
    simpa [endpoints.2] using certificate
  have atomic := executeText_commit_crash_atomic text commands state next
    results oldImage committed.prepared.writes supported success oldRepresents
    postImage phase recoveredMain recoveredJournal outcome
  exact ⟨atomic.1, atomic.2,
    committed.trace_eq_commitPlan oldImage journalExact⟩

/-- Strongest localized SQL-text theorem: the live tree encoder equation and
semantic row bounds determine the complete overflow-aware representation.
There is no separately supplied general-encoder value or no-overflow equation. -/
theorem executeText_committedLocalizedIndexedSingleOfInlineTree_crash_atomic
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (chunkState : CoreChunkPageState.State)
    (delta : CoreChunkPageDelta.StateDelta)
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta
      chunkState next.database delta)
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (indexed : delta.table.before.table.indexes ≠ [])
    (single : chunkState.tables = [delta.table.before])
    (noFree : delta.after.freePages = [])
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) chunkState)
    (onImage : committed.prepared.OnImage oldImage)
    (oldHeader : CoreDurability.SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
    (beforeRowsInline : CorePageCodec.NodeRowsInline
      delta.table.before.table.schema delta.table.before.tree.root)
    (afterRowsInline : CorePageCodec.NodeRowsInline
      delta.table.after.table.schema delta.table.after.tree.root)
    (afterPages : List CorePageCodec.NumberedPage)
    (afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterPages)
    (journalExact : committed.journal =
      GrowableStorage.makeJournal oldImage committed.prepared.writes)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        committed.prepared.writes phase) recoveredMain recoveredJournal) :
    TraceEffects commands state next results ∧
      ((CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some state.database.canonicalize ∨
        CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some next.database.canonicalize) ∧
       committed.requests =
         POSIXVFS.persistentCommitPlan oldImage committed.prepared.writes) := by
  let selected := CoreChunkPageDelta.updateState?_selected_mem prepared.updated
  let before := Classical.choose
    (physical.exists_table delta.table.before selected.1)
  let afterEncoding : CorePageCodec.OverflowEncoding := {
    treePages := afterPages
    overflowPages := []
    nextPage := before.nextOverflow }
  have afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding := by
    exact CorePageCodec.encodeChunkNodeWithOverflow_of_inline
      delta.table.after.table.schema delta.table.after.tree.root
        before.nextOverflow afterPages afterRowsInline afterTree
  exact
    executeText_committedLocalizedIndexedSingleOfRowsInline_crash_atomic
      text commands state next results chunkState delta prepared committed
        oldImage supported success oldRepresents indexed single noFree physical
          onImage oldHeader emptyFreelist beforeRowsInline afterRowsInline
            afterEncoding (by simpa [before, selected] using afterEncoded)
              journalExact phase recoveredMain recoveredJournal outcome

/-- Fully structural live theorem for inline point updates.  The exact SQL
execution, prepared delta and returned commit determine every physical page;
only semantic row bounds and the VFS image/refinement facts remain premises. -/
theorem executeText_committedLocalizedIndexedSingleOfInlineRows_crash_atomic
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (chunkState : CoreChunkPageState.State)
    (delta : CoreChunkPageDelta.StateDelta)
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta
      chunkState next.database delta)
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (indexed : delta.table.before.table.indexes ≠ [])
    (single : chunkState.tables = [delta.table.before])
    (noFree : delta.after.freePages = [])
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) chunkState)
    (onImage : committed.prepared.OnImage oldImage)
    (oldHeader : CoreDurability.SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
    (beforeRowsInline : CorePageCodec.NodeRowsInline
      delta.table.before.table.schema delta.table.before.tree.root)
    (afterRowsInline : CorePageCodec.NodeRowsInline
      delta.table.after.table.schema delta.table.after.tree.root)
    (journalExact : committed.journal =
      GrowableStorage.makeJournal oldImage committed.prepared.writes)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        committed.prepared.writes phase) recoveredMain recoveredJournal) :
    TraceEffects commands state next results ∧
      ((CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some state.database.canonicalize ∨
        CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some next.database.canonicalize) ∧
       committed.requests =
         POSIXVFS.persistentCommitPlan oldImage committed.prepared.writes) := by
  have postImage : CoreDurability.PostImageCertificate oldImage
      committed.prepared.writes next.database := by
    have certificate :=
      CoreDurability.CoreFileAdapter.PreparedOrdinaryDelta.postImageCertificateOfCommittedIndexedSingleOfInlineRows
        prepared indexed single noFree committed oldImage physical onImage
          oldHeader emptyFreelist beforeRowsInline afterRowsInline
    have endpoints := CoreChunkPageDelta.updateState?_endpoints prepared.updated
    simpa [endpoints.2] using certificate
  have atomic := executeText_commit_crash_atomic text commands state next
    results oldImage committed.prepared.writes supported success oldRepresents
    postImage phase recoveredMain recoveredJournal outcome
  exact ⟨atomic.1, atomic.2,
    committed.trace_eq_commitPlan oldImage journalExact⟩

/-- Exact VeriBetrKV/YCSB specialization: literal TEXT-primary schema,
64-bit-hash keys and one 512-byte field.  The row-shape premises discharge all
inline/encoder facts through `YCSBRow.inline`; no benchmark adaptation appears
in the statement. -/
theorem executeText_committedLocalizedIndexedSingleYCSB_crash_atomic
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (chunkState : CoreChunkPageState.State)
    (delta : CoreChunkPageDelta.StateDelta)
    (prepared : CoreFileAdapter.PreparedOrdinaryDelta
      chunkState next.database delta)
    (committed : CoreFileAdapter.CommittedLocalizedDelta
      delta.after.freePages prepared.writes)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (oldRepresents : CoreDurability.RepresentsDatabase oldImage state.database)
    (indexed : delta.table.before.table.indexes ≠ [])
    (single : chunkState.tables = [delta.table.before])
    (noFree : delta.after.freePages = [])
    (physical : CoreLocalizedRepresentation.DatabaseOnSource
      (CorePageSource.ofStorageImage oldImage) chunkState)
    (onImage : committed.prepared.OnImage oldImage)
    (oldHeader : CoreDurability.SQLiteHeaderMatches oldImage)
    (emptyFreelist : oldHeader.FreelistEmpty)
    (beforeYCSB : CorePageCodec.YCSBTableState delta.table.before)
    (afterYCSB : CorePageCodec.YCSBTableState delta.table.after)
    (journalExact : committed.journal =
      GrowableStorage.makeJournal oldImage committed.prepared.writes)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        committed.prepared.writes phase) recoveredMain recoveredJournal) :
    TraceEffects commands state next results ∧
      ((CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some state.database.canonicalize ∨
        CoreDecode.decode
            (PhysicalJournalRecovery.recoverBytes recoveredMain
              recoveredJournal) = some next.database.canonicalize) ∧
       committed.requests =
         POSIXVFS.persistentCommitPlan oldImage committed.prepared.writes) := by
  exact executeText_committedLocalizedIndexedSingleOfInlineRows_crash_atomic
    text commands state next results chunkState delta prepared committed
      oldImage supported success oldRepresents indexed single noFree physical
        onImage oldHeader emptyFreelist beforeYCSB.rowsInline
          afterYCSB.rowsInline journalExact phase recoveredMain
            recoveredJournal outcome

theorem executeText_returned_recovers_new
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedText state text commands)
    (success : CoreSQL.execute state text = .ok (next, results))
    (newRepresents : CoreDurability.RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) next.database)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes .committed)
      recoveredMain recoveredJournal) :
    TraceEffects commands state next results ∧
      CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some next.database.canonicalize := by
  exact ⟨execute_success supported success,
    CoreDurability.rollbackWrites_represents_returned_recovers_new
      next.database oldImage writes newRepresents recoveredMain
      recoveredJournal outcome⟩

theorem executeText_recovery_crash_trace_atomic
    (text : String) (commands : List TraceCommand)
    (state next : Core.State) (results : List Core.Result)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (supported : SupportedText state text commands)
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
    TraceEffects commands state next results ∧
      (CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some state.database.canonicalize ∨
        CoreDecode.decode
          (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
          some next.database.canonicalize) := by
  exact ⟨execute_success supported success,
    CoreDurability.rollbackWrites_represents_recovery_crash_trace_atomic
      state.database next.database oldImage writes oldRepresents newRepresents
      phase recoveredMain finalMain journal outcome recoveryCrashes⟩

end CoreSQLTraceText
end SQLeanite
