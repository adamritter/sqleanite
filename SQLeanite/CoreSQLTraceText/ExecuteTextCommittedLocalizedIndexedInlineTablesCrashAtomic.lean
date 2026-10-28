import SQLeanite.CoreSQLTraceText.TraceCommand

namespace SQLeanite
namespace CoreSQLTraceText

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
