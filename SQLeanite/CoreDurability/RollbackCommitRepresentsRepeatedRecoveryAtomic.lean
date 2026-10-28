import SQLeanite.CoreDurability.LocalizedRepresentationOfComponents

namespace SQLeanite
namespace CoreDurability

theorem rollbackCommit_represents_repeated_recovery_atomic
    (oldDatabase newDatabase : Core.Database)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (newImage : CoreFile.Image)
    (oldRepresents : RepresentsDatabase oldImage oldDatabase)
    (newRepresents : RepresentsDatabase
      (CoreFileAdapter.storageImage newImage) newDatabase)
    (doesNotShrink :
      oldImage.pageCount ≤ (CoreFileAdapter.storageImage newImage).pageCount)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        (CoreFileAdapter.transactionWrites oldImage newImage) phase)
      recoveredMain recoveredJournal)
    (restartCount : Nat) :
    CoreDecode.decode
        (recoverRepeatedBytes recoveredMain recoveredJournal restartCount) =
        some oldDatabase.canonicalize ∨
      CoreDecode.decode
        (recoverRepeatedBytes recoveredMain recoveredJournal restartCount) =
        some newDatabase.canonicalize := by
  rw [recoverRepeatedBytes, GrowableStorage.recoverRepeatedly_eq_recover]
  exact rollbackCommit_represents_crash_atomic oldDatabase newDatabase oldImage
    newImage oldRepresents newRepresents doesNotShrink phase recoveredMain
    recoveredJournal outcome

/-- Concrete database-level closure under crashes *inside* recovery.  Every
step in `recoveryCrashes` may persist an arbitrary subset/permutation of the
authenticated journal page copies; the final bytes still decode to the old or
new Core database. -/
theorem rollbackCommit_represents_recovery_crash_trace_atomic
    (oldDatabase newDatabase : Core.Database)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (newImage : CoreFile.Image)
    (oldRepresents : RepresentsDatabase oldImage oldDatabase)
    (newRepresents : RepresentsDatabase
      (CoreFileAdapter.storageImage newImage) newDatabase)
    (doesNotShrink :
      oldImage.pageCount ≤ (CoreFileAdapter.storageImage newImage).pageCount)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain finalMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        (CoreFileAdapter.transactionWrites oldImage newImage) phase)
      recoveredMain (some journal))
    (recoveryCrashes : GrowableStorage.RecoveryCrashTrace journal
      recoveredMain finalMain) :
    CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
        some oldDatabase.canonicalize ∨
      CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
        some newDatabase.canonicalize := by
  have stable := GrowableStorage.recoverWithJournal_after_recovery_trace
    journal recoveredMain finalMain recoveryCrashes
  unfold PhysicalJournalRecovery.recoverBytes
  rw [stable]
  exact rollbackCommit_represents_crash_atomic oldDatabase newDatabase oldImage
    newImage oldRepresents newRepresents doesNotShrink phase recoveredMain
    (some journal) outcome

theorem rollbackCommit_padded_recovery_crash_trace_atomic
    (utf8 : CoreDecode.UTF8Roundtrips)
    (oldDatabase newDatabase : Core.Database)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (layout : CoreMultiFreelist.Layout)
    (oldRepresents : RepresentsDatabase oldImage oldDatabase)
    (newEncoded : CorePageCodec.encodeBulk newDatabase = some layout.image)
    (doesNotShrink : oldImage.pageCount ≤
      (CoreFileAdapter.storageImage layout.paddedImage).pageCount)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain finalMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        (CoreFileAdapter.transactionWrites oldImage layout.paddedImage) phase)
      recoveredMain (some journal))
    (recoveryCrashes : GrowableStorage.RecoveryCrashTrace journal
      recoveredMain finalMain) :
    CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
        some oldDatabase.canonicalize ∨
      CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes finalMain (some journal)) =
        some newDatabase.canonicalize := by
  exact rollbackCommit_represents_recovery_crash_trace_atomic oldDatabase
    newDatabase oldImage layout.paddedImage oldRepresents
    (storageImage_padded_represents utf8 newDatabase layout newEncoded)
    doesNotShrink phase recoveredMain finalMain journal outcome recoveryCrashes

/-- Crashing and restarting the recovery process any finite number of times
does not enlarge the set of database outcomes. -/
theorem rollbackCommit_core_repeated_recovery_atomic
    (utf8 : CoreDecode.UTF8Roundtrips)
    (oldDatabase newDatabase : Core.Database)
    (oldImage newImage : CoreFile.Image)
    (oldEncoded : CorePageCodec.encodeBulk oldDatabase = some oldImage)
    (newEncoded : CorePageCodec.encodeBulk newDatabase = some newImage)
    (doesNotShrink :
      (CoreFileAdapter.storageImage oldImage).pageCount ≤
        (CoreFileAdapter.storageImage newImage).pageCount)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState
        (CoreFileAdapter.storageImage oldImage)
        (CoreFileAdapter.transactionWrites
          (CoreFileAdapter.storageImage oldImage) newImage) phase)
      recoveredMain recoveredJournal)
    (restartCount : Nat) :
    CoreDecode.decode
        (recoverRepeatedBytes recoveredMain recoveredJournal restartCount) =
        some oldDatabase.canonicalize ∨
      CoreDecode.decode
        (recoverRepeatedBytes recoveredMain recoveredJournal restartCount) =
        some newDatabase.canonicalize := by
  exact rollbackCommit_represents_repeated_recovery_atomic oldDatabase
    newDatabase (CoreFileAdapter.storageImage oldImage) newImage
    (storageImage_encodeBulk_represents utf8 oldDatabase oldImage oldEncoded)
    (storageImage_encodeBulk_represents utf8 newDatabase newImage newEncoded)
    doesNotShrink phase recoveredMain recoveredJournal outcome restartCount

end CoreDurability

end SQLeanite
