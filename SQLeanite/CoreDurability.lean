import SQLeanite.CorePageCodec
import SQLeanite.CoreFreelistCodec
import SQLeanite.CoreFileAdapter
import SQLeanite.CorePageSource
import SQLeanite.PhysicalJournalRecovery

namespace SQLeanite
namespace CoreDurability

/-!
# Core database durability composition

This module is the missing lifting step between the growable page/journal
protocol and the canonical Core SQLite codec.  The protocol theorem speaks
about page-image equivalence; the results below turn that into an old-or-new
theorem about databases obtained by decoding the recovered bytes.
-/

theorem imagePages_storageImage (image : CoreFile.Image) :
    PhysicalJournalRecovery.imagePages (CoreFileAdapter.storageImage image) =
      image.pages.map CoreFile.Page.storage := by
  apply List.ext_getElem
  · rw [PhysicalJournalRecovery.imagePages_length]
    simp [CoreFileAdapter.storageImage, CoreFile.Image.pageCount]
  · intro index leftBound rightBound
    have bound : index < image.pages.length := by simpa using rightBound
    simp [PhysicalJournalRecovery.imagePages, CoreFileAdapter.storageImage,
      CoreFile.Image.pageCount, leftBound, rightBound, bound]

theorem imageBytes_storageImage (image : CoreFile.Image) :
    PhysicalJournalRecovery.imageBytes (CoreFileAdapter.storageImage image) =
      image.fileBytes := by
  unfold PhysicalJournalRecovery.imageBytes CoreFile.Image.fileBytes
  rw [imagePages_storageImage]
  induction image.pages with
  | nil => rfl
  | cons page pages induction =>
      simp [DiskFormat.encodePages, CoreFile.Page.storage, induction]

theorem decode_imageBytes_encodeBulk (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image) :
    CoreDecode.decode
        (PhysicalJournalRecovery.imageBytes
          (CoreFileAdapter.storageImage image)) =
      some database.canonicalize := by
  rw [imageBytes_storageImage]
  exact CorePageCodec.decode_encodeBulk utf8 database image encoded

/-- A physical page image represents a Core database when the actual bytes
read by recovery decode to that database.  Keeping this relation independent
of a particular encoder is what lets the same crash theorem cover canonical
bulk images, freelist-padded images, and page-local updates. -/
def RepresentsDatabase
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (database : Core.Database) : Prop :=
  CoreDecode.decode (PhysicalJournalRecovery.imageBytes image) =
    some database.canonicalize

/-- The byte decoder's non-logical framing obligations for a growable image.
The catalog/table/index meaning is deliberately kept in
`PageSourceRepresents`; this relation records only the SQLite header fields
which connect the byte string to that page source. -/
inductive SQLiteHeaderMatches
    (image : GrowableStorage.Image PhysicalCodec.pageSize) : Prop where
  | intro (header : FileFormat.DatabaseHeader) (suffix : List UInt8)
      (decoded : FileFormat.decodeDatabaseHeader
        (PhysicalJournalRecovery.imageBytes image) = some (header, suffix))
      (pageCount : header.databaseSizePages.val = image.pageCount)
      (pageSize : header.headerPrefix.pageSizeField.val =
        PhysicalCodec.pageSize)
      (reserved : header.headerPrefix.reservedSpace = 0)
      (utf8 : header.textEncoding.val = 1) :
      SQLiteHeaderMatches image

/-- Component-wise physical representation plus the four SQLite framing
fields implies representation by the public whole-byte decoder.  This is the
composition rule needed by localized writes: they may preserve or re-prove
catalog/table/index components independently and close the byte-level result
without another execution or validation pass. -/
theorem pageSourceRepresents_storageImage
    {image : GrowableStorage.Image PhysicalCodec.pageSize}
    {database : Core.Database}
    (header : SQLiteHeaderMatches image)
    (represents : CoreDecode.PageSourceRepresents
      (CorePageSource.ofStorageImage image) database) :
    RepresentsDatabase image database := by
  rcases header with ⟨header, suffix, decoded, pageCount, pageSize,
    reserved, utf8⟩
  unfold RepresentsDatabase CoreDecode.decode
  rw [decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [pageCount]
  rw [dif_pos pageSize, dif_pos reserved, dif_pos utf8]
  have fileLength :
      (PhysicalJournalRecovery.imageBytes image).length =
        image.pageCount * PhysicalCodec.pageSize := by
    unfold PhysicalJournalRecovery.imageBytes
    rw [DiskFormat.encodePages_length,
      PhysicalJournalRecovery.imagePages_length]
    exact Nat.mul_comm _ _
  rw [dif_pos fileLength, CorePageSource.pages_imageBytes]
  exact represents.decode

theorem storageImage_encodeBulk_represents
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image) :
    RepresentsDatabase (CoreFileAdapter.storageImage image) database :=
  decode_imageBytes_encodeBulk utf8 database image encoded

theorem storageImage_padded_represents
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (layout : CoreMultiFreelist.Layout)
    (encoded : CorePageCodec.encodeBulk database = some layout.image) :
    RepresentsDatabase
      (CoreFileAdapter.storageImage layout.paddedImage) database := by
  unfold RepresentsDatabase
  rw [imageBytes_storageImage]
  exact CoreFreelistCodec.decode_paddedImage utf8 database layout encoded

/-- Fully representation-parametric FSCQ lifting.  Unlike the older
`CoreFile.Image` wrapper below, the target here is the exact result of an
arbitrary page-write list.  This is the theorem consumed by the live
localized writer once its component-wise codec preservation proof is
available. -/
theorem rollbackWrites_represents_crash_atomic
    (oldDatabase newDatabase : Core.Database)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (oldRepresents : RepresentsDatabase oldImage oldDatabase)
    (newRepresents : RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) newDatabase)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
      recoveredMain recoveredJournal) :
    CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some oldDatabase.canonicalize ∨
      CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some newDatabase.canonicalize := by
  rcases GrowableStorage.rollbackCommit_crash_atomic oldImage writes phase
      recoveredMain recoveredJournal outcome with restored | committed
  · left
    unfold PhysicalJournalRecovery.recoverBytes
    rw [PhysicalJournalRecovery.imageBytes_eq_of_equiv restored]
    exact oldRepresents
  · right
    unfold PhysicalJournalRecovery.recoverBytes
    rw [PhysicalJournalRecovery.imageBytes_eq_of_equiv committed]
    exact newRepresents

theorem rollbackWrites_represents_returned_recovers_new
    (newDatabase : Core.Database)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (newRepresents : RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) newDatabase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes .committed)
      recoveredMain recoveredJournal) :
    CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
      some newDatabase.canonicalize := by
  have recovered := GrowableStorage.rollbackCommit_committed_recovers_new
    oldImage writes recoveredMain recoveredJournal outcome
  unfold PhysicalJournalRecovery.recoverBytes
  rw [PhysicalJournalRecovery.imageBytes_eq_of_equiv recovered]
  exact newRepresents

theorem rollbackWrites_represents_recovery_crash_trace_atomic
    (oldDatabase newDatabase : Core.Database)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (oldRepresents : RepresentsDatabase oldImage oldDatabase)
    (newRepresents : RepresentsDatabase
      (GrowableStorage.applyWrites oldImage writes) newDatabase)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain finalMain :
      GrowableStorage.Image PhysicalCodec.pageSize)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage writes phase)
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
  exact rollbackWrites_represents_crash_atomic oldDatabase newDatabase
    oldImage writes oldRepresents newRepresents phase recoveredMain
    (some journal) outcome

/-- Representation-parametric crash atomicity.  This is the reusable FSCQ
lifting theorem: the storage protocol supplies old-or-new page equivalence;
the two representation premises say what those byte images mean. -/
theorem rollbackCommit_represents_crash_atomic
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
      recoveredMain recoveredJournal) :
    CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some oldDatabase.canonicalize ∨
      CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some newDatabase.canonicalize := by
  rcases CoreFileAdapter.commit_crash_atomic oldImage newImage doesNotShrink
      phase recoveredMain recoveredJournal outcome with restored | committed
  · left
    have bytes := PhysicalJournalRecovery.imageBytes_eq_of_equiv restored
    unfold PhysicalJournalRecovery.recoverBytes
    rw [bytes]
    exact oldRepresents
  · right
    have bytes := PhysicalJournalRecovery.imageBytes_eq_of_equiv committed
    unfold PhysicalJournalRecovery.recoverBytes
    rw [bytes]
    exact newRepresents

theorem rollbackCommit_padded_crash_atomic
    (utf8 : CoreDecode.UTF8Roundtrips)
    (oldDatabase newDatabase : Core.Database)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (layout : CoreMultiFreelist.Layout)
    (oldRepresents : RepresentsDatabase oldImage oldDatabase)
    (newEncoded : CorePageCodec.encodeBulk newDatabase = some layout.image)
    (doesNotShrink : oldImage.pageCount ≤
      (CoreFileAdapter.storageImage layout.paddedImage).pageCount)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        (CoreFileAdapter.transactionWrites oldImage layout.paddedImage) phase)
      recoveredMain recoveredJournal) :
    CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some oldDatabase.canonicalize ∨
      CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some newDatabase.canonicalize := by
  exact rollbackCommit_represents_crash_atomic oldDatabase newDatabase oldImage
    layout.paddedImage oldRepresents
    (storageImage_padded_represents utf8 newDatabase layout newEncoded)
    doesNotShrink phase recoveredMain recoveredJournal outcome

/-- A crash at every rollback-journal checkpoint decodes to the old or new
Core database, not merely an equivalent abstract page image. -/
theorem rollbackCommit_core_crash_atomic
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
      recoveredMain recoveredJournal) :
    CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some oldDatabase.canonicalize ∨
      CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
        some newDatabase.canonicalize := by
  exact rollbackCommit_represents_crash_atomic oldDatabase newDatabase
    (CoreFileAdapter.storageImage oldImage) newImage
    (storageImage_encodeBulk_represents utf8 oldDatabase oldImage oldEncoded)
    (storageImage_encodeBulk_represents utf8 newDatabase newImage newEncoded)
    doesNotShrink phase recoveredMain recoveredJournal outcome

/-- Representation-parametric returned-commit theorem.  Unlike the canonical
bulk corollary below, this applies directly to any localized or padded target
image once its decoder representation theorem is available. -/
theorem rollbackCommit_represents_returned_recovers_new
    (newDatabase : Core.Database)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (newImage : CoreFile.Image)
    (newRepresents : RepresentsDatabase
      (CoreFileAdapter.storageImage newImage) newDatabase)
    (doesNotShrink :
      oldImage.pageCount ≤ (CoreFileAdapter.storageImage newImage).pageCount)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        (CoreFileAdapter.transactionWrites oldImage newImage) .committed)
      recoveredMain recoveredJournal) :
    CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
      some newDatabase.canonicalize := by
  have recovered := GrowableStorage.rollbackCommit_committed_recovers_new
    oldImage (CoreFileAdapter.transactionWrites oldImage newImage)
    recoveredMain recoveredJournal outcome
  have target := GrowableStorage.apply_deltaWrites_equiv oldImage
    (CoreFileAdapter.storageImage newImage) doesNotShrink
  have bytes := PhysicalJournalRecovery.imageBytes_eq_of_equiv
    (recovered.trans target)
  unfold PhysicalJournalRecovery.recoverBytes
  rw [bytes]
  exact newRepresents

theorem rollbackCommit_padded_returned_recovers_new
    (utf8 : CoreDecode.UTF8Roundtrips)
    (newDatabase : Core.Database)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (layout : CoreMultiFreelist.Layout)
    (newEncoded : CorePageCodec.encodeBulk newDatabase = some layout.image)
    (doesNotShrink : oldImage.pageCount ≤
      (CoreFileAdapter.storageImage layout.paddedImage).pageCount)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState oldImage
        (CoreFileAdapter.transactionWrites oldImage layout.paddedImage)
          .committed)
      recoveredMain recoveredJournal) :
    CoreDecode.decode
        (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
      some newDatabase.canonicalize := by
  exact rollbackCommit_represents_returned_recovers_new newDatabase oldImage
    layout.paddedImage
    (storageImage_padded_represents utf8 newDatabase layout newEncoded)
    doesNotShrink recoveredMain recoveredJournal outcome

/-- After the commit protocol has returned, the old disjunct is impossible:
every permitted crash image decodes to the committed Core database. -/
theorem rollbackCommit_core_returned_recovers_new
    (utf8 : CoreDecode.UTF8Roundtrips)
    (newDatabase : Core.Database)
    (oldImage newImage : CoreFile.Image)
    (newEncoded : CorePageCodec.encodeBulk newDatabase = some newImage)
    (doesNotShrink :
      (CoreFileAdapter.storageImage oldImage).pageCount ≤
        (CoreFileAdapter.storageImage newImage).pageCount)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState
        (CoreFileAdapter.storageImage oldImage)
        (CoreFileAdapter.transactionWrites
          (CoreFileAdapter.storageImage oldImage) newImage) .committed)
      recoveredMain recoveredJournal) :
    CoreDecode.decode
      (PhysicalJournalRecovery.recoverBytes recoveredMain recoveredJournal) =
      some newDatabase.canonicalize := by
  exact rollbackCommit_represents_returned_recovers_new newDatabase
    (CoreFileAdapter.storageImage oldImage) newImage
    (storageImage_encodeBulk_represents utf8 newDatabase newImage newEncoded)
    doesNotShrink recoveredMain recoveredJournal outcome

def recoverRepeatedBytes
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option
      (GrowableStorage.Journal PhysicalCodec.pageSize))
    (restartCount : Nat) : List UInt8 :=
  PhysicalJournalRecovery.imageBytes
    (GrowableStorage.recoverRepeatedly recoveredMain recoveredJournal restartCount)

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
