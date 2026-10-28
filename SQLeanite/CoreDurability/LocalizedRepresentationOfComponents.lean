import SQLeanite.CoreDurability.CoreFileAdapterPreparedOrdinaryDeltaPostImageCertificateOfCommittedIndexedInline

namespace SQLeanite
namespace CoreDurability

/-- Variant of the constructor that accepts one compositional proof per table
instead of the already-collapsed `mapM` equation. -/
def localizedRepresentation_of_components
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (database : Core.Database)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pageZero : GrowableStorage.PageWrite PhysicalCodec.pageSize)
    (member : pageZero ∈ writes) (zero : pageZero.pageId = 0)
    (header : FileFormat.DatabaseHeader) (pageSuffix : List UInt8)
    (headerBytes : pageZero.page.bytes.toList =
      FileFormat.encodeDatabaseHeader header ++ pageSuffix)
    (pageCount : header.databaseSizePages.val =
      (GrowableStorage.applyWrites oldImage writes).pageCount)
    (pageSize : header.headerPrefix.pageSizeField.val =
      PhysicalCodec.pageSize)
    (reserved : header.headerPrefix.reservedSpace = 0)
    (utf8 : header.textEncoding.val = 1)
    (catalog : List CoreDecode.CatalogEntry)
    (catalogDecoded :
      CoreDecode.decodeCatalogForOpen pageZero.page.bytes.toList = some catalog)
    (tables : CoreLocalizedRepresentation.TablesDecode
      (localizedSource oldImage writes)
      (catalog.filter (fun entry => entry.kind == "table")) database.tables)
    (indexesRead :
      CoreDecode.applyIndexesForOpen (localizedSource oldImage writes)
          database.withoutIndexes
          (catalog.filter (fun entry => entry.kind == "index")) =
        some database.canonicalize) :
    LocalizedRepresentation oldImage writes database :=
  localizedRepresentation_of_pageZeroWrite oldImage writes database distinct
    pageZero member zero header pageSuffix headerBytes pageCount pageSize
    reserved utf8 catalog catalogDecoded tables.mapM indexesRead

/-- Fully decomposed constructor: exact table pages, exact index pages, and
independently decoded index metadata establish the two logical decoder fields.
Unlike `localizedRepresentation_of_components`, no whole index-decoder
equation is left as an input premise. -/
def localizedRepresentation_of_certificates
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (database : Core.Database)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pageZero : GrowableStorage.PageWrite PhysicalCodec.pageSize)
    (member : pageZero ∈ writes) (zero : pageZero.pageId = 0)
    (header : FileFormat.DatabaseHeader) (pageSuffix : List UInt8)
    (headerBytes : pageZero.page.bytes.toList =
      FileFormat.encodeDatabaseHeader header ++ pageSuffix)
    (pageCount : header.databaseSizePages.val =
      (GrowableStorage.applyWrites oldImage writes).pageCount)
    (pageSize : header.headerPrefix.pageSizeField.val =
      PhysicalCodec.pageSize)
    (reserved : header.headerPrefix.reservedSpace = 0)
    (utf8 : header.textEncoding.val = 1)
    (catalog : List CoreDecode.CatalogEntry)
    (catalogDecoded :
      CoreDecode.decodeCatalogForOpen pageZero.page.bytes.toList = some catalog)
    (tables : CoreLocalizedRepresentation.TablesDecode
      (localizedSource oldImage writes)
      (catalog.filter (fun entry => entry.kind == "table")) database.tables)
    (physicalIndexes : CoreLocalizedRepresentation.IndexGroupsDecode
      (localizedSource oldImage writes)
      (database.tables.map Core.Table.withoutIndexes)
      (catalog.filter (fun entry => entry.kind == "index")))
    (indexMetadata : CoreLocalizedRepresentation.IndexMetadataGroups
      database.tables
      (catalog.filter (fun entry => entry.kind == "index"))) :
    LocalizedRepresentation oldImage writes database :=
  localizedRepresentation_of_components oldImage writes database distinct
    pageZero member zero header pageSuffix headerBytes pageCount pageSize
    reserved utf8 catalog catalogDecoded tables
    (CoreLocalizedRepresentation.applyIndexesForOpen_of_index_certificates
      (localizedSource oldImage writes) database _ physicalIndexes indexMetadata)

/-- Fully decomposed constructor for the common localized path which leaves
page zero untouched.  Header and catalog facts are transported from the old
represented image; table and index witnesses describe only the components
whose page reads can have changed.  Freelist pages may occur in `writes` as
long as page zero and the recorded page count remain unchanged. -/
def localizedRepresentation_of_unchangedPageZero
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (database : Core.Database)
    (notWritten : ∀ write ∈ writes, 0 ≠ write.pageId)
    (positive : 0 < oldImage.pageCount)
    (header : FileFormat.DatabaseHeader) (pageSuffix : List UInt8)
    (headerBytes : (oldImage.read 0).bytes.toList =
      FileFormat.encodeDatabaseHeader header ++ pageSuffix)
    (pageCount : header.databaseSizePages.val =
      (GrowableStorage.applyWrites oldImage writes).pageCount)
    (pageSize : header.headerPrefix.pageSizeField.val =
      PhysicalCodec.pageSize)
    (reserved : header.headerPrefix.reservedSpace = 0)
    (utf8 : header.textEncoding.val = 1)
    (catalog : List CoreDecode.CatalogEntry)
    (catalogDecoded :
      (CorePageSource.ofStorageImage oldImage).readPage 1 >>=
        CoreDecode.decodeCatalogForOpen = some catalog)
    (tables : CoreLocalizedRepresentation.TablesDecode
      (localizedSource oldImage writes)
      (catalog.filter (fun entry => entry.kind == "table")) database.tables)
    (physicalIndexes : CoreLocalizedRepresentation.IndexGroupsDecode
      (localizedSource oldImage writes)
      (database.tables.map Core.Table.withoutIndexes)
      (catalog.filter (fun entry => entry.kind == "index")))
    (indexMetadata : CoreLocalizedRepresentation.IndexMetadataGroups
      database.tables
      (catalog.filter (fun entry => entry.kind == "index"))) :
    LocalizedRepresentation oldImage writes database := {
  header := sqliteHeaderMatches_of_unchangedPageZero oldImage writes
    notWritten positive header pageSuffix headerBytes pageCount pageSize
    reserved utf8
  components := ⟨catalog,
    catalogRead_of_unchangedPageZero oldImage writes positive
      notWritten catalog catalogDecoded,
    tables.mapM,
    CoreLocalizedRepresentation.applyIndexesForOpen_of_index_certificates
      (localizedSource oldImage writes) database _ physicalIndexes indexMetadata⟩ }

theorem LocalizedRepresentation.pageSourceRepresents
    {oldImage : GrowableStorage.Image PhysicalCodec.pageSize}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    {database : Core.Database}
    (certificate : LocalizedRepresentation oldImage writes database) :
    CoreDecode.PageSourceRepresents
      (localizedSource oldImage writes) database := by
  rcases certificate.components with
    ⟨catalog, catalogRead, tablesRead, indexesRead⟩
  exact .intro catalog catalogRead tablesRead indexesRead

/-- Component proofs close the public whole-byte representation theorem. -/
theorem LocalizedRepresentation.representsDatabase
    {oldImage : GrowableStorage.Image PhysicalCodec.pageSize}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    {database : Core.Database}
    (certificate : LocalizedRepresentation oldImage writes database) :
    RepresentsDatabase (GrowableStorage.applyWrites oldImage writes)
      database := by
  apply pageSourceRepresents_storageImage certificate.header
  simpa [localizedSource] using certificate.pageSourceRepresents

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

end CoreDurability

end SQLeanite
