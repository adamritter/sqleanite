import SQLeanite.AtomicFileReplacement
import SQLeanite.CoreCatalogImage
import SQLeanite.CoreFileAdapter.RowsForExpectedIndexEntries

namespace SQLeanite
namespace CoreFileAdapter

def lookupGeneratedIndexCandidates (paths : Paths) (tableName : String)
    (schema : Core.Schema) (query : Core.Query)
    (cache : Option PageReadCache := none) : IO (Option IndexLookup) := do
  let some geometry ← readGeneratedFileGeometry paths | return none
  lookupGeneratedIndexCandidatesWith geometry paths tableName schema query cache

/-- Cold ascending `ORDER BY indexed_column LIMIT n` for a stamped generated
image. The bounded cursor crosses as many leaves and promoted interior records
as necessary; rowid/value links are checked locally before normal Core
evaluation. -/
def lookupGeneratedOrderedPrefix (paths : Paths) (tableName : String)
    (schema : Core.Schema) (query : Core.Query) : IO (Option IndexLookup) := do
  let selected := match query.predicate, query.orderBy, query.limit,
      query.distinct with
    | none, [(column, false)], some limit, false => some (column, limit)
    | _, _, _, _ => none
  let some (column, limit) := selected | return none
  let some columnSpec := schema.columns[column]? | return none
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let some firstPage ← readPageBytes handle | return none
    let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
      return none
    let count := header.databaseSizePages.val
    unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
        header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
        metadata.byteSize.toNat = count * PhysicalCodec.pageSize &&
        CoreFile.hasGeneratedImageStamp header do return none
    let some catalog := CoreDecode.decodeCatalog firstPage | return none
    let some tableEntry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == tableName | return none
    let some tableSql := tableEntry.sql | return none
    let some decodedSchema := CoreDecode.parseTableSchema tableSql | return none
    unless decodedSchema = schema && schema.name = tableName do return none
    let some indexEntry := catalog.find? (generatedIndexEntryMatches schema
      tableName column columnSpec.name) | return none
    let reads ← IO.mkRef 0
    let base := preadPageSource paths.main count
    let source : CoreDecode.IOPageSource := {
      pageCount := count
      readPage := fun pageNumber => do
        reads.modify (· + 1)
        base.readPage pageNumber }
    let some entries ← CoreDecode.lookupIndexPrefixIOFrom source limit
        (count + 1) indexEntry.rootPage | return none
    let mut candidates := []
    for entry in entries do
      let some resolved ← CoreDecode.lookupTableRowidIOFrom schema source
          entry.rowid (count + 1) tableEntry.rootPage | return none
      let some row := resolved | return none
      unless row.rowid = entry.rowid && row.WellFormed schema &&
          row.value column = entry.value do return none
      candidates := row :: candidates
    return some ⟨candidates.reverse, ← reads.get⟩

def create (syncOps : SyncOps) (paths : Paths)
    (database : Core.Database) : IO Unit := do
  let image ← match CorePageCodec.encodeChecked database with
    | some image => pure image
    | none => throw (IO.userError "general MVP database exceeds the physical subset")
  if ← paths.journalTemp.pathExists then
    SyscallVFS.unlinkPath paths.journalTemp.toString
  if ← paths.journal.pathExists then
    SyscallVFS.unlinkPath paths.journal.toString
  IO.FS.writeBinFile paths.main (bytes image.fileBytes)
  IO.FS.writeBinFile paths.journal PhysicalJournalCodec.initialInactiveBytes
  syncOps.syncFile paths.main
  syncOps.syncFile paths.journal
  syncOps.syncDeletion paths.main

/-- Establish the durable inactive journal inode once.  A temporary name and
directory sync make this migration safe even for databases created by an
older SQLeanite version; recurrent commits never mutate the directory. -/
private def initializePersistentJournal (syncOps : SyncOps) (paths : Paths) :
    IO Unit := do
  unless ← paths.journal.pathExists do
    IO.FS.writeBinFile paths.journalTemp
      PhysicalJournalCodec.initialInactiveBytes
    syncOps.syncFile paths.journalTemp
    SyscallVFS.renamePath paths.journalTemp.toString paths.journal.toString
    syncOps.syncDeletion paths.main

/-- The current encoder has no representation for extension-owned reserved
bytes. Reject before journal activation or image publication until a writer
that preserves this geometry is implemented. -/
private def requireUnreservedWrite (path : System.FilePath) : IO Unit := do
  requireWritableFormat path
  let header ← readHeader path
  unless header.headerPrefix.reservedSpace = 0 do
    throw (IO.userError "unsupported reserved-byte database writes")

private def activatePersistentJournal (syncOps : SyncOps) (paths : Paths)
    (journal : PhysicalJournalCodec.PersistentEncodable) : IO Unit := do
  requireUnreservedWrite paths.main
  SyscallVFS.pwriteBytes paths.journal.toString 0
    (PhysicalJournalCodec.encodePersistentActiveBytes journal)
  syncOps.syncFile paths.journal

private def retirePersistentJournal (syncOps : SyncOps) (paths : Paths) :
    IO Unit := do
  SyscallVFS.pwriteBytes paths.journal.toString 0
    PhysicalJournalCodec.inactiveBytes
  syncOps.syncFile paths.journal

/-- Roll back a leftover journal, without reading the database back.

`commit` needs only this side effect, so keeping the reopen inside `recover`
made every commit pay a whole extra read-and-decode whose result was discarded. -/
def recoverInPlace (syncOps : SyncOps) (paths : Paths) : IO Unit := do
  if ← paths.journalTemp.pathExists then
    SyscallVFS.unlinkPath paths.journalTemp.toString
    syncOps.syncDeletion paths.main
  if ← paths.journal.pathExists then
    let encoded ← IO.FS.readBinFile paths.journal
    match PhysicalJournalCodec.decodePersistent encoded.data.toList with
    | none => throw (IO.userError "invalid general MVP rollback journal")
    | some none => pure ()
    | some (some journal) =>
        let current ← IO.FS.readBinFile paths.main
        let current := if current.size ≤ 1 then ByteArray.empty else current
        let currentPageCount := current.size / PhysicalCodec.pageSize
        unless current.size = currentPageCount * PhysicalCodec.pageSize do
          throw (IO.userError "misaligned general MVP main file during recovery")
        let recoveredMain ← match PhysicalJournalRecovery.decodeImage
            currentPageCount current.data.toList with
          | some image => pure image
          | none => throw (IO.userError
              "invalid paged general MVP main file during recovery")
        let restored := PhysicalJournalRecovery.recoverBytes recoveredMain
          (some journal)
        IO.FS.writeBinFile paths.main (bytes restored)
        syncOps.syncFile paths.main
        retirePersistentJournal syncOps paths
  else
    initializePersistentJournal syncOps paths

def recover (syncOps : SyncOps) (paths : Paths) : IO Core.Database := do
  recoverInPlace syncOps paths
  reopen paths

/-- The 4096-byte page-delta writer cannot reinterpret another geometry.
Only the validated full-file path may convert such a database. -/
def needsPageSizeConversion (paths : Paths) : IO Bool :=
  IO.FS.withFile paths.main .read fun handle => do
    let headerBytes ← handle.read 100
    let some header := headerOrEmpty headerBytes.data.toList (← paths.main.metadata).byteSize.toNat |
      throw (IO.userError "invalid database header before write")
    if let some message := SQLite.HeaderVersion.writeError? header then
      throw (IO.userError message)
    unless header.headerPrefix.reservedSpace = 0 do
      throw (IO.userError "unsupported reserved-byte database writes")
    return header.headerPrefix.pageSizeField.val != PhysicalCodec.pageSize

/-- Encode a complete canonical image before publication. This branch changes
the page size to 4096, and uses atomic image replacement rather than claiming
that the ordinary same-geometry rollback-journal trace was executed. -/
def convertPageSize (syncOps : SyncOps) (paths : Paths) (database : Core.Database)
    (updatedMetadata : Option CoreMultiFreelist.HeaderMetadata := none) :
    IO ValidatedOpenState := do
  requireUnreservedWrite paths.main
  recoverInPlace syncOps paths
  let main ← IO.FS.realPath paths.main
  let metadata ← main.metadata
  unless metadata.numLinks == 1 do
    throw (IO.userError "unsupported page-size conversion of a multiply linked database")
  let temporary : System.FilePath := main.toString ++ ".sqleanite-image.tmp"
  let old : GrowableStorage.Image PhysicalCodec.pageSize := {
    pageCount := 0, read := fun _ => Storage.Page.zero PhysicalCodec.pageSize }
  let oldHeader ← IO.FS.withFile main .read (fun handle => handle.read 100)
  let some metadata := CoreMultiFreelist.HeaderMetadata.decode? oldHeader.toList |
    throw (IO.userError "invalid application metadata before page-size conversion")
  let prepared ← match prepareBulkCommit? old database (some (updatedMetadata.getD metadata)) with
    | some prepared => pure prepared
    | none => throw (IO.userError "database exceeds the canonical image bounds")
  let validated ← match retainGeneratedState? prepared.state
      prepared.newImage.pageCount prepared.freePages with
    | some validated => pure validated
    | none => throw (IO.userError "converted image did not retain its validated state")
  let requests := AtomicFileReplacement.plan prepared.newImage.fileBytes
  for request in requests do
    match request with
    | .stage contents =>
        if ← temporary.pathExists then SyscallVFS.unlinkPath temporary.toString
        IO.FS.withFile temporary .write fun handle => do
          IO.setAccessRights temporary { user := { read := true, write := true } }
          handle.write (bytes contents)
    | .syncTemporary =>
        syncOps.syncFile temporary
        let actual ← IO.FS.readBinFile temporary
        unless actual.data.toList == prepared.newImage.fileBytes do
          throw (IO.userError "converted database image verification failed")
    | .publish => SyscallVFS.renamePath temporary.toString main.toString
    | .syncDirectory => syncOps.syncDeletion main
  return validated

/-- Page-size conversion with independently checked source-aware catalog
objects. This is an atomic whole-image replacement, not a same-geometry
rollback-journal commit. No view or schema identity is discarded. -/
def convertCatalogPageSize (syncOps : SyncOps) (paths : Paths) (database : Core.Database)
    (metadata : CoreMultiFreelist.HeaderMetadata) (declarations : List CoreDecode.CatalogEntry)
    (objects : CoreCatalogData.Objects) : IO Core.Database := do
  requireUnreservedWrite paths.main
  recoverInPlace syncOps paths
  let main ← IO.FS.realPath paths.main
  unless (← main.metadata).numLinks == 1 do
    throw (IO.userError "unsupported page-size conversion of a multiply linked database")
  let temporary : System.FilePath := main.toString ++ ".sqleanite-image.tmp"
  let old : GrowableStorage.Image PhysicalCodec.pageSize := {
    pageCount := 0, read := fun _ => Storage.Page.zero PhysicalCodec.pageSize }
  let header ← readHeader main
  let some image := CoreCatalogImage.encode 0 database header metadata [] declarations (some objects) |
    throw (IO.userError "cannot encode source-aware catalog conversion")
  let some checked := CoreCatalogImage.check old database image |
    throw (IO.userError "converted catalog image failed component validation")
  let some checked := CoreCatalogImage.attachObjects checked objects |
    throw (IO.userError "converted schema object identity validation failed")
  for request in AtomicFileReplacement.plan checked.image.fileBytes do
    match request with
    | .stage contents =>
        if ← temporary.pathExists then SyscallVFS.unlinkPath temporary.toString
        IO.FS.withFile temporary .write fun handle => do
          IO.setAccessRights temporary { user := { read := true, write := true } }
          handle.write (bytes contents)
    | .syncTemporary =>
        syncOps.syncFile temporary
        let actual ← IO.FS.readBinFile temporary
        unless actual.data.toList == checked.image.fileBytes do
          throw (IO.userError "converted catalog image verification failed")
    | .publish => SyscallVFS.renamePath temporary.toString main.toString
    | .syncDirectory => syncOps.syncDeletion main
  return checked.decoded

/-- Successful live publication retains the pure final-write preparation and
the equation tying the returned abstract syscall trace to that exact list. -/
structure CommittedLocalizedDelta
    (freePages : List Nat)
    (baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) where
  prepared : PreparedLocalizedWrites freePages baseWrites
  journal : GrowableStorage.Journal PhysicalCodec.pageSize
  requests : List (POSIXVFS.Request PhysicalCodec.pageSize)
  requestsEq : requests = preparedCommitPlan journal prepared.writes

theorem CommittedLocalizedDelta.trace_eq
    {freePages : List Nat}
    {baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (committed : CommittedLocalizedDelta freePages baseWrites) :
    committed.requests =
      preparedCommitPlan committed.journal committed.prepared.writes :=
  committed.requestsEq

/-- Once the concrete pre-image reads are identified with the modeled old
image, the exact request list returned by the live localized writer is the
proved rollback-journal commit plan.  The journal equality is precisely the
VFS read-refinement obligation; no table or codec fact is hidden in it. -/
theorem CommittedLocalizedDelta.trace_eq_commitPlan
    {freePages : List Nat}
    {baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (committed : CommittedLocalizedDelta freePages baseWrites)
    (oldImage : GrowableStorage.Image PhysicalCodec.pageSize)
    (journalExact : committed.journal =
      GrowableStorage.makeJournal oldImage committed.prepared.writes) :
    committed.requests =
      POSIXVFS.persistentCommitPlan oldImage committed.prepared.writes := by
  rw [committed.trace_eq, journalExact]
  exact preparedCommitPlan_eq_persistentCommitPlan oldImage
    committed.prepared.writes

/-- Commit an already proved page delta. Only the final pages selected by the
pure preparation are read for journal pre-images, written, and read back. No
whole-file encode, diff, or reopen occurs on this path. -/
def commitLocalizedCertified (syncOps : SyncOps) (paths : Paths)
    (expectedBefore baseWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (freePages : List Nat := []) :
    IO (Option (CommittedLocalizedDelta freePages baseWrites)) := do
  recoverInPlace syncOps paths
  let prepared ← prepareLocalizedWrites paths.main freePages baseWrites
  let writes := prepared.writes
  let journal ← journalFromFile paths.main writes
  -- `expectedBefore` is deliberately a safe superset: a structural operation
  -- includes absorbed pages even when only one of them becomes the freelist
  -- trunk.  Validate every page that will actually be overwritten against its
  -- proved preimage; do not require every supplied preimage to become a write.
  let oldWritesCovered := journal.undo.all fun record =>
    record.pageId = 0 ||
      expectedBefore.any (fun expected =>
        expected.pageId = record.pageId && expected.page = record.before)
  unless oldWritesCovered do return none
  let encodable ← match PhysicalJournalCodec.ofJournal? journal with
    | some value => pure value
    | none => throw (IO.userError "localized rollback journal exceeds encoded bounds")
  let persistent ← match PhysicalJournalCodec.ofEncodable? encodable with
    | some value => pure value
    | none => throw (IO.userError "localized rollback journal exceeds persistent bounds")
  activatePersistentJournal syncOps paths persistent
  writeMainPages paths.main writes
  syncOps.syncFile paths.main
  verifyWrittenPages paths.main writes
  retirePersistentJournal syncOps paths
  let requests := preparedCommitPlan journal writes
  return some { prepared, journal, requests, requestsEq := rfl }

/-- Compatibility projection for direct adapter tests. The live engine uses
`commitLocalizedCertified` so the proof-carrying final list cannot be erased
before its syscall trace is selected. -/
def commitLocalized (syncOps : SyncOps) (paths : Paths)
    (expectedBefore writes :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (freePages : List Nat := []) :
    IO (Option (List (POSIXVFS.Request PhysicalCodec.pageSize))) := do
  return (← commitLocalizedCertified syncOps paths expectedBefore writes
    freePages).map (fun committed => committed.requests)

/-- Commit a proved high-fanout bulk image and retain the exact topology that
was serialized.  The syscall protocol is identical to `commit`; only the
proof-owned post-state differs. -/
def commitWide (syncOps : SyncOps) (paths : Paths) (new : Core.Database) :
    IO (Option (ValidatedWideState new ×
      List (POSIXVFS.Request PhysicalCodec.pageSize))) := do
  recoverInPlace syncOps paths
  let current ← IO.FS.readBinFile paths.main
  let oldImage ← match physicalImage? current.data.toList with
    | some image => pure image
    | none => throw (IO.userError "could not page the current general MVP image")
  let some prepared := prepareWideBulkCommit? oldImage new | return none
  let writes := prepared.writes
  let journal := GrowableStorage.makeJournal oldImage writes
  let encodable ← match PhysicalJournalCodec.ofJournal? journal with
    | some value => pure value
    | none => throw (IO.userError "general MVP rollback journal exceeds encoded bounds")
  let persistent ← match PhysicalJournalCodec.ofEncodable? encodable with
    | some value => pure value
    | none => throw (IO.userError "general MVP rollback journal exceeds persistent bounds")
  activatePersistentJournal syncOps paths persistent
  writeMainPages paths.main writes
  syncOps.syncFile paths.main
  verifyWrittenPages paths.main writes
  retirePersistentJournal syncOps paths
  let retained := prepared.state.reserveThrough (prepared.image.pageCount + 1)
  have builtRepresents :=
    CoreWidePageCodec.encodeBulkInlineWithState_represents
      prepared.encodedWithState
  have retainedRepresents : retained.Represents new := by
    have reserved := prepared.state.reserveThrough_represents
      (prepared.image.pageCount + 1)
    rw [builtRepresents.1] at reserved
    exact reserved
  return some (⟨retained, retainedRepresents⟩,
    POSIXVFS.persistentCommitPlan oldImage writes)

def commit (syncOps : SyncOps) (paths : Paths) (new : Core.Database)
    (updatedMetadata : Option CoreMultiFreelist.HeaderMetadata := none) :
    IO (ValidatedOpenState × List (POSIXVFS.Request PhysicalCodec.pageSize)) := do
  recoverInPlace syncOps paths
  let current ← IO.FS.readBinFile paths.main
  let oldImage ← match physicalImage? current.data.toList with
    | some image => pure image
    | none => throw (IO.userError "could not page the current general MVP image")
  -- The pure preparation retains the exact encoder branch and write equation
  -- later consumed by `PreparedBulkCommit.postImageCertificate`; syscalls do
  -- not recompute or reinterpret either choice.
  let prepared ← match prepareBulkCommit? oldImage new updatedMetadata with
    | some result => pure result
    | none => throw (IO.userError
        "general MVP database or freelist exceeds the verified physical bounds")
  let newImage := prepared.newImage
  let writes := prepared.writes
  let journal := GrowableStorage.makeJournal oldImage writes
  let encodable ← match PhysicalJournalCodec.ofJournal? journal with
    | some value => pure value
    | none => throw (IO.userError "general MVP rollback journal exceeds encoded bounds")
  let persistent ← match PhysicalJournalCodec.ofEncodable? encodable with
    | some value => pure value
    | none => throw (IO.userError "general MVP rollback journal exceeds persistent bounds")
  activatePersistentJournal syncOps paths persistent
  writeMainPages paths.main writes
  syncOps.syncFile paths.main
  verifyWrittenPages paths.main writes
  retirePersistentJournal syncOps paths
  let validated ← match retainGeneratedState? prepared.state
      newImage.pageCount prepared.freePages with
    | some value => pure value
    | none => throw (IO.userError
        "generated commit did not retain a proof-carrying state")
  return (validated, POSIXVFS.persistentCommitPlan oldImage writes)

/-- The new catalog route retains its component checks and exact journal plan;
it does not attach a canonical-image certificate to noncanonical declarations. -/
structure CommittedCatalog (database : Core.Database) where
  old : GrowableStorage.Image PhysicalCodec.pageSize
  checked : CoreCatalogImage.Checked old database
  requests : List (POSIXVFS.Request PhysicalCodec.pageSize)
  requestsEq : requests = POSIXVFS.persistentCommitPlan old checked.writes

def commitCatalog (syncOps : SyncOps) (paths : Paths) (database : Core.Database)
    (metadata : CoreMultiFreelist.HeaderMetadata) (declarations : List CoreDecode.CatalogEntry)
    (objects : Option CoreCatalogData.Objects := none) :
    IO (CommittedCatalog database) := do
  recoverInPlace syncOps paths
  let bytes ← IO.FS.readBinFile paths.main
  let some old := physicalImage? bytes.data.toList | throw (IO.userError "invalid catalog write geometry")
  let header ← readHeader paths.main
  unless header.headerPrefix.pageSize == PhysicalCodec.pageSize && header.headerPrefix.reservedSpace == 0 do
    throw (IO.userError "unsupported catalog write geometry")
  let source := CorePageSource.ofStorageImage old
  let ioSource : CoreDecode.IOPageSource := {
    pageCount := source.pageCount
    readPage := fun page => pure (source.readPage page) }
  let some catalog ← if old.pageCount == 0 then pure (some []) else CoreDecode.catalogIOFrom ioSource
    | throw (IO.userError "invalid current catalog")
  let some image := CoreCatalogImage.encode old.pageCount database header metadata catalog declarations objects
    | throw (IO.userError "cannot encode retained index catalog")
  let some checked := CoreCatalogImage.check old database image
    | throw (IO.userError "retained catalog image failed component validation")
  let checked ← match objects with
    | none => pure checked
    | some objects =>
        match CoreCatalogImage.attachObjects checked objects with
        | none => throw (IO.userError "schema object image failed catalog identity validation")
        | some checked => pure checked
  let journal := GrowableStorage.makeJournal old checked.writes
  let some encodable := PhysicalJournalCodec.ofJournal? journal
    | throw (IO.userError "catalog rollback journal exceeds encoded bounds")
  let some persistent := PhysicalJournalCodec.ofEncodable? encodable
    | throw (IO.userError "catalog rollback journal exceeds persistent bounds")
  activatePersistentJournal syncOps paths persistent
  writeMainPages paths.main checked.writes
  syncOps.syncFile paths.main
  verifyWrittenPages paths.main checked.writes
  retirePersistentJournal syncOps paths
  return { old, checked, requests := POSIXVFS.persistentCommitPlan old checked.writes, requestsEq := rfl }

theorem CommittedCatalog.trace_eq {database} (committed : CommittedCatalog database) :
    committed.requests = POSIXVFS.persistentCommitPlan committed.old committed.checked.writes :=
  committed.requestsEq

end CoreFileAdapter

end SQLeanite
