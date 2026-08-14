import SQLeanite.CoreDecode
import SQLeanite.CoreFreelist
import SQLeanite.CoreMultiFreelist
import SQLeanite.CoreOverflow
import SQLeanite.CoreChunkPageDelta
import SQLeanite.CorePageLoad
import SQLeanite.PhysicalFileAdapter

namespace SQLeanite
namespace CoreFileAdapter

abbrev Paths := PhysicalFileAdapter.Paths
abbrev SyncOps := PhysicalFileAdapter.SyncOps
abbrev Request := GrowableStorage.VFSRequest PhysicalCodec.pageSize

def storageImage (image : CoreFile.Image) :
    GrowableStorage.Image PhysicalCodec.pageSize := {
  pageCount := image.pages.length
  read := fun pageId =>
    (image.pages[pageId]?).map CoreFile.Page.storage |>.getD
      (Storage.Page.zero PhysicalCodec.pageSize) }

def transactionWrites (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (image : CoreFile.Image) :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize) :=
  GrowableStorage.deltaWrites old (storageImage image)

def commitPlan (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (new : CoreFile.Image) : List Request :=
  let writes := transactionWrites old new
  [.writeJournal (some (GrowableStorage.makeJournal old writes)),
    .syncJournal] ++ writes.map GrowableStorage.VFSRequest.writeMain ++
      [.syncMain, .writeJournal none, .syncJournal]

theorem run_commitPlan (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (new : CoreFile.Image) :
    PhysicalFileAdapter.runPlan (GrowableStorage.JournaledState.initial old)
      (commitPlan old new) =
    GrowableStorage.rollbackCommitState old (transactionWrites old new) .committed := by
  unfold commitPlan
  simp only [List.cons_append, List.nil_append, PhysicalFileAdapter.runPlan,
    PhysicalFileAdapter.modelStep]
  rw [PhysicalFileAdapter.runPlan_writeMain_append]
  simp [PhysicalFileAdapter.runPlan, PhysicalFileAdapter.modelStep,
    GrowableStorage.rollbackCommitState,
    GrowableStorage.JournaledState.initial,
    GrowableStorage.JournaledState.writeJournal,
    GrowableStorage.JournaledState.syncJournal,
    GrowableStorage.JournaledState.stageMainWrites,
    GrowableStorage.JournaledState.syncMain,
    GrowableStorage.JournaledState.deleteJournal,
    GrowableStorage.Cache.writeAll, GrowableStorage.Cache.write]

theorem commit_crash_atomic (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (new : CoreFile.Image)
    (doesNotShrink : old.pageCount ≤ (storageImage new).pageCount)
    (phase : GrowableStorage.CommitPhase)
    (recoveredMain : GrowableStorage.Image PhysicalCodec.pageSize)
    (recoveredJournal : Option (GrowableStorage.Journal PhysicalCodec.pageSize))
    (outcome : GrowableStorage.JournaledCrashOutcome
      (GrowableStorage.rollbackCommitState old (transactionWrites old new) phase)
      recoveredMain recoveredJournal) :
    (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal).Equiv old ∨
      (GrowableStorage.recoverWithJournal recoveredMain recoveredJournal).Equiv
        (storageImage new) := by
  rcases GrowableStorage.rollbackCommit_crash_atomic old (transactionWrites old new)
      phase recoveredMain recoveredJournal outcome with oldState | writtenState
  · exact .inl oldState
  · exact .inr (writtenState.trans
      (GrowableStorage.apply_deltaWrites_equiv old (storageImage new) doesNotShrink))

private def bytes (values : List UInt8) : ByteArray :=
  ByteArray.mk values.toArray

def physicalImage? (input : List UInt8) :
    Option (GrowableStorage.Image PhysicalCodec.pageSize) := do
  let (header, _) ← FileFormat.decodeDatabaseHeader input
  if _pageSize : header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize then
    let count := header.databaseSizePages.val
    let (decoded, suffix) ← DiskFormat.decodeSizedPages PhysicalCodec.pageSize count input
    if _consumed : suffix = [] then
      some {
        pageCount := count
        read := fun pageId => decoded.pages[pageId]?.getD
          (Storage.Page.zero PhysicalCodec.pageSize) }
    else none
  else none

/-- Read exactly one SQLite page. Regular-file short reads are rejected rather
than silently zero-filled. -/
private def readPageBytesOf (handle : IO.FS.Handle) (pageSize : Nat) :
    IO (Option (List UInt8)) := do
  let chunk ← handle.read (USize.ofNat pageSize)
  if chunk.size = pageSize then
    return some chunk.toList
  else return none

private def readPageBytes (handle : IO.FS.Handle) : IO (Option (List UInt8)) :=
  readPageBytesOf handle PhysicalCodec.pageSize

private def skipPagesOf (handle : IO.FS.Handle) (pageSize : Nat) : Nat → IO Bool
  | 0 => pure true
  | count + 1 => do
      let some _ ← readPageBytesOf handle pageSize | return false
      skipPagesOf handle pageSize count

private def skipPages (handle : IO.FS.Handle) : Nat → IO Bool :=
  skipPagesOf handle PhysicalCodec.pageSize

/-- Publish exactly the pages represented by the verified transaction. The C
boundary performs only positional writes; ordering and page bytes stay Lean. -/
private def writeMainPages (path : System.FilePath)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : IO Unit := do
  for write in writes do
    SyscallVFS.pwriteBytes path.toString
      (UInt64.ofNat (write.pageId * PhysicalCodec.pageSize))
      (ByteArray.mk write.page.bytes)

/-- The syscall trace used when page pre-images have already been read from
the concrete file.  It is the same rollback protocol as `POSIXVFS.commitPlan`;
the separate argument makes the concrete read boundary explicit. -/
def preparedCommitPlan
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    List (POSIXVFS.Request PhysicalCodec.pageSize) :=
  [.writeJournalTemp journal, .fdatasyncJournalTemp, .renameJournal,
    .fsyncDirectory] ++ writes.map POSIXVFS.Request.pwriteMain ++
    [.fdatasyncMain, .unlinkJournal, .fsyncDirectory]

theorem preparedCommitPlan_eq_commitPlan
    (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    preparedCommitPlan (GrowableStorage.makeJournal old writes) writes =
      POSIXVFS.commitPlan old writes := rfl

private def readPageCount (handle : IO.FS.Handle)
    (path : System.FilePath) : IO Nat := do
  handle.rewind
  let some firstPage ← readPageBytes handle |
    throw (IO.userError s!"invalid general MVP SQLite image: {path}")
  let (header, _) ← match FileFormat.decodeDatabaseHeader firstPage with
    | some decoded => pure decoded
    | none => throw (IO.userError s!"invalid general MVP SQLite image: {path}")
  let count := header.databaseSizePages.val
  let metadata ← path.metadata
  unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
      metadata.byteSize.toNat = count * PhysicalCodec.pageSize do
    throw (IO.userError s!"invalid general MVP SQLite image: {path}")
  return count

private def targetPageCount (current : Nat)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : Nat :=
  writes.foldl (fun count write => max count (write.pageId + 1)) current

/-- Add a write only when its intended bytes differ from the current page.
This keeps an unchanged freelist trunk out of later transactions. -/
private def prependChangedWrite (path : System.FilePath)
    (write : GrowableStorage.PageWrite PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    IO (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) := do
  let current ← SyscallVFS.preadBytes path.toString
    (UInt64.ofNat (write.pageId * PhysicalCodec.pageSize))
    (USize.ofNat PhysicalCodec.pageSize)
  if current.size = PhysicalCodec.pageSize &&
      current.toList == write.page.bytes.toList then
    return writes
  else return write :: writes

/-- Growth and page release both mutate SQLite page zero.  Released page
numbers are encoded as one ordinary SQLite freelist trunk plus leaf pointers;
the catalog body and every active root remain byte-for-byte stable. -/
private def addHeaderAndFreelistWrites (path : System.FilePath)
    (freePages : List Nat)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    IO (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) := do
  IO.FS.withFile path .read fun handle => do
    let current ← readPageCount handle path
    let target := targetPageCount current writes
    if bounds : target < 2 ^ 32 ∧ freePages.length < 2 ^ 32 ∧
        freePages.Nodup ∧
        ∀ page ∈ freePages, 1 < page ∧ page ≤ target ∧ page < 2 ^ 32 then
      let first ← SyscallVFS.preadBytes path.toString 0
        (USize.ofNat PhysicalCodec.pageSize)
      unless first.size = PhysicalCodec.pageSize do
        throw (IO.userError "short read while updating the SQLite header")
      let (header, suffix) ← match FileFormat.decodeDatabaseHeader first.toList with
        | some decoded => pure decoded
        | none => throw (IO.userError "invalid SQLite header during page delta")
      let count : FileFormat.U32Value := ⟨target, bounds.1⟩
      let freeCount : FileFormat.U32Value := ⟨freePages.length, bounds.2.1⟩
      let firstFree : FileFormat.U32Value := match firstResult : freePages with
        | [] => ⟨0, by omega⟩
        | page :: _ => ⟨page, (bounds.2.2.2 page (by simp [firstResult])).2.2⟩
      let updatedHeader : FileFormat.DatabaseHeader := {
        headerPrefix := header.headerPrefix
        databaseSizePages := count
        firstFreelistTrunk := firstFree
        freelistPageCount := freeCount
        schemaCookie := header.schemaCookie
        schemaFormat := header.schemaFormat
        defaultPageCacheSize := header.defaultPageCacheSize
        largestRootBTreePage := header.largestRootBTreePage
        textEncoding := header.textEncoding
        userVersion := header.userVersion
        incrementalVacuum := header.incrementalVacuum
        applicationId := header.applicationId
        versionValidFor := header.versionValidFor
        sqliteVersion := header.sqliteVersion }
      let patched := FileFormat.encodeDatabaseHeader updatedHeader ++ suffix
      let headerPage ← match DiskFormat.decodeStoragePage
          PhysicalCodec.pageSize patched with
        | some (page, []) => pure page
        | _ => throw (IO.userError "updated SQLite header changed page size")
      let writes ← match freePages with
        | [] => pure writes
        | trunk :: leaves => do
            let trunkPrefix := FileFormat.encodeUnsignedFixed 4 0 ++
              FileFormat.encodeUnsignedFixed 4 leaves.length ++
                CoreFreelist.encodePageNumbers leaves
            if fits : trunkPrefix.length ≤ PhysicalCodec.pageSize then
              let trunkBytes := trunkPrefix ++
                List.replicate (PhysicalCodec.pageSize - trunkPrefix.length) 0
              let trunkPage ← match DiskFormat.decodeStoragePage
                  PhysicalCodec.pageSize trunkBytes with
                | some (page, []) => pure page
                | _ => throw (IO.userError "freelist trunk changed page size")
              prependChangedWrite path ⟨trunk - 1, trunkPage⟩ writes
            else
              throw (IO.userError "localized freelist exceeds one trunk page")
      if writes.any (fun write => write.pageId = 0) then
        pure writes
      else prependChangedWrite path ⟨0, headerPage⟩ writes
    else
      throw (IO.userError
        "localized allocation or freelist exceeds SQLite bounds")

private def journalFromFile (path : System.FilePath)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    IO (GrowableStorage.Journal PhysicalCodec.pageSize) :=
  IO.FS.withFile path .read fun handle => do
    let count ← readPageCount handle path
    let mut undo := []
    for write in writes do
      if write.pageId < count then
        let bytes ← SyscallVFS.preadBytes path.toString
          (UInt64.ofNat (write.pageId * PhysicalCodec.pageSize))
          (USize.ofNat PhysicalCodec.pageSize)
        unless bytes.size = PhysicalCodec.pageSize do
          throw (IO.userError s!"short read for main page {write.pageId}")
        let before ← match DiskFormat.decodeStoragePage
            PhysicalCodec.pageSize bytes.toList with
          | some (page, []) => pure page
          | _ => throw (IO.userError s!"could not decode main page {write.pageId}")
        undo := undo ++ [⟨write.pageId, before⟩]
    return ⟨count, undo⟩

private def verifyWrittenPages (path : System.FilePath)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : IO Unit := do
    for write in writes do
      let bytes ← SyscallVFS.preadBytes path.toString
        (UInt64.ofNat (write.pageId * PhysicalCodec.pageSize))
        (USize.ofNat PhysicalCodec.pageSize)
      unless bytes.size = PhysicalCodec.pageSize do
        throw (IO.userError s!"short read for main page {write.pageId}")
      let actual ← match DiskFormat.decodeStoragePage
          PhysicalCodec.pageSize bytes.toList with
        | some (page, []) => pure page
        | _ => throw (IO.userError s!"could not decode main page {write.pageId}")
      unless actual == write.page do
        throw (IO.userError s!"dirty-page read-back mismatch at {write.pageId}")

/-- A bounded, file-backed page source. It remembers only the current page
position. Forward traversal discards skipped pages instead of materializing the
file; a backward request rewinds and scans to its target. -/
private def filePageSourceFor (handle : IO.FS.Handle)
    (usable : FileFormat.UsablePageSize) (pageCount : Nat)
    (position : IO.Ref Nat) : CoreDecode.IOPageSource := {
  usable
  pageCount
  readPage := fun pageNumber => do
    if pageNumber = 0 ∨ pageCount < pageNumber then return none
    let target := pageNumber - 1
    let current ← position.get
    let current ← if target < current then
      handle.rewind
      position.set 0
      pure 0
    else pure current
    unless ← skipPagesOf handle usable.val (target - current) do return none
    position.set target
    let page ← readPageBytesOf handle usable.val
    if page.isSome then position.set pageNumber
    return page }

private def filePageSource (handle : IO.FS.Handle) (pageCount : Nat)
    (position : IO.Ref Nat) : CoreDecode.IOPageSource :=
  filePageSourceFor handle PhysicalCodec.usablePageSize pageCount position

/-- Random-access source for routed reads. Database page numbers are one-based;
`pread` leaves no shared cursor and avoids reading every earlier page merely to
reach an index root allocated after a large table. -/
private def preadPageSource (path : System.FilePath)
    (pageCount : Nat) : CoreDecode.IOPageSource := {
  pageCount
  readPage := fun pageNumber => do
    if pageNumber = 0 ∨ pageCount < pageNumber then return none
    let bytes ← SyscallVFS.preadBytes path.toString
      (UInt64.ofNat ((pageNumber - 1) * PhysicalCodec.pageSize))
      (USize.ofNat PhysicalCodec.pageSize)
    if bytes.size = PhysicalCodec.pageSize then return some bytes.toList
    else return none }

/-- Turn the semantic SQLite page size in a validated zero-reserved-byte
header into the proof-carrying geometry consumed by the general decoder. -/
def headerUsablePageSize? (header : FileFormat.DatabaseHeader) :
    Option FileFormat.UsablePageSize := do
  let pageSize := header.headerPrefix.pageSize
  if valid : FileFormat.ValidSQLitePageSize pageSize then
    if _unreserved : header.headerPrefix.reservedSpace = 0 then
      some {
        val := pageSize
        atLeastMinimum := by
          simp [FileFormat.ValidSQLitePageSize] at valid
          omega
        atMostMaximum := by
          simp [FileFormat.ValidSQLitePageSize] at valid
          omega }
    else none
  else none

theorem headerUsablePageSize?_val {header : FileFormat.DatabaseHeader}
    {usable : FileFormat.UsablePageSize}
    (decoded : headerUsablePageSize? header = some usable) :
    usable.val = header.headerPrefix.pageSize := by
  unfold headerUsablePageSize? at decoded
  dsimp only at decoded
  split at decoded
  next =>
    split at decoded
    next =>
      have equal := Option.some.inj decoded
      exact (congrArg FileFormat.UsablePageSize.val equal).symm
    next => contradiction
  next => contradiction

def generatedImageStamp (paths : Paths) : IO Bool := do
  let bytes ← SyscallVFS.preadBytes paths.main.toString 0 100
  if bytes.size = 100 then
    match FileFormat.decodeDatabaseHeader bytes.toList with
    | some (header, _) => return CoreFile.hasGeneratedImageStamp header
    | none => return false
  else return false

def reopen (paths : Paths) : IO Core.Database := do
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let headerBytes ← handle.read 100
    unless headerBytes.size = 100 do
      throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")
    let (header, _) ← match FileFormat.decodeDatabaseHeader headerBytes.toList with
      | some decoded => pure decoded
      | none => throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")
    let usable ← match headerUsablePageSize? header with
      | some usable => pure usable
      | none => throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")
    let count := header.databaseSizePages.val
    unless header.textEncoding.val = 1 &&
        metadata.byteSize.toNat = count * usable.val do
      throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")
    handle.rewind
    let position ← IO.mkRef 0
    let source := filePageSourceFor handle usable count position
    match ← CoreDecode.decodeFromIOPageSource source with
    | some database => return database
    | none => throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")

/-- Recover the proof-carrying 2-3-tree view only when the bytes actually have
that shape and its abstraction is exactly the already-decoded database. -/
def loadPageState (paths : Paths) (database : Core.Database) :
    IO (Option CoreChunkPageState.State) := do
  let input ← IO.FS.readBinFile paths.main
  let bytes := input.data.toList
  let some (header, _) := FileFormat.decodeDatabaseHeader bytes |
    return none
  let count := header.databaseSizePages.val
  unless input.size = count * PhysicalCodec.pageSize do return none
  let pages := CoreDecode.pages count bytes
  return CorePageLoad.load? (.ofList pages) database

structure ValidatedOpenState where
  state : CoreChunkPageState.State
  /-- The constructor is private to this module: this capability is produced
  only after `CorePageLoad.open?` has validated every table and index tree. -/
  private validated : Unit

/-- Raise the high-water mark of the persistent state serialized by the bulk
encoder to include its index and freelist tail. -/
def retainGeneratedState? (built : CoreChunkPageState.State) (pageCount : Nat)
    (freePages : List Nat) : Option ValidatedOpenState := do
  let state : CoreChunkPageState.State := {
    built with
    nextPage := pageCount + 1
    freePages }
  if _allocation : state.AllocationWellFormed then
    some ⟨state, ()⟩
  else none

/-- Recover the proof-carrying table topology directly from the logical input
to the proved bulk encoder.  The caller separately verifies every changed page
against that encoder's bytes before publishing this capability; unchanged
pages were byte-equal in the pre-commit image by construction of the delta.
This avoids decoding every newly written row and index a second time. -/
def generatedOpenState? (database : Core.Database) (pageCount : Nat)
    (freePages : List Nat) : Option ValidatedOpenState := do
  let built ← CoreChunkPageState.State.build? database
  retainGeneratedState? built pageCount freePages

theorem retainGeneratedState?_state
    {built : CoreChunkPageState.State} {pageCount : Nat}
    {freePages : List Nat} {validated : ValidatedOpenState}
    (retained : retainGeneratedState? built pageCount freePages =
      some validated) :
    validated.state.database = built.database := by
  unfold retainGeneratedState? at retained
  dsimp only at retained
  split at retained
  next =>
    injection retained with equal
    exact congrArg (fun value : ValidatedOpenState => value.state.database)
      equal.symm
  next => contradiction

theorem retainGeneratedState?_allocationWellFormed
    {built : CoreChunkPageState.State} {pageCount : Nat}
    {freePages : List Nat} {validated : ValidatedOpenState}
    (retained : retainGeneratedState? built pageCount freePages =
      some validated) :
    validated.state.AllocationWellFormed := by
  unfold retainGeneratedState? at retained
  dsimp only at retained
  split at retained
  next allocation =>
    injection retained with equal
    subst validated
    exact allocation
  next => contradiction

theorem generatedOpenState?_database
    {database : Core.Database} {pageCount : Nat} {freePages : List Nat}
    {validated : ValidatedOpenState}
    (generated : generatedOpenState? database pageCount freePages =
      some validated) :
    validated.state.database = database := by
  unfold generatedOpenState? at generated
  rcases Option.bind_eq_some.mp generated with ⟨built, builtResult, generated⟩
  exact (retainGeneratedState?_state generated).trans
    (CoreChunkPageState.State.build?_represents builtResult).1

theorem generatedOpenState?_allocationWellFormed
    {database : Core.Database} {pageCount : Nat} {freePages : List Nat}
    {validated : ValidatedOpenState}
    (generated : generatedOpenState? database pageCount freePages =
      some validated) :
    validated.state.AllocationWellFormed := by
  unfold generatedOpenState? at generated
  rcases Option.bind_eq_some.mp generated with ⟨built, builtResult, generated⟩
  exact retainGeneratedState?_allocationWellFormed generated

/-- Preserve the validating-open capability across a proved table-only delta.
The physical secondary indexes remain valid precisely because the delta's
linear source image is unchanged; the database equivalence check prevents a
capability from being attached to an unrelated connection state. -/
def ValidatedOpenState.retarget? (validated : ValidatedOpenState)
    (delta : CoreChunkPageDelta.StateDelta)
    (_sufficient : delta.table.tablePagesSufficient = true) :
    Option ValidatedOpenState :=
  if _same : validated.state.database.Equiv delta.before.database then
    some ⟨delta.after, ()⟩
  else none

theorem ValidatedOpenState.retarget?_state
    {validated next : ValidatedOpenState}
    {delta : CoreChunkPageDelta.StateDelta}
    {sufficient : delta.table.tablePagesSufficient = true}
    (retargeted : validated.retarget? delta sufficient = some next) :
    next.state = delta.after := by
  unfold ValidatedOpenState.retarget? at retargeted
  split at retargeted
  next =>
    injection retargeted with equal
    exact congrArg ValidatedOpenState.state equal.symm
  next => contradiction

theorem ValidatedOpenState.retarget?_indexImage
    {validated next : ValidatedOpenState}
    {delta : CoreChunkPageDelta.StateDelta}
    {sufficient : delta.table.tablePagesSufficient = true}
    (_retargeted : validated.retarget? delta sufficient = some next) :
    CoreChunkPageDelta.indexImage delta.table.before.table =
      CoreChunkPageDelta.indexImage delta.table.after.table :=
  delta.table.tablePagesSufficient_indexImage sufficient

/-- Read a supported physical image once and recover its logical database and
persistent page identities together.  The returned capability records that
the index images were validated by this same open. Returning `none` is an
optimization miss: callers retain the general compatibility path. -/
def loadOpenState (paths : Paths) :
    IO (Option ValidatedOpenState) := do
  let input ← IO.FS.readBinFile paths.main
  let bytes := input.data.toList
  let some (header, _) := FileFormat.decodeDatabaseHeader bytes |
    return none
  let count := header.databaseSizePages.val
  unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
      header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
      input.size = count * PhysicalCodec.pageSize do return none
  let pages := CoreDecode.pages count bytes
  let source := CoreDecode.PageSource.ofList pages
  let opened := match CorePageLoad.openGenerated? source with
    | some state => some state
    | none => CorePageLoad.open? source
  return opened.map fun state => ⟨state, ()⟩

structure CertifiedIndexEncoding (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) where
  value : CoreOverflow.IndexEncoding
  encoded : CoreOverflow.encodeIndex rootPage table index = some value

def certifyIndexEncoding? (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) :
    Option (CertifiedIndexEncoding rootPage table index) :=
  match encoded : CoreOverflow.encodeIndex rootPage table index with
  | none => none
  | some value => some ⟨value, encoded⟩

theorem certifyIndexEncoding?_exact {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {certified : CertifiedIndexEncoding rootPage table index}
    (success : certifyIndexEncoding? rootPage table index = some certified) :
    CoreOverflow.encodeIndex rootPage table index = some certified.value := by
  unfold certifyIndexEncoding? at success
  split at success
  next => contradiction
  next value encoded =>
    injection success with equal
    subst certified
    exact encoded

/-- A physical, page-directed index image is accepted only with an exact
decoder witness for the logical post-state. This is deliberately stronger
than a byte-count or successful-mutation flag. -/
structure DecodedIndexCertificate (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) where
  source : CoreDecode.PageSource
  exact : CoreDecode.decodeIndexSubtreeFrom source (source.pageCount + 1)
      rootPage = some (CoreDecode.expectedIndexEntries table index)

def certifyDecodedIndex? (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) (source : CoreDecode.PageSource) :
    Option (DecodedIndexCertificate rootPage table index) :=
  match decoded : CoreDecode.decodeIndexSubtreeFrom source
      (source.pageCount + 1) rootPage with
  | none => none
  | some entries =>
      if same : entries = CoreDecode.expectedIndexEntries table index then
        some ⟨source, by simpa [same] using decoded⟩
      else none

theorem certifyDecodedIndex?_source {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {source : CoreDecode.PageSource}
    {certified : DecodedIndexCertificate rootPage table index}
    (success : certifyDecodedIndex? rootPage table index source =
      some certified) :
    certified.source = source := by
  unfold certifyDecodedIndex? at success
  split at success
  next => contradiction
  next entries decoded =>
    split at success
    next =>
      injection success with equal
      exact congrArg DecodedIndexCertificate.source equal.symm
    next => contradiction

theorem certifyDecodedIndex?_exact {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {source : CoreDecode.PageSource}
    {certified : DecodedIndexCertificate rootPage table index}
    (success : certifyDecodedIndex? rootPage table index source =
      some certified) :
    CoreDecode.decodeIndexSubtreeFrom source (source.pageCount + 1) rootPage =
      some (CoreDecode.expectedIndexEntries table index) := by
  rw [← certifyDecodedIndex?_source success]
  exact certified.exact

inductive LocalizedIndexCertificate (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) where
  | encoded (certificate : CertifiedIndexEncoding rootPage table index)
  | decoded (certificate : DecodedIndexCertificate rootPage table index)

structure LocalizedLastIndexDelta
    (delta : CoreChunkPageDelta.StateDelta) where
  state : CoreChunkPageState.State
  index : Core.Index
  rootPage : Nat
  certificate : LocalizedIndexCertificate rootPage
    delta.table.after.table index
  expectedBefore : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  writesDistinct : writes.Pairwise (fun left right => left.pageId ≠ right.pageId)
  allocation : state.AllocationWellFormed
  validated : ValidatedOpenState

private def storagePage? (bytes : List UInt8) :
    Option (Storage.Page PhysicalCodec.pageSize) :=
  if exact : bytes.length = PhysicalCodec.pageSize then
    some {
      bytes := bytes.toArray
      sizeInvariant := by simp [exact] }
  else none

private def indexPageWrites (rootPage : Nat) :
    List CoreFile.Page →
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  | [] => []
  | page :: pages =>
      ⟨rootPage - 1, page.storage⟩ :: indexPageWrites (rootPage + 1) pages

theorem indexPageWrites_length (rootPage : Nat) (pages : List CoreFile.Page) :
    (indexPageWrites rootPage pages).length = pages.length := by
  induction pages generalizing rootPage with
  | nil => rfl
  | cons page pages induction =>
      simp only [indexPageWrites, List.length_cons, induction]

/-- Drop a proposed write only when the validated old tail already contains
the exact same page ID and bytes.  This scopes both journal pre-images and main
writes to the physical index delta instead of the complete rebuilt image. -/
def changedPageWrites
    (before writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize) :=
  writes.filter fun write =>
    !before.any fun old => old.pageId == write.pageId && old.page == write.page

theorem changedPageWrites_sublist (before writes :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    (changedPageWrites before writes).Sublist writes := by
  exact List.filter_sublist

theorem omitted_changedPageWrites_matches
    {before writes :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    {write : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (member : write ∈ writes)
    (omitted : write ∉ changedPageWrites before writes) :
    ∃ old ∈ before, old.pageId = write.pageId ∧ old.page = write.page := by
  unfold changedPageWrites at omitted
  simp only [List.mem_filter, member, true_and, Bool.not_eq_true] at omitted
  have anyTrue : before.any (fun old =>
      old.pageId == write.pageId && old.page == write.page) = true := by
    simpa using omitted
  simp only [List.any_eq_true] at anyTrue
  rcases anyTrue with ⟨old, oldMember, matched⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at matched
  exact ⟨old, oldMember, matched⟩

/-! ## Page-directed generated-index deletion -/

def indexEntryCell? (entry : CoreDecode.IndexEntry) : Option (List UInt8) := do
  let record ← CoreFile.physicalRecord? [
    entry.value.recordField,
    (PhysicalCodec.Value.integer entry.rowid).recordField]
  if bounded : record.encode.length < 2 ^ 64 then
    let size : FileFormat.U64Value :=
      ⟨record.encode.length, by simpa using bounded⟩
    some (FileFormat.encodeVarint size ++ record.encode)
  else none

def indexInteriorPageFromEntries? (entries : List (Nat × CoreDecode.IndexEntry))
    (rightmost : Nat) : Option CoreFile.Page := do
  let children ← entries.mapM fun entry => do
    let cell ← indexEntryCell? entry.2
    some (entry.1, cell)
  RecursivePageBTree.indexInteriorPage? children rightmost

def byteArrayPageSource (input : ByteArray) (pageCount : Nat) :
    CoreDecode.PageSource := {
  pageCount
  readPage := fun pageNumber =>
    if pageNumber = 0 || pageCount < pageNumber then none
    else
      let start := (pageNumber - 1) * PhysicalCodec.pageSize
      let stop := start + PhysicalCodec.pageSize
      if stop ≤ input.size then some (input.extract start stop).toList
      else none }

structure IndexPageMutations where
  source : CoreDecode.PageSource
  changed : List (Nat × List UInt8) := []

def replaceChangedPage (pageNumber : Nat) (bytes : List UInt8) :
    List (Nat × List UInt8) → List (Nat × List UInt8)
  | [] => [(pageNumber, bytes)]
  | changed :: changes =>
      if changed.1 = pageNumber then (pageNumber, bytes) :: changes
      else changed :: replaceChangedPage pageNumber bytes changes

def IndexPageMutations.readPage? (state : IndexPageMutations)
    (pageNumber : Nat) : Option (List UInt8) :=
  match state.changed.find? (fun changed => changed.1 == pageNumber) with
  | some changed => some changed.2
  | none => state.source.readPage pageNumber

def IndexPageMutations.pageSource (state : IndexPageMutations) :
    CoreDecode.PageSource := {
  pageCount := state.source.pageCount
  readPage := state.readPage? }

def IndexPageMutations.writePage? (state : IndexPageMutations)
    (pageNumber : Nat) (page : CoreFile.Page) : Option IndexPageMutations := do
  if _valid : 0 < pageNumber ∧ pageNumber ≤ state.source.pageCount then
    some { state with
      changed := replaceChangedPage pageNumber page.bytes state.changed }
  else none

def splitInlineIndexCells : Nat → List UInt8 →
    Option (List (List UInt8) × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (payloadSize, afterSize) ← FileFormat.decodeVarint input
      if _inline : payloadSize.val ≤
          FileFormat.indexMaxLocal PhysicalCodec.usablePageSize then
        let prefixLength := input.length - afterSize.length
        let cellLength := prefixLength + payloadSize.val
        if _bounded : cellLength ≤ input.length then
          let cell := input.take cellLength
          let rest := input.drop cellLength
          let tail ← splitInlineIndexCells count rest
          some (cell :: tail.1, tail.2)
        else none
      else none

def inlineIndexLeafCells? (page : List UInt8) :
    Option (List (List UInt8)) := do
  if _canonical : CoreDecode.canonicalIndexLeafPointersBeginAtContent page then
    let (count, content) ← CoreDecode.canonicalIndexLeafContent? page
    let (cells, suffix) ← splitInlineIndexCells count content
    if suffix.isEmpty then some cells else none
  else none

def popGreatestIndexEntry? : Nat → Nat → IndexPageMutations →
    Option (CoreDecode.IndexEntry × IndexPageMutations)
  | 0, _, _ => none
  | fuel + 1, pageNumber, state => do
      let page ← state.readPage? pageNumber
      let source := state.pageSource
      match CoreDecode.decodeIndexInteriorFrom source page with
      | some (_, rightmost) =>
          popGreatestIndexEntry? fuel rightmost state
      | none => do
          let cells ← inlineIndexLeafCells? page
          let greatestCell ← cells.getLast?
          let (greatest, suffix) ←
            CoreDecode.decodeIndexCellWithSuffix greatestCell
          if _consumed : suffix = [] then
            let replacement ← CoreFile.indexLeafPage? cells.dropLast
            let updated ← state.writePage? pageNumber replacement
            some (greatest, updated)
          else none

def indexEntryAfter (left right : CoreDecode.IndexEntry) : Bool :=
  left ≠ right && !CoreChunkPageDelta.indexEntryLess left right

/-- Remove an ordered target subsequence from ordered inline leaf cells in one
linear pass. Unlike repeated byte-list membership, every cell is decoded and
compared at most once. -/
def deleteSortedIndexCells? : List (List UInt8) →
    List CoreDecode.IndexEntry → Option (List (List UInt8))
  | cells, [] => some cells
  | [], _ :: _ => none
  | cell :: cells, target :: targets => do
      let (entry, suffix) ← CoreDecode.decodeIndexCellWithSuffix cell
      if _consumed : suffix = [] then
        if entry = target then deleteSortedIndexCells? cells targets
        else if CoreChunkPageDelta.indexEntryLess entry target then
          (deleteSortedIndexCells? cells (target :: targets)).map (cell :: ·)
        else none
      else none

/-- Insert one exact encoded entry into an ordered inline leaf.  Equality is a
duplicate `(value,rowid)` and is rejected; page construction below remains the
single authority for whether the enlarged leaf still fits. -/
def insertSortedIndexCell? (target : CoreDecode.IndexEntry)
    (targetCell : List UInt8) : List (List UInt8) →
      Option (List (List UInt8))
  | [] => some [targetCell]
  | cell :: cells => do
      let (entry, suffix) ← CoreDecode.decodeIndexCellWithSuffix cell
      if _consumed : suffix = [] then
        if target = entry then none
        else if CoreChunkPageDelta.indexEntryLess target entry then
          some (targetCell :: cell :: cells)
        else
          (insertSortedIndexCell? target targetCell cells).map (cell :: ·)
      else none

/-- Descend by the promoted entries stored in an SQLite index interior page.
The interior page is unchanged: this fast path succeeds only when the target
leaf absorbs the new cell without a split. -/
def insertIndexEntryNoSplit? : Nat → Nat → CoreDecode.IndexEntry →
    List UInt8 → IndexPageMutations → Option IndexPageMutations
  | 0, _, _, _, _ => none
  | fuel + 1, pageNumber, target, targetCell, state => do
      let page ← state.readPage? pageNumber
      let source := state.pageSource
      match CoreDecode.decodeIndexInteriorFrom source page with
      | some (entries, rightmost) =>
          let rec descend : List (Nat × CoreDecode.IndexEntry) →
              Option IndexPageMutations
            | [] => insertIndexEntryNoSplit? fuel rightmost target targetCell state
            | (child, separator) :: remaining =>
                if target = separator then none
                else if CoreChunkPageDelta.indexEntryLess target separator then
                  insertIndexEntryNoSplit? fuel child target targetCell state
                else descend remaining
          descend entries
      | none => do
          let cells ← inlineIndexLeafCells? page
          let inserted ← insertSortedIndexCell? target targetCell cells
          let rewritten ← CoreFile.indexLeafPage? inserted
          state.writePage? pageNumber rewritten

/-- Delete a batch of exact encoded entries by partitioning them at the same
promoted separators used by SQLite routing. Each affected leaf is unpacked and
rewritten once, regardless of how many target rows it contains. -/
def deleteIndexEntriesBatch? : Nat → Nat → List CoreDecode.IndexEntry →
    IndexPageMutations → Option IndexPageMutations
  | 0, _, _, _ => none
  | _, _, [], state => some state
  | fuel + 1, pageNumber, targets, state => do
      let page ← state.readPage? pageNumber
      let source := state.pageSource
      match CoreDecode.decodeIndexInteriorFrom source page with
      | some ([(leftPage, separator)], rightPage) => do
          let leftTargets := targets.filter fun target =>
            CoreChunkPageDelta.indexEntryLess target separator
          let rightTargets := targets.filter fun target =>
            indexEntryAfter target separator
          let left ← deleteIndexEntriesBatch? fuel leftPage leftTargets state
          let right ← deleteIndexEntriesBatch? fuel rightPage rightTargets left
          if targets.contains separator then
            let replacement ← popGreatestIndexEntry? fuel leftPage right
            let rewritten ← indexInteriorPageFromEntries?
              [(leftPage, replacement.1)] rightPage
            replacement.2.writePage? pageNumber rewritten
          else some right
      | some ([(leftPage, firstSeparator),
          (middlePage, secondSeparator)], rightPage) => do
          let leftTargets := targets.filter fun target =>
            CoreChunkPageDelta.indexEntryLess target firstSeparator
          let middleTargets := targets.filter fun target =>
            indexEntryAfter target firstSeparator &&
              CoreChunkPageDelta.indexEntryLess target secondSeparator
          let rightTargets := targets.filter fun target =>
            indexEntryAfter target secondSeparator
          let left ← deleteIndexEntriesBatch? fuel leftPage leftTargets state
          let middle ← deleteIndexEntriesBatch? fuel middlePage
            middleTargets left
          let right ← deleteIndexEntriesBatch? fuel rightPage rightTargets middle
          let first ← if targets.contains firstSeparator then do
              let replacement ← popGreatestIndexEntry? fuel leftPage right
              some (replacement.1, replacement.2)
            else some (firstSeparator, right)
          let second ← if targets.contains secondSeparator then do
              let replacement ← popGreatestIndexEntry? fuel middlePage first.2
              some (replacement.1, replacement.2)
            else some (secondSeparator, first.2)
          if targets.contains firstSeparator || targets.contains secondSeparator then
            let rewritten ← indexInteriorPageFromEntries?
              [(leftPage, first.1), (middlePage, second.1)] rightPage
            second.2.writePage? pageNumber rewritten
          else some second.2
      | some _ => none
      | none => do
          let cells ← inlineIndexLeafCells? page
          let retained ← deleteSortedIndexCells? cells targets
          let rewritten ← CoreFile.indexLeafPage? retained
          state.writePage? pageNumber rewritten

def deletedRowsOrdered? : List Core.Row → List Core.Row →
    Option (List Core.Row)
  | [], [] => some []
  | [], _ :: _ => none
  | rows, [] => some rows
  | old :: olds, row :: rows =>
      if old.rowid = row.rowid then deletedRowsOrdered? olds rows
      else if old.rowid.value < row.rowid.value then do
        let deleted ← deletedRowsOrdered? olds (row :: rows)
        some (old :: deleted)
      else none

/-- The merge walk accounts for every pre-state row exactly once: a row is
either consumed by the retained post-state or returned as deleted. -/
theorem deletedRowsOrdered?_length {before after deleted : List Core.Row}
    (success : deletedRowsOrdered? before after = some deleted) :
    before.length = deleted.length + after.length := by
  induction before generalizing after deleted with
  | nil =>
      cases after with
      | nil =>
          simp only [deletedRowsOrdered?, Option.some.injEq] at success
          subst deleted
          rfl
      | cons row rows => simp [deletedRowsOrdered?] at success
  | cons old olds induction =>
      cases after with
      | nil =>
          simp only [deletedRowsOrdered?, Option.some.injEq] at success
          subst deleted
          simp
      | cons row rows =>
          simp only [deletedRowsOrdered?] at success
          split at success
          next =>
            have tail := induction success
            simp only [List.length_cons]
            omega
          next =>
            split at success
            next =>
              rcases Option.bind_eq_some.mp success with ⟨tail, recursive, equal⟩
              simp only [Option.some.injEq] at equal
              subst deleted
              have tailLength := induction (after := row :: rows) recursive
              simp only [List.length_cons] at tailLength ⊢
              omega
            next => contradiction

def deletedRows? (before after : Core.Table) : Option (List Core.Row) :=
  deletedRowsOrdered? before.rows after.rows

def deleteIndexRowsFromPages? (rootPage : Nat) (index : Core.Index)
    (rows : List Core.Row) (source : CoreDecode.PageSource) :
    Option IndexPageMutations :=
  deleteIndexEntriesBatch? (source.pageCount + 1) rootPage
    (CoreChunkPageDelta.sortIndexEntries
      (rows.map (CoreChunkPageDelta.indexEntryOfRow index))) { source }

def insertIndexRowIntoPages? (rootPage : Nat) (index : Core.Index)
    (row : Core.Row) (source : CoreDecode.PageSource) :
    Option IndexPageMutations := do
  let entry := CoreChunkPageDelta.indexEntryOfRow index row
  let cell ← indexEntryCell? entry
  insertIndexEntryNoSplit? (source.pageCount + 1) rootPage entry cell { source }

def mutationPageWrites? (mutated : IndexPageMutations) :
    Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize) ×
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) := do
  let pairs ← mutated.changed.mapM fun changed => do
      let pageNumber := changed.1
      let oldBytes ← mutated.source.readPage pageNumber
      let newBytes := changed.2
      let oldPage ← storagePage? oldBytes
      let newPage ← storagePage? newBytes
      some ((⟨pageNumber - 1, oldPage⟩ :
        GrowableStorage.PageWrite PhysicalCodec.pageSize),
        (⟨pageNumber - 1, newPage⟩ :
          GrowableStorage.PageWrite PhysicalCodec.pageSize))
  some (pairs.map (fun pair => pair.1), pairs.map (fun pair => pair.2))

def physicalCatalogEntry? (entry : CoreDecode.CatalogEntry) :
    Option CoreFile.CatalogEntry := do
  let sql ← entry.sql
  some {
    kind := entry.kind
    name := entry.name
    table := entry.table
    rootPage := entry.rootPage
    sql }

/-- Append a newly-created secondary index without re-encoding any table.
The old catalog comes from the validating open; the added index is the ordinary
proved encoder rooted immediately after the current file. -/
def prepareAppendedIndex? (validated : ValidatedOpenState)
    (input : ByteArray) (delta : CoreChunkPageDelta.StateDelta) :
    Option (LocalizedLastIndexDelta delta) := do
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPageBytes
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noExistingFree : header.freelistPageCount.val = 0 then
      if _length : input.size = count * PhysicalCodec.pageSize then
        if _sameDatabase : validated.state.database.Equiv delta.before.database then
          let before := delta.table.before.table
          let after := delta.table.after.table
          if _sameSchema : before.schema = after.schema then
            if _sameRows : before.rows = after.rows then
              match after.indexes with
              | index :: previous =>
                  if _oneAdded : previous = before.indexes then
                    let source := byteArrayPageSource input count
                    let firstPage ← source.readPage 1
                    let catalog ← CoreDecode.decodeCatalogForOpen firstPage
                    let entries ← catalog.mapM physicalCatalogEntry?
                    let rootPage := count + 1
                    let certified ← certifyIndexEncoding? rootPage after index
                    let encoding := certified.value
                    let newCount := count + encoding.pages.length
                    if _nonempty : 0 < encoding.pages.length then
                      if countBound : newCount < 2 ^ 32 then
                        let pageCount : FileFormat.U32Value :=
                          ⟨newCount, countBound⟩
                        let schemaPage ← CoreFile.schemaPageForEntries?
                          (entries ++ [encoding.catalogEntry]) pageCount
                        let oldPage ← storagePage? firstPageBytes
                        let writes :=
                          (⟨0, schemaPage.storage⟩ :
                            GrowableStorage.PageWrite PhysicalCodec.pageSize) ::
                          indexPageWrites rootPage encoding.pages
                        let state := { delta.after with
                          nextPage := newCount + 1 }
                        if distinct : writes.Pairwise
                            (fun left right => left.pageId ≠ right.pageId) then
                          if allocation : state.AllocationWellFormed then
                            some {
                              state
                              index
                              rootPage
                              certificate := .encoded certified
                              expectedBefore := [⟨0, oldPage⟩]
                              writes
                              writesDistinct := distinct
                              allocation
                              validated := ⟨state, ()⟩ }
                          else none
                        else none
                      else none
                    else none
                  else none
              | [] => none
            else none
          else none
        else none
      else none
    else none
  else none

/-- Insert one row into the one tail-owned generated secondary index by
rewriting only its routed leaf.  This intentionally has no split case: a full
leaf returns `none` and retains the certified rebuild path.  A successful byte
mutation is not trusted by itself; `certifyDecodedIndex?` below proves that the
complete resulting physical index is exactly the logical post-state. -/
def preparePageDirectedIndexInsert? (validated : ValidatedOpenState)
    (input : ByteArray) (delta : CoreChunkPageDelta.StateDelta) :
    Option (LocalizedLastIndexDelta delta) := do
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPageBytes
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noExistingFree : header.freelistPageCount.val = 0 then
      if _length : input.size = count * PhysicalCodec.pageSize then
        let source := byteArrayPageSource input count
        let firstPage ← source.readPage 1
        let catalog ← CoreDecode.decodeCatalogForOpen firstPage
        let before := delta.table.before.table
        let after := delta.table.after.table
        if _grew : before.rows.length < after.rows.length then
          if _oneRow : after.rows.length = before.rows.length + 1 then
            if _sameDatabase : validated.state.database.Equiv
                delta.before.database then
              if _sameSchema : before.schema = after.schema then
                if _sameIndexes : before.indexes = after.indexes then
                  match before.indexes with
                  | [index] => do
                      let row ← CoreChunkPageDelta.firstInserted
                        before.rows after.rows
                      let entry ← catalog.find? fun entry =>
                        entry.kind == "index" && entry.name == index.name &&
                          entry.table == after.schema.name
                      if _lastRoot : catalog.all fun candidate =>
                          candidate.rootPage ≤ entry.rootPage then
                        if _rootRange : 1 < entry.rootPage ∧
                            entry.rootPage ≤ count then
                          let mutated ← insertIndexRowIntoPages?
                            entry.rootPage index row source
                          let certificate ← certifyDecodedIndex? entry.rootPage
                            after index mutated.pageSource
                          let indexDelta ← mutationPageWrites? mutated
                          let tableBefore ←
                            CoreChunkPageDelta.beforeWrites delta.table
                          let tableWrites ← CoreChunkPageDelta.writes delta.table
                          let expectedBefore := tableBefore ++ indexDelta.1
                          let writes := tableWrites ++ indexDelta.2
                          if _tableBeforeIndex :
                                delta.table.before.tree.root.pageIds.all
                                    (fun pageId => pageId < entry.rootPage) &&
                              delta.table.after.tree.root.pageIds.all
                                    (fun pageId => pageId < entry.rootPage) then
                            if distinct : writes.Pairwise
                                (fun left right => left.pageId ≠ right.pageId) then
                              if allocation : delta.after.AllocationWellFormed then
                                some {
                                  state := delta.after
                                  index
                                  rootPage := entry.rootPage
                                  certificate := .decoded certificate
                                  expectedBefore
                                  writes
                                  writesDistinct := distinct
                                  allocation
                                  validated := ⟨delta.after, ()⟩ }
                              else none
                            else none
                          else none
                        else none
                      else none
                  | _ => none
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

/-- Delete a set of rows from the one tail-owned generated secondary index by
descending only through pages that contain those entries. No index sort,
pagination, or whole-index encoding occurs. A promoted interior entry is
replaced by the greatest entry of its left subtree, so SQLite's promoted-key
semantics are preserved without duplication. Any overflow, page-fit, routing,
or allocation miss returns `none` and retains the certified rebuild path. -/
def preparePageDirectedIndexDelete? (validated : ValidatedOpenState)
    (input : ByteArray) (delta : CoreChunkPageDelta.StateDelta) :
    Option (LocalizedLastIndexDelta delta) := do
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPageBytes
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noExistingFree : header.freelistPageCount.val = 0 then
      if _length : input.size = count * PhysicalCodec.pageSize then
        let source := byteArrayPageSource input count
        let firstPage ← source.readPage 1
        let catalog ← CoreDecode.decodeCatalogForOpen firstPage
        let before := delta.table.before.table
        let after := delta.table.after.table
        if _shrunk : after.rows.length < before.rows.length then
          if _sameDatabase : validated.state.database.Equiv
              delta.before.database then
            if _sameSchema : before.schema = after.schema then
              if _sameIndexes : before.indexes = after.indexes then
                match before.indexes with
                | [index] => do
                    let entry ← catalog.find? fun entry =>
                      entry.kind == "index" && entry.name == index.name &&
                        entry.table == after.schema.name
                    if _lastRoot : catalog.all fun candidate =>
                        candidate.rootPage ≤ entry.rootPage then
                      if _rootRange : 1 < entry.rootPage ∧ entry.rootPage ≤ count then
                        let removed ← deletedRows? before after
                        let mutated ← deleteIndexRowsFromPages?
                          entry.rootPage index removed source
                        let certificate ← certifyDecodedIndex? entry.rootPage
                          after index mutated.pageSource
                        let indexDelta ← mutationPageWrites? mutated
                        let tableBefore ←
                          CoreChunkPageDelta.beforeWrites delta.table
                        let tableWrites ← CoreChunkPageDelta.writes delta.table
                        let expectedBefore := tableBefore ++ indexDelta.1
                        let writes := tableWrites ++ indexDelta.2
                        if _tableBeforeIndex :
                              delta.table.before.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) &&
                            delta.table.after.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) then
                          if distinct : writes.Pairwise
                              (fun left right => left.pageId ≠ right.pageId) then
                            if allocation : delta.after.AllocationWellFormed then
                              some {
                                state := delta.after
                                index
                                rootPage := entry.rootPage
                                certificate := .decoded certificate
                                expectedBefore
                                writes
                                writesDistinct := distinct
                                allocation
                                validated := ⟨delta.after, ()⟩ }
                            else none
                          else none
                        else none
                      else none
                    else none
                | _ => none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

/-- Localize one changed generated index when it owns the final file interval.
The validating-open capability records that the old index matched the logical
pre-state; the replacement is the ordinary proved index encoder rooted at the
same page. Every page after the shorter replacement becomes freelist space.
General files, multiple changed indexes, non-tail ownership, or replacement
indexes that exceed the old tail return `none` and keep the full compatibility
commit. -/
def prepareLocalizedLastIndex? (validated : ValidatedOpenState)
    (input : List UInt8)
    (delta : CoreChunkPageDelta.StateDelta) :
    Option (LocalizedLastIndexDelta delta) := do
  let (header, _) ← FileFormat.decodeDatabaseHeader input
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noExistingFree : header.freelistPageCount.val = 0 then
      if _length : input.length = count * PhysicalCodec.pageSize then
        let physicalPages := CoreDecode.pages count input
        let source := CoreDecode.PageSource.ofList physicalPages
        let firstPage ← source.readPage 1
        let catalog ← CoreDecode.decodeCatalogForOpen firstPage
        let before := delta.table.before.table
        let after := delta.table.after.table
        if _sameDatabase : validated.state.database.Equiv
            delta.before.database then
          if _sameSchema : before.schema = after.schema then
            if _sameIndexes : before.indexes = after.indexes then
              -- Every index entry carries the rowid, so insertion/deletion
              -- necessarily changes every index. Avoid constructing two full
              -- source images merely to rediscover the cardinality change.
              let changed :=
                if before.rows.length == after.rows.length then
                  before.indexes.filter fun index =>
                    before.rows.map
                        (CoreChunkPageDelta.indexEntryOfRow index) !=
                      after.rows.map
                        (CoreChunkPageDelta.indexEntryOfRow index)
                else before.indexes
              match changed with
              | [index] => do
                  let entry ← catalog.find? fun entry =>
                    entry.kind == "index" &&
                      entry.name == index.name &&
                      entry.table == after.schema.name
                  if _lastRoot : catalog.all fun candidate =>
                      candidate.rootPage ≤ entry.rootPage then
                    if _rootRange : 1 < entry.rootPage ∧ entry.rootPage ≤ count then
                      let certified ← certifyIndexEncoding?
                          entry.rootPage after index
                      let encoding := certified.value
                      let oldCount := count + 1 - entry.rootPage
                      if _fits : 0 < encoding.pages.length ∧
                            encoding.pages.length ≤ oldCount then
                        if _tableBeforeIndex :
                              delta.table.before.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) &&
                                delta.table.after.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) then
                          let tableBefore ←
                              CoreChunkPageDelta.beforeWrites delta.table
                          let tableWrites ←
                              CoreChunkPageDelta.writes delta.table
                          let oldTail ←
                              (List.range' entry.rootPage oldCount).mapM
                                fun pageNumber => do
                                  let bytes ← source.readPage pageNumber
                                  let page ← storagePage? bytes
                                  some ⟨pageNumber - 1, page⟩
                          let indexWrites := changedPageWrites oldTail
                              (indexPageWrites entry.rootPage encoding.pages)
                          let writes := tableWrites ++ indexWrites
                          let expectedBefore := tableBefore ++ oldTail
                          let released := List.range'
                              (entry.rootPage + encoding.pages.length)
                              (oldCount - encoding.pages.length)
                          let freePages := CoreChunkPageDelta.addFreePages
                              delta.after.freePages released
                          let state := { delta.after with freePages }
                          if distinct : writes.Pairwise
                                (fun left right => left.pageId ≠ right.pageId) then
                            if allocation : state.AllocationWellFormed then
                              some {
                                  state
                                  index
                                  rootPage := entry.rootPage
                                  certificate := .encoded certified
                                  expectedBefore
                                  writes
                                  writesDistinct := distinct
                                  allocation
                                  validated := ⟨state, ()⟩ }
                            else none
                          else none
                        else none
                      else none
                    else none
                  else none
              | _ => none
            else none
          else none
        else none
      else none
    else none
  else none

structure IndexLookup where
  candidates : List Core.Row
  pagesRead : Nat

structure PrimaryLookup where
  schema : Core.Schema
  row : Core.Row
  pagesRead : Nat

inductive PrimaryLookupOutcome where
  | found (row : Core.Row)
  | generatedMissing

/-- A page-directed lookup which preserves the distinction between a decoded
row and a complete miss in a stamped Lean-generated image.  Malformed bytes
and misses in general SQLite files remain `none`. -/
structure PrimaryLookupDecision where
  schema : Core.Schema
  outcome : PrimaryLookupOutcome
  pagesRead : Nat

/-- Physical inputs for a certified primary-key merge join.  The right table
is decoded once; the left side contains only rows at or below its greatest
key, obtained by separator-directed traversal. -/
structure PrimaryJoinLookup where
  leftSchema : Core.Schema
  rightSchema : Core.Schema
  leftCandidates : List Core.Row
  rightRows : List Core.Row
  bound : Option Core.Integer
  pagesRead : Nat

inductive IntegerIndexRouting (source : CoreDecode.PageSource)
    (fuel rootPage : Nat) (expected : List CoreDecode.IndexEntry) where
  | generated (certificate : CoreDecode.CertifiedIntegerIndex
      source fuel rootPage expected)
  | general (certificate : CoreDecode.CertifiedWideIntegerIndex
      source fuel rootPage expected)
  | allValues (certificate : CoreDecode.CertifiedAllValueIndex
      source fuel rootPage expected)

def IntegerIndexRouting.valueEntries
    {source : CoreDecode.PageSource} {fuel rootPage : Nat}
    {expected : List CoreDecode.IndexEntry}
    (routing : IntegerIndexRouting source fuel rootPage expected)
    (target : Core.Value) : List CoreDecode.IndexEntry :=
  match routing with
  | .generated _certificate =>
      (CoreDecode.lookupIndexValueFrom source target fuel rootPage).getD []
  | .general certificate => certificate.valueEntries target
  | .allValues certificate => certificate.valueEntries target

theorem IntegerIndexRouting.valueEntries_exact
    {source : CoreDecode.PageSource} {fuel rootPage : Nat}
    {expected : List CoreDecode.IndexEntry}
    (routing : IntegerIndexRouting source fuel rootPage expected)
    (target : Core.Value) :
    routing.valueEntries target =
      expected.filter (fun entry => entry.matchesValue target) := by
  cases routing with
  | generated certificate =>
      simp [IntegerIndexRouting.valueEntries,
        CoreDecode.lookupIndexValueFrom_certified_exact certificate target]
  | general certificate => exact certificate.valueEntries_exact target
  | allValues certificate => exact certificate.valueEntries_exact target

def IntegerIndexRouting.rangeEntries
    {source : CoreDecode.PageSource} {fuel rootPage : Nat}
    {expected : List CoreDecode.IndexEntry}
    (routing : IntegerIndexRouting source fuel rootPage expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    List CoreDecode.IndexEntry :=
  match routing with
  | .generated _certificate =>
      (CoreDecode.lookupIndexRangeFrom source operation target fuel rootPage)
        |>.getD []
  | .general certificate => certificate.rangeEntries operation target
  | .allValues certificate => certificate.rangeEntries operation target

theorem IntegerIndexRouting.rangeEntries_exact
    {source : CoreDecode.PageSource} {fuel rootPage : Nat}
    {expected : List CoreDecode.IndexEntry}
    (routing : IntegerIndexRouting source fuel rootPage expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    routing.rangeEntries operation target =
      expected.filter (fun entry => entry.matchesRange operation target) := by
  cases routing with
  | generated certificate =>
      simp [IntegerIndexRouting.rangeEntries,
        CoreDecode.lookupIndexRangeFrom_certified_exact certificate operation
          target]
  | general certificate => exact certificate.rangeEntries_exact operation target
  | allValues certificate => exact certificate.rangeEntries_exact operation target

/-- A certificate retained by a live connection.  Its dependent proof ties a
specific physical page source to the exact logical entries of `table/index`.
The connection invalidates these values on mutation until localized
certificate maintenance is implemented. -/
structure StoredIntegerIndex where
  table : Core.Table
  index : Core.Index
  source : CoreDecode.PageSource
  fuel : Nat
  rootPage : Nat
  expected : List CoreDecode.IndexEntry
  expected_eq : expected = CoreDecode.expectedIndexEntries table index
  certificate : IntegerIndexRouting source fuel rootPage expected

/-- Rebind a physical index certificate to a newer logical table when the
exact abstract index entries are unchanged.  The dependent certificate itself
is reused: it names only the immutable page source and `expected` list. -/
def StoredIntegerIndex.retarget (stored : StoredIntegerIndex)
    (table : Core.Table) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) : StoredIntegerIndex := {
  table
  index
  source := stored.source
  fuel := stored.fuel
  rootPage := stored.rootPage
  expected := stored.expected
  expected_eq := sameExpected.symm
  certificate := stored.certificate }

@[simp] theorem StoredIntegerIndex.retarget_expected
    (stored : StoredIntegerIndex) (table : Core.Table) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) :
    (stored.retarget table index sameExpected).expected = stored.expected := rfl

theorem StoredIntegerIndex.retarget_value_exact
    (stored : StoredIntegerIndex) (table : Core.Table) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) (target : Core.Value) :
    (stored.retarget table index sameExpected).certificate.valueEntries target =
      (CoreDecode.expectedIndexEntries table index).filter
        (fun entry => entry.matchesValue target) := by
  change stored.certificate.valueEntries target = _
  rw [stored.certificate.valueEntries_exact, sameExpected]

theorem StoredIntegerIndex.retarget_range_exact
    (stored : StoredIntegerIndex) (table : Core.Table) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) (operation : PhysicalQuery.Comparison)
    (target : Core.Value) :
    (stored.retarget table index sameExpected).certificate.rangeEntries
        operation target =
      (CoreDecode.expectedIndexEntries table index).filter
        (fun entry => entry.matchesRange operation target) := by
  change stored.certificate.rangeEntries operation target = _
  rw [stored.certificate.rangeEntries_exact, sameExpected]

/-- Checked certificate maintenance for a localized table mutation.  Schema,
index identity and the complete logical index image must all agree. -/
def StoredIntegerIndex.retarget? (stored : StoredIntegerIndex)
    (database : Core.Database) : Option StoredIntegerIndex := do
  let table ← database.findTable? stored.table.schema.name
  if _sameSchema : table.schema = stored.table.schema then
    let index ← table.indexes.find? fun candidate =>
      candidate.name == stored.index.name
    if _sameIndex : index = stored.index then
      if sameExpected : CoreDecode.expectedIndexEntries table index =
          stored.expected then
        some (stored.retarget table index sameExpected)
      else none
    else none
  else none

def retargetIntegerIndexCertificates
    (certificates : List StoredIntegerIndex) (database : Core.Database) :
    List StoredIntegerIndex :=
  certificates.filterMap fun stored => stored.retarget? database

def certifyIntegerIndexes (physicalPages : List (List UInt8))
    (catalog : List CoreDecode.CatalogEntry) (database : Core.Database) :
    List StoredIntegerIndex :=
  let source := CoreDecode.PageSource.ofList physicalPages
  let fuel := physicalPages.length + 1
  database.tables.flatMap fun table =>
    table.indexes.filterMap fun index =>
      match catalog.find? (fun entry =>
        entry.kind == "index" && entry.name == index.name &&
          entry.table == table.schema.name) with
      | none => none
      | some catalogEntry =>
          let expected := CoreDecode.expectedIndexEntries table index
          match CoreDecode.certifyIntegerIndex source fuel
              catalogEntry.rootPage expected with
          | none =>
              match CoreDecode.certifyWideIntegerIndex source fuel
                  catalogEntry.rootPage expected with
              | none =>
                  match CoreDecode.certifyAllValueIndex source fuel
                      catalogEntry.rootPage expected with
                  | none => none
                  | some certificate =>
                      some ⟨table, index, source, fuel, catalogEntry.rootPage,
                        expected, rfl, .allValues certificate⟩
              | some certificate =>
                  some ⟨table, index, source, fuel, catalogEntry.rootPage,
                    expected, rfl, .general certificate⟩
          | some certificate =>
              some ⟨table, index, source, fuel, catalogEntry.rootPage,
                expected, rfl, .generated certificate⟩

def loadIntegerIndexCertificates (paths : Paths) (database : Core.Database) :
    IO (List StoredIntegerIndex) := do
  let input ← IO.FS.readBinFile paths.main
  let bytes := input.data.toList
  let some (header, _) := FileFormat.decodeDatabaseHeader bytes | return []
  let count := header.databaseSizePages.val
  unless input.size = count * PhysicalCodec.pageSize do return []
  let physicalPages := CoreDecode.pages count bytes
  let some catalog := physicalPages.head?.bind CoreDecode.decodeCatalog |
    return []
  return certifyIntegerIndexes physicalPages catalog database

def readTableSchema (paths : Paths) (tableName : String) :
    IO (Option Core.Schema) := do
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let some firstPage ← readPageBytes handle | return none
    let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
      return none
    let count := header.databaseSizePages.val
    unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
        header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
        metadata.byteSize.toNat = count * PhysicalCodec.pageSize do return none
    let some catalog := CoreDecode.decodeCatalog firstPage | return none
    let some entry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == tableName | return none
    let some sql := entry.sql | return none
    let some schema := CoreDecode.parseTableSchema sql | return none
    if schema.name = tableName then return some schema else return none

/-- Cold, page-directed primary lookup with a generated-image miss
certificate.  The nested decoder result distinguishes malformed input from a
valid leaf miss.  A miss is exposed only when the parsed header carries the
stamp established by `CorePageCodec.encodeBulk_generatedHeader`; ordinary
SQLite writes invalidate its change-counter half.  Found rows remain usable
for general compatible SQLite files after their schema and row invariants are
checked locally. -/
def lookupPrimaryRowDecision (paths : Paths) (tableName : String)
    (rowid : Core.Integer) : IO (Option PrimaryLookupDecision) := do
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let some firstPage ← readPageBytes handle | return none
    let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
      return none
    let count := header.databaseSizePages.val
    unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
        header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
        metadata.byteSize.toNat = count * PhysicalCodec.pageSize do return none
    let some catalog := CoreDecode.decodeCatalog firstPage | return none
    let some entry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == tableName | return none
    let some sql := entry.sql | return none
    let some schema := CoreDecode.parseTableSchema sql | return none
    unless schema.name = tableName do return none
    let reads ← IO.mkRef 0
    let base := preadPageSource paths.main count
    let source : CoreDecode.IOPageSource := {
      pageCount := count
      readPage := fun pageNumber => do
        reads.modify (· + 1)
        base.readPage pageNumber }
    let some result ← CoreDecode.lookupTableRowidIOFrom schema source rowid
        (count + 1) entry.rootPage | return none
    match result with
    | some row =>
        unless row.rowid = rowid && row.WellFormed schema do return none
        return some ⟨schema, .found row, ← reads.get⟩
    | none =>
        unless CoreFile.hasGeneratedImageStamp header do return none
        return some ⟨schema, .generatedMissing, ← reads.get⟩

/-- Compatibility projection for callers interested only in successful hits.
Unlike `lookupPrimaryRowDecision`, this continues to collapse a valid miss. -/
def lookupPrimaryRow (paths : Paths) (tableName : String)
    (rowid : Core.Integer) : IO (Option PrimaryLookup) := do
  let some decision ← lookupPrimaryRowDecision paths tableName rowid |
    return none
  match decision.outcome with
  | .found row => return some ⟨decision.schema, row, decision.pagesRead⟩
  | .generatedMissing => return none

/-- Cold, separator-directed primary-key range lookup for a generated image.
The generated stamp supplies the encoder provenance needed by the pure
byte-level refinement theorem; rows are additionally checked against the
decoded schema and requested predicate before they cross the IO boundary. -/
def lookupGeneratedPrimaryRange (paths : Paths) (tableName : String)
    (schema : Core.Schema) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) : IO (Option IndexLookup) := do
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
    let reads ← IO.mkRef 0
    let base := preadPageSource paths.main count
    let source : CoreDecode.IOPageSource := {
      pageCount := count
      readPage := fun pageNumber => do
        reads.modify (· + 1)
        base.readPage pageNumber }
    let some candidates ← CoreDecode.lookupTableRangeIOFrom schema source
        operation target (count + 1) tableEntry.rootPage | return none
    unless candidates.all fun row =>
        row.WellFormed schema &&
          CoreDecode.tableRowMatchesRange operation target row do return none
    return some ⟨candidates, ← reads.get⟩

/-- Cold primary-key join acquisition for a stamped Lean-generated image.
Only the right table is decoded in full.  Its greatest rowid bounds an exact
separator-directed range read on the left; an empty right side avoids reading
the left tree altogether.  Local well-formedness checks keep malformed bytes
from crossing the IO boundary, while the generated stamp connects this path
to the encoder/range exactness theorems. -/
def lookupGeneratedPrimaryJoin (paths : Paths) (leftName rightName : String) :
    IO (Option PrimaryJoinLookup) := do
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
    let some leftEntry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == leftName | return none
    let some rightEntry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == rightName | return none
    let some leftSql := leftEntry.sql | return none
    let some rightSql := rightEntry.sql | return none
    let some leftSchema := CoreDecode.parseTableSchema leftSql | return none
    let some rightSchema := CoreDecode.parseTableSchema rightSql | return none
    unless leftSchema.name = leftName && rightSchema.name = rightName do
      return none
    let reads ← IO.mkRef 0
    let base := preadPageSource paths.main count
    let source : CoreDecode.IOPageSource := {
      pageCount := count
      readPage := fun pageNumber => do
        reads.modify (· + 1)
        base.readPage pageNumber }
    let some rightRows ← CoreDecode.decodeSubtreeRowsIOFrom rightSchema source
        (count + 1) rightEntry.rootPage | return none
    if _rightWellFormed : Core.RowsWellFormed rightSchema rightRows then
      match rightRows.getLast? with
      | none =>
          return some ⟨leftSchema, rightSchema, [], rightRows, none, ← reads.get⟩
      | some last =>
          unless rightRows.all fun row =>
              decide (row.rowid.value ≤ last.rowid.value) do return none
          let some leftCandidates ← CoreDecode.lookupTableRangeIOFrom leftSchema
              source .lessEqual last.rowid (count + 1) leftEntry.rootPage |
            return none
          if _leftWellFormed :
              Core.RowsWellFormed leftSchema leftCandidates then
            unless leftCandidates.all fun row =>
                CoreDecode.tableRowMatchesRange .lessEqual last.rowid row do
              return none
            return some ⟨leftSchema, rightSchema, leftCandidates, rightRows,
              some last.rowid, ← reads.get⟩
          else return none
    else return none

private inductive IndexLookupTarget where
  | equality (value : Core.Value)
  | range (operation : PhysicalQuery.Comparison) (value : Core.Value)

private def rowidLe (left right : Core.Row) : Bool :=
  decide (left.rowid.value ≤ right.rowid.value)

def rowForIndexEntry? (table : Core.Table)
    (entry : CoreDecode.IndexEntry) : Option Core.Row :=
  table.findRowid? entry.rowid

/-- Resolve persisted index rowids through the proof-carrying primary tree.
The former implementation filtered every table row, making even a selective
index lookup O(table size).  Sorting only the returned rows restores the
table-order semantics required when SQL has no ORDER BY. -/
def rowsForIndexEntries (table : Core.Table)
    (entries : List CoreDecode.IndexEntry) : List Core.Row :=
  (entries.filterMap (rowForIndexEntry? table)).mergeSort rowidLe

theorem filterMap_expectedIndexEntries (table : Core.Table)
    (index : Core.Index) (rows : List Core.Row)
    (members : ∀ row ∈ rows, row ∈ table.rows)
    (keepEntry : CoreDecode.IndexEntry → Bool) (keepRow : Core.Row → Bool)
    (sameKeep : ∀ row ∈ rows,
      keepEntry ⟨row.value index.column, row.rowid⟩ = keepRow row) :
    (((rows.map fun row : Core.Row =>
        (⟨row.value index.column, row.rowid⟩ : CoreDecode.IndexEntry)).filter
      keepEntry).filterMap (rowForIndexEntry? table)) = rows.filter keepRow := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      have rowMember : row ∈ table.rows := members row (by simp)
      have tailMembers : ∀ candidate ∈ rows, candidate ∈ table.rows := by
        intro candidate member
        exact members candidate (by simp [member])
      have rowLookup : rowForIndexEntry? table
          ⟨row.value index.column, row.rowid⟩ = some row := by
        unfold rowForIndexEntry?
        exact Core.Table.findRowid?_eq_some_of_mem rowMember rfl
      have keep := sameKeep row (by simp)
      have tailKeep : ∀ candidate ∈ rows,
          keepEntry ⟨candidate.value index.column, candidate.rowid⟩ =
            keepRow candidate := by
        intro candidate member
        exact sameKeep candidate (by simp [member])
      cases kept : keepRow row <;>
        simp [keep, kept, rowLookup, induction tailMembers tailKeep]

theorem rowsForExpectedIndexEntries (table : Core.Table) (index : Core.Index)
    (keepEntry : CoreDecode.IndexEntry → Bool) (keepRow : Core.Row → Bool)
    (sameKeep : ∀ row ∈ CoreFile.sortedIndexRows table index,
      keepEntry ⟨row.value index.column, row.rowid⟩ = keepRow row) :
    rowsForIndexEntries table
        ((CoreDecode.expectedIndexEntries table index).filter keepEntry) =
      table.rows.filter keepRow := by
  have sortedMembers : ∀ row ∈ CoreFile.sortedIndexRows table index,
      row ∈ table.rows := by
    intro row member
    exact (CoreFile.sortedIndexRows_perm table index).subset member
  have resolved :
      (((CoreDecode.expectedIndexEntries table index).filter keepEntry).filterMap
        (rowForIndexEntry? table)) =
        (CoreFile.sortedIndexRows table index).filter keepRow := by
    exact filterMap_expectedIndexEntries table index
      (CoreFile.sortedIndexRows table index) sortedMembers keepEntry keepRow
      sameKeep
  have resolvedPerm :
      (((CoreDecode.expectedIndexEntries table index).filter keepEntry).filterMap
          (rowForIndexEntry? table)).Perm (table.rows.filter keepRow) := by
    rw [resolved]
    exact (CoreFile.sortedIndexRows_perm table index).filter keepRow
  let candidates :=
    ((CoreDecode.expectedIndexEntries table index).filter keepEntry).filterMap
      (rowForIndexEntry? table)
  have candidatePerm : (candidates.mergeSort rowidLe).Perm
      (table.rows.filter keepRow) :=
    (List.mergeSort_perm candidates rowidLe).trans resolvedPerm
  have rowidLeTrans : ∀ (left middle right : Core.Row),
      rowidLe left middle = true → rowidLe middle right = true →
        rowidLe left right = true := by
    intro left middle right leftMiddle middleRight
    simp only [rowidLe, decide_eq_true_eq] at leftMiddle middleRight ⊢
    omega
  have rowidLeTotal : ∀ (left right : Core.Row),
      (rowidLe left right || rowidLe right left) = true := by
    intro left right
    simp only [rowidLe, Bool.or_eq_true, decide_eq_true_eq]
    omega
  have candidatesSorted : (candidates.mergeSort rowidLe).Pairwise
      (fun left right => rowidLe left right = true) :=
    List.sorted_mergeSort rowidLeTrans rowidLeTotal candidates
  have tableSorted : (table.rows.filter keepRow).Pairwise
      (fun left right => rowidLe left right = true) := by
    have strict := table.rowsWellFormed.2.filter keepRow
    exact strict.imp fun less => by
      simp only [rowidLe, decide_eq_true_eq]
      exact Int.le_of_lt less
  unfold rowsForIndexEntries
  change candidates.mergeSort rowidLe = table.rows.filter keepRow
  apply candidatePerm.eq_of_sorted _ candidatesSorted tableSorted
  intro left right leftMember rightMember leftRight rightLeft
  have leftFiltered : left ∈ table.rows.filter keepRow :=
    candidatePerm.subset leftMember
  have leftTable : left ∈ table.rows := (List.mem_filter.mp leftFiltered).1
  have rightTable : right ∈ table.rows := (List.mem_filter.mp rightMember).1
  simp only [rowidLe, decide_eq_true_eq] at leftRight rightLeft
  have rowidValue : left.rowid.value = right.rowid.value :=
    Int.le_antisymm leftRight rightLeft
  have rowid : left.rowid = right.rowid :=
    FileFormat.SignedInteger.ext rowidValue
  have leftLookup := Core.Table.findRowid?_eq_some_of_mem leftTable rfl
  have rightLookup := Core.Table.findRowid?_eq_some_of_mem rightTable rfl
  rw [rowid] at leftLookup
  exact Option.some.inj (leftLookup.symm.trans rightLookup)

theorem rowsForExpectedValue_exact (table : Core.Table) (index : Core.Index)
    (target : Core.Value) :
    rowsForIndexEntries table
        ((CoreDecode.expectedIndexEntries table index).filter
          (fun entry => entry.matchesValue target)) =
      table.rows.filter
        (Core.selects (some (.equal index.column target))) := by
  apply rowsForExpectedIndexEntries table index
  intro row member
  simp [CoreDecode.IndexEntry.matchesValue, Core.selects,
    Core.Predicate.eval, Core.indexColumnMatches]

theorem rowsForExpectedRange_exact (table : Core.Table) (index : Core.Index)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    rowsForIndexEntries table
        ((CoreDecode.expectedIndexEntries table index).filter
          (fun entry => entry.matchesRange operation target)) =
      table.rows.filter
        (Core.selects (some (.compare operation index.column target))) := by
  apply rowsForExpectedIndexEntries table index
  intro row member
  simp [CoreDecode.IndexEntry.matchesRange, Core.selects,
    Core.Predicate.eval]

structure CertifiedCandidates (table : Core.Table) (query : Core.Query) where
  candidates : List Core.Row
  exact : query.eval candidates = query.eval table.rows

def CertifiedCandidates.result {table : Core.Table} {query : Core.Query}
    (certified : CertifiedCandidates table query) : Core.Result :=
  { rows := query.eval certified.candidates }

theorem CertifiedCandidates.result_exact {table : Core.Table}
    {query : Core.Query} (certified : CertifiedCandidates table query) :
    certified.result.rows = query.eval table.rows := by
  exact certified.exact

def certifiedEqualityCandidates (stored : StoredIntegerIndex)
    (table : Core.Table) (query : Core.Query) (target : Core.Value)
    (rowsEqual : stored.table.rows = table.rows)
    (predicateEqual : query.predicate =
      some (.equal stored.index.column target)) :
    CertifiedCandidates table query :=
  let entries := stored.certificate.valueEntries target
  let candidates := rowsForIndexEntries table entries
  have entriesEqual : entries = stored.expected.filter
      (fun entry => entry.matchesValue target) := by
    unfold entries
    exact stored.certificate.valueEntries_exact target
  have candidatesEqual : candidates = table.rows.filter
      (Core.selects query.predicate) := by
    unfold candidates
    have expectedCurrent : stored.expected =
        CoreDecode.expectedIndexEntries table stored.index := by
      rw [stored.expected_eq]
      simp [CoreDecode.expectedIndexEntries, CoreFile.sortedIndexRows,
        CoreFile.indexValuesInteger, CoreFile.indexValuesText,
        rowsEqual]
    rw [entriesEqual, expectedCurrent, rowsForExpectedValue_exact]
    rw [predicateEqual, ← rowsEqual]
  have narrowed : Core.indexedCandidates stored.index query.predicate
      table.rows = some candidates := by
    rw [predicateEqual]
    simp only [Core.indexedCandidates, ↓reduceIte]
    rw [candidatesEqual, predicateEqual]
  ⟨candidates, Core.Query.eval_indexed stored.index query table.rows candidates
    narrowed⟩

def certifiedRangeCandidates (stored : StoredIntegerIndex)
    (table : Core.Table) (query : Core.Query)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (rowsEqual : stored.table.rows = table.rows)
    (predicateEqual : query.predicate =
      some (.compare operation stored.index.column target)) :
    CertifiedCandidates table query :=
  let entries := stored.certificate.rangeEntries operation target
  let candidates := rowsForIndexEntries table entries
  have entriesEqual : entries = stored.expected.filter
      (fun entry => entry.matchesRange operation target) := by
    unfold entries
    exact stored.certificate.rangeEntries_exact operation target
  have candidatesEqual : candidates = table.rows.filter
      (Core.selects query.predicate) := by
    unfold candidates
    have expectedCurrent : stored.expected =
        CoreDecode.expectedIndexEntries table stored.index := by
      rw [stored.expected_eq]
      simp [CoreDecode.expectedIndexEntries, CoreFile.sortedIndexRows,
        CoreFile.indexValuesInteger, CoreFile.indexValuesText,
        rowsEqual]
    rw [entriesEqual, expectedCurrent, rowsForExpectedRange_exact]
    rw [predicateEqual, ← rowsEqual]
  have narrowed : Core.indexedCandidates stored.index query.predicate
      table.rows = some candidates := by
    rw [predicateEqual]
    simp only [Core.indexedCandidates, ↓reduceIte]
    rw [candidatesEqual, predicateEqual]
  ⟨candidates, Core.Query.eval_indexed stored.index query table.rows candidates
    narrowed⟩

def lookupCertifiedIndexCandidates (certificates : List StoredIntegerIndex)
    (table : Core.Table) (query : Core.Query) :
    Option (CertifiedCandidates table query) :=
  match predicateResult : query.predicate with
  | some (.equal column target) =>
      match table.chooseAccessPath query.predicate with
      | .equalityIndex index =>
          if columnEqual : column = index.column then
            match certificates.find? fun stored =>
                stored.table.schema.name == table.schema.name &&
                  stored.index.name == index.name with
            | none => none
            | some stored =>
                if indexEqual : stored.index = index then
                  if rowsEqual : stored.table.rows = table.rows then
                    have predicateEqual : query.predicate =
                        some (.equal stored.index.column target) := by
                      calc
                        query.predicate = some (.equal column target) :=
                          predicateResult
                        _ = some (.equal stored.index.column target) := by
                          simp [indexEqual, columnEqual]
                    some (certifiedEqualityCandidates stored table query target
                      rowsEqual predicateEqual)
                  else none
                else none
          else none
      | _ => none
  | some (.compare operation column target) =>
      match table.chooseAccessPath query.predicate with
      | .rangeIndex index =>
          if columnEqual : column = index.column then
            match certificates.find? fun stored =>
                stored.table.schema.name == table.schema.name &&
                  stored.index.name == index.name with
            | none => none
            | some stored =>
                if indexEqual : stored.index = index then
                  if rowsEqual : stored.table.rows = table.rows then
                    have predicateEqual : query.predicate =
                        some (.compare operation stored.index.column target) := by
                      calc
                        query.predicate =
                            some (.compare operation column target) :=
                          predicateResult
                        _ = some (.compare operation stored.index.column target) := by
                          simp [indexEqual, columnEqual]
                    some (certifiedRangeCandidates stored table query operation
                      target rowsEqual predicateEqual)
                  else none
                else none
          else none
      | _ => none
  | _ => none

/-- Use the persisted SQLite index B-tree for an equality query. The traversal
reads the catalog and only value-compatible index branches; returned rowids are
projected back into table order so queries without ORDER BY retain Core's
observable list semantics. Unsupported query shapes return `none`. -/
def lookupIndexCandidates (paths : Paths) (table : Core.Table)
    (query : Core.Query) : IO (Option IndexLookup) := do
  let selected := match query.predicate, table.chooseAccessPath query.predicate with
    | some (.equal column target), .equalityIndex index =>
        if column = index.column then
          some (index, IndexLookupTarget.equality target)
        else none
    | some (.compare operation column target), .rangeIndex index =>
        if column = index.column then
          some (index, IndexLookupTarget.range operation target)
        else none
    | _, _ => none
  let some (index, target) := selected | return none
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let some firstPage ← readPageBytes handle | return none
    let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
      return none
    let count := header.databaseSizePages.val
    unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
        header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
        metadata.byteSize.toNat = count * PhysicalCodec.pageSize do return none
    let some catalog := CoreDecode.decodeCatalog firstPage | return none
    let some entry := catalog.find? fun entry =>
      entry.kind == "index" && entry.name == index.name &&
        entry.table == table.schema.name | return none
    let reads ← IO.mkRef 0
    let base := preadPageSource paths.main count
    let source : CoreDecode.IOPageSource := {
      pageCount := count
      readPage := fun pageNumber => do
        reads.modify (· + 1)
        base.readPage pageNumber }
    let entries ← match target with
      | .equality value =>
          CoreDecode.lookupIndexValueIOFrom source value
            (count + 1) entry.rootPage
      | .range operation value =>
          CoreDecode.lookupIndexRangeIOFrom source operation value
            (count + 1) entry.rootPage
    let some entries := entries | return none
    let candidates := rowsForIndexEntries table entries
    return some ⟨candidates, ← reads.get⟩

/-- Cold secondary-index lookup for a stamped image emitted by the proved
encoder. The exact canonical catalog suffix records the INTEGER-only premise
of `lookupIndexValueFrom_encodeIndex_exact` and
`lookupIndexRangeFrom_encodeIndex_exact`. Only selected index branches and
the corresponding primary-tree paths are read; every returned rowid/value
link is checked locally before it reaches SQL evaluation. -/
def lookupGeneratedIndexCandidates (paths : Paths) (tableName : String)
    (schema : Core.Schema) (query : Core.Query) : IO (Option IndexLookup) := do
  let selected := match query.predicate with
    | some (.equal column target) =>
        some (column, IndexLookupTarget.equality target)
    | some (.compare operation column target) =>
        some (column, IndexLookupTarget.range operation target)
    | _ => none
  let some (column, target) := selected | return none
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
    let some indexEntry := catalog.find? (fun entry =>
      entry.kind == "index" && entry.table == tableName &&
        match entry.sql.bind CanonicalIndexSQL.parseGeneratedCertified with
        | some spec => spec.name == entry.name && spec.table == tableName &&
            spec.column == columnSpec.name
        | none => false) | return none
    let reads ← IO.mkRef 0
    let base := preadPageSource paths.main count
    let source : CoreDecode.IOPageSource := {
      pageCount := count
      readPage := fun pageNumber => do
        reads.modify (· + 1)
        base.readPage pageNumber }
    let entries ← match target with
      | .equality value =>
          CoreDecode.lookupIndexValueIOFrom source value
            (count + 1) indexEntry.rootPage
      | .range operation value =>
          CoreDecode.lookupIndexRangeIOFrom source operation value
            (count + 1) indexEntry.rootPage
    let some entries := entries | return none
    let mut candidates := []
    for entry in entries do
      let some resolved ← CoreDecode.lookupTableRowidIOFrom schema source
          entry.rowid (count + 1) tableEntry.rootPage | return none
      let some row := resolved | return none
      unless row.rowid = entry.rowid && row.WellFormed schema &&
          row.value column = entry.value do return none
      candidates := row :: candidates
    return some ⟨candidates.mergeSort rowidLe, ← reads.get⟩

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
    let some indexEntry := catalog.find? (fun entry =>
      entry.kind == "index" && entry.table == tableName &&
        match entry.sql.bind CanonicalIndexSQL.parseGeneratedCertified with
        | some spec => spec.name == entry.name && spec.table == tableName &&
            spec.column == columnSpec.name
        | none => false) | return none
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
  syncOps.syncFile paths.main
  syncOps.syncDeletion paths.main

/-- Roll back a leftover journal, without reading the database back.

`commit` needs only this side effect, so keeping the reopen inside `recover`
made every commit pay a whole extra read-and-decode whose result was discarded. -/
def recoverInPlace (syncOps : SyncOps) (paths : Paths) : IO Unit := do
  if ← paths.journalTemp.pathExists then
    SyscallVFS.unlinkPath paths.journalTemp.toString
    syncOps.syncDeletion paths.main
  if ← paths.journal.pathExists then
    let encoded ← IO.FS.readBinFile paths.journal
    let journal ← match PhysicalJournalCodec.decodeChecked encoded.data.toList with
      | some journal => pure journal
      | _ => throw (IO.userError "invalid general MVP rollback journal")
    let current ← IO.FS.readBinFile paths.main
    let currentPageCount := current.size / PhysicalCodec.pageSize
    unless current.size = currentPageCount * PhysicalCodec.pageSize do
      throw (IO.userError "misaligned general MVP main file during recovery")
    let recoveredMain ← match PhysicalJournalRecovery.decodeImage
        currentPageCount current.data.toList with
      | some image => pure image
      | none => throw (IO.userError "invalid paged general MVP main file during recovery")
    let restored := PhysicalJournalRecovery.recoverBytes recoveredMain (some journal)
    IO.FS.writeBinFile paths.main (bytes restored)
    syncOps.syncFile paths.main
    SyscallVFS.unlinkPath paths.journal.toString
    syncOps.syncDeletion paths.main

def recover (syncOps : SyncOps) (paths : Paths) : IO Core.Database := do
  recoverInPlace syncOps paths
  reopen paths

/-- Commit an already proved page delta.  Only the pages in `writes` are read
for journal pre-images, written, and read back.  No whole-file encode, diff, or
reopen occurs on this path.  The exact same write list feeds the journal and
the main-file protocol, preserving the hypotheses of the generic crash theorem. -/
def commitLocalized (syncOps : SyncOps) (paths : Paths)
    (expectedBefore writes :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (freePages : List Nat := []) :
    IO (Option (List (POSIXVFS.Request PhysicalCodec.pageSize))) := do
  recoverInPlace syncOps paths
  let writes ← addHeaderAndFreelistWrites paths.main freePages writes
  unless writes.Pairwise (fun left right => left.pageId ≠ right.pageId) do
    throw (IO.userError s!"localized delta contains duplicate page IDs: \
      {writes.map (fun write => write.pageId)}")
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
  IO.FS.writeBinFile paths.journalTemp
    (bytes (PhysicalJournalCodec.encodeChecked encodable))
  syncOps.syncFile paths.journalTemp
  SyscallVFS.renamePath paths.journalTemp.toString paths.journal.toString
  syncOps.syncDeletion paths.main
  writeMainPages paths.main writes
  syncOps.syncFile paths.main
  verifyWrittenPages paths.main writes
  SyscallVFS.unlinkPath paths.journal.toString
  syncOps.syncDeletion paths.main
  return some (preparedCommitPlan journal writes)

def commit (syncOps : SyncOps) (paths : Paths) (new : Core.Database) :
    IO (ValidatedOpenState × List (POSIXVFS.Request PhysicalCodec.pageSize)) := do
  recoverInPlace syncOps paths
  let current ← IO.FS.readBinFile paths.main
  let oldImage ← match physicalImage? current.data.toList with
    | some image => pure image
    | none => throw (IO.userError "could not page the current general MVP image")
  -- The bulk encoder has a compositional whole-image inverse. The exact write
  -- delta is read back below; the in-memory codec theorem and the on-disk
  -- read-back check establish distinct obligations without reparsing rows.
  let bulk ← match CorePageCodec.encodeBulkWithState new with
    | some result => pure result
    | none => throw (IO.userError "general MVP database exceeds the physical subset")
  let canonicalImage := bulk.1
  let (newImage, freePages) ←
    if oldImage.pageCount ≤ canonicalImage.pageCount then
      pure (canonicalImage, [])
    else
      match CoreMultiFreelist.ofImageTotal? canonicalImage oldImage.pageCount with
      | some layout =>
          pure (layout.paddedImage,
            List.range' (canonicalImage.pageCount + 1)
              (oldImage.pageCount - canonicalImage.pageCount))
      | none => throw (IO.userError "general MVP freelist exceeds the verified page-count bound")
  let writes := transactionWrites oldImage newImage
  let journal := GrowableStorage.makeJournal oldImage writes
  let encodable ← match PhysicalJournalCodec.ofJournal? journal with
    | some value => pure value
    | none => throw (IO.userError "general MVP rollback journal exceeds encoded bounds")
  IO.FS.writeBinFile paths.journalTemp
    (bytes (PhysicalJournalCodec.encodeChecked encodable))
  syncOps.syncFile paths.journalTemp
  SyscallVFS.renamePath paths.journalTemp.toString paths.journal.toString
  syncOps.syncDeletion paths.main
  writeMainPages paths.main writes
  syncOps.syncFile paths.main
  verifyWrittenPages paths.main writes
  SyscallVFS.unlinkPath paths.journal.toString
  syncOps.syncDeletion paths.main
  let validated ← match retainGeneratedState? bulk.2 newImage.pageCount freePages with
    | some value => pure value
    | none => throw (IO.userError
        "generated commit did not retain a proof-carrying state")
  return (validated, POSIXVFS.commitPlan oldImage writes)

end CoreFileAdapter
end SQLeanite
