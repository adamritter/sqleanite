import SQLeanite.CoreChunkPageDelta.UpdateStateFreePagesEqOfIndexed
import SQLeanite.CoreFileAdapter.AddLocalizedHeaderWriteBaseMem
import SQLeanite.CorePageLoad.RetargetOpenTablesWithoutIndexes
import SQLeanite.CoreSchemaRead
import SQLeanite.CoreWidePageLoad
import SQLeanite.Runtime.Record

namespace SQLeanite
namespace CoreFileAdapter

/-- Random-access source for routed reads. Database page numbers are one-based;
`pread` leaves no shared cursor and avoids reading every earlier page merely to
reach an index root allocated after a large table. -/
def preadPageSource (path : System.FilePath)
    (pageCount : Nat) : CoreDecode.IOPageSource := {
  pageCount
  readPage := fun pageNumber => do
    if pageNumber = 0 ∨ pageCount < pageNumber then return none
    let bytes ← SyscallVFS.preadBytes path.toString
      (UInt64.ofNat ((pageNumber - 1) * PhysicalCodec.pageSize))
      (USize.ofNat PhysicalCodec.pageSize)
    if bytes.size = PhysicalCodec.pageSize then return some bytes.toList
    else return none }

/-- A bounded batch-local cache for immutable routed reads.  It stores the
exact page bytes returned by `preadPageSource`; decoder results and proof
certificates are unchanged.  The bound prevents a long random-read workload
from retaining one linked-list page per lookup. -/
structure PageReadCache where
  pages : IO.Ref (Std.HashMap Nat ByteArray)
  decodedIndexPages : IO.Ref (Std.HashMap Nat CoreDecode.DecodedIndexPage)
  capacity : Nat
  tableCursors : IO.Ref (Std.HashMap Nat Runtime.TableCursor.Cursor)
  tableViews : IO.Ref (Std.HashMap Nat Runtime.TablePage.View)

def PageReadCache.create (capacity : Nat := 512) : BaseIO PageReadCache := do
  return {
    pages := ← IO.mkRef (Std.HashMap.emptyWithCapacity capacity)
    decodedIndexPages := ← IO.mkRef (Std.HashMap.emptyWithCapacity capacity)
    capacity
    tableCursors := ← IO.mkRef (Std.HashMap.emptyWithCapacity capacity)
    tableViews := ← IO.mkRef (Std.HashMap.emptyWithCapacity capacity) }

private def readPager (path : System.FilePath) (pageCount : Nat)
    (cache : PageReadCache) : Runtime.ReadPager.Pager :=
  Runtime.ReadPager.ofPath path pageCount PhysicalCodec.pageSize
    cache.pages cache.capacity

def preadPageSourceCached (path : System.FilePath)
    (pageCount : Nat) (cache : PageReadCache) : CoreDecode.IOPageSource := {
  pageCount
  readPage := fun page => do
    return (← (readPager path pageCount cache).get page).map ByteArray.toList }

/-- Compatibility adapter: the pager owns bytes, the table cursor locates a
cell, and the record layer decodes its payload. Existing generated-index and
primary-key readers share the same bounded transaction-local resources. -/
def lookupTableRowidBytesCached (path : System.FilePath)
    (schema : Core.Schema) (source : CoreDecode.IOPageSource)
    (cache : PageReadCache) (target : Core.Integer)
    (fuel pageNumber : Nat) : IO (Option (Option Core.Row)) := do
  let cursors ← cache.tableCursors.get
  let cursor ← match cursors.get? pageNumber with
    | some cursor => pure cursor
    | none => do
        let cursor ← Runtime.TableCursor.create
          (readPager path source.pageCount cache) pageNumber (some cache.tableViews)
        if cursors.size < cache.capacity then
          cache.tableCursors.set (cursors.insert pageNumber cursor)
        pure cursor
  let some located ← cursor.seek target fuel | return none
  match located with
  | none => return some none
  | some cell =>
      let some row ← Runtime.Record.readRowWithSource schema source cell |
        return none
      return some (some row)

def decodedIndexPageCached (cache : PageReadCache)
    (source : CoreDecode.IOPageSource) (pageNumber : Nat) :
    IO (Option CoreDecode.DecodedIndexPage) := do
  let pages ← cache.decodedIndexPages.get
  match pages.get? pageNumber with
  | some page => return some page
  | none =>
      let decoded ← CoreDecode.decodeIndexPageIOFrom source pageNumber
      match decoded with
      | some page =>
          if pages.size < cache.capacity then
            cache.decodedIndexPages.set (pages.insert pageNumber page)
          return some page
      | none => return none

/-- The physical page size includes an optional reserved tail. B-tree cells
and overflow payloads use only the remaining, at least 480, usable bytes. -/
def headerUsablePageSize? (header : FileFormat.DatabaseHeader) :
    Option FileFormat.UsablePageSize := do
  let pageSize := header.headerPrefix.pageSize
  if valid : FileFormat.ValidSQLitePageSize pageSize then
    if minimum : 480 ≤ pageSize - header.headerPrefix.reservedSpace.toNat then
      some {
        val := pageSize - header.headerPrefix.reservedSpace.toNat
        atLeastMinimum := minimum
        atMostMaximum := by
          simp [FileFormat.ValidSQLitePageSize] at valid
          omega }
    else none
  else none

theorem headerUsablePageSize?_val {header : FileFormat.DatabaseHeader}
    {usable : FileFormat.UsablePageSize}
    (decoded : headerUsablePageSize? header = some usable) :
    usable.val = header.headerPrefix.pageSize - header.headerPrefix.reservedSpace.toNat := by
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

/-- Every admitted page partitions exactly into payload geometry and its
reserved tail; natural-number subtraction cannot conceal an oversized tail. -/
theorem headerUsablePageSize?_partition {header : FileFormat.DatabaseHeader}
    {usable : FileFormat.UsablePageSize}
    (decoded : headerUsablePageSize? header = some usable) :
    usable.val + header.headerPrefix.reservedSpace.toNat = header.headerPrefix.pageSize := by
  have geometry := headerUsablePageSize?_val decoded
  have minimum := usable.atLeastMinimum
  omega

def generatedImageStamp (paths : Paths) : IO Bool := do
  let bytes ← SyscallVFS.preadBytes paths.main.toString 0 100
  if bytes.size = 100 then
    match FileFormat.decodeDatabaseHeader bytes.toList with
    | some (header, _) => return CoreFile.hasGeneratedImageStamp header
    | none => return false
  else return false

/-- A bounded direct page source over the file buffer. Converting the entire
database to a linked list and then splitting it into page lists made a validated
write-open traverse every byte before decoding began. -/
def byteArrayPageSource (input : ByteArray) (pageCount : Nat) :
    CoreDecode.PageSource := {
  pageCount
  readPage := fun pageNumber =>
    if pageNumber = 0 || pageCount < pageNumber then none
    else
      let start := (pageNumber - 1) * PhysicalCodec.pageSize
      let stop := start + PhysicalCodec.pageSize
      if stop ≤ input.size then some (input.extract start stop).data.toList
      else none }

def reopenWithMetadata (paths : Paths)
    (origins : Option (IO.Ref (List SQLite.StoredText)) := none) :
    IO (Core.Database × CoreMultiFreelist.HeaderMetadata) := do
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let headerBytes ← handle.read 100
    if metadata.byteSize.toNat ≤ 1 && headerBytes.size == metadata.byteSize.toNat then
      return (Core.Database.empty, {})
    unless headerBytes.size = 100 do
      throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")
    let (header, _) ← match FileFormat.decodeDatabaseHeader headerBytes.toList with
      | some decoded => pure decoded
      | none => throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")
    if let some message := SQLite.HeaderVersion.readError? header then
      throw (IO.userError message)
    let usable ← match headerUsablePageSize? header with
      | some usable => pure usable
      | none => throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")
    let some count := SQLite.DatabaseSize.pageCount? header metadata.byteSize.toNat header.headerPrefix.pageSize |
      throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")
    unless SQLite.TextEncoding.supported header.textEncoding.val do
      throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")
    handle.rewind
    -- Read the file once and slice pages out of the buffer rather than issuing a
    -- read per page. The streaming source cost one syscall per page, which
    -- dominated the general open: at 11 MB this step alone was 3.4 s and is now
    -- about 1.3 s. The page size comes from the validated header, not from
    -- `PhysicalCodec.pageSize`, so files written with a non-default page size
    -- still decode -- using the fixed-size `byteArrayPageSource` here silently
    -- broke the 1024-byte differential case.
    let whole ← IO.FS.readBinFile paths.main
    let pageBytes := header.headerPrefix.pageSize
    let source : CoreDecode.IOPageSource := {
      -- `usable` is defaulted on `IOPageSource`, and omitting it here is what
      -- broke the 1024-byte differential case: the slices were the header's page
      -- size while the decoder's cell and overflow thresholds stayed at 4096, so
      -- every page parsed as garbage and the open reported a corrupt image.
      usable
      textEncoding := header.textEncoding.val
      observeRow := if header.textEncoding.val == 2 || header.textEncoding.val == 3 then
        origins.map fun reference => fun schema row fields =>
          reference.modify (fun previous => CoreTextEncoding.origins header.textEncoding.val schema row fields ++ previous)
        else none
      pageCount := count
      readPage := fun pageNumber => pure <|
        if pageNumber = 0 || count < pageNumber then none
        else
          (SQLite.DatabaseSize.pageBytes whole pageBytes pageNumber).map (List.take usable.val) }
    match ← CoreDecode.decodeFromIOPageSource source with
    | some database => return (database, CoreMultiFreelist.HeaderMetadata.fromHeader header)
    | none => throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")

/-- Read catalog records through their physical rowids, not synthesized schema
rows. This also handles a catalog interior tree and overflow declarations. -/
def readSchemaRows (paths : Paths) : IO (List Core.Row) := do
  let header ← readHeader paths.main
  let whole ← IO.FS.readBinFile paths.main
  if whole.size ≤ 1 then return []
  let some usable := headerUsablePageSize? header | throw (IO.userError "invalid catalog geometry")
  let pageSize := header.headerPrefix.pageSize
  let some count := SQLite.DatabaseSize.pageCount? header whole.size pageSize
    | throw (IO.userError "invalid catalog page count")
  let source : CoreDecode.IOPageSource := {
    usable
    textEncoding := header.textEncoding.val
    pageCount := count
    readPage := fun page => pure ((SQLite.DatabaseSize.pageBytes whole pageSize page).map (List.take usable.val)) }
  let some rows ← CoreSchemaRead.rows source | throw (IO.userError "invalid schema records")
  return rows

def reopen (paths : Paths) : IO Core.Database := do
  return (← reopenWithMetadata paths).1

/-- Recover the proof-carrying 2-3-tree view only when the bytes actually have
that shape and its abstraction is exactly the already-decoded database. -/
def loadPageState (paths : Paths) (database : Core.Database) :
    IO (Option CoreChunkPageState.State) := do
  let input ← IO.FS.readBinFile paths.main
  -- Page-wise, for the reason given on `byteArrayPageSource`: materializing the
  -- whole database as a list here costs one cons cell per byte on every open
  -- that falls back to the general decoder.
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let some (header, _) := FileFormat.decodeDatabaseHeader firstPageBytes |
    return none
  let count := header.databaseSizePages.val
  unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
      header.headerPrefix.reservedSpace = 0 && input.size = count * PhysicalCodec.pageSize do return none
  return CorePageLoad.load? (byteArrayPageSource input count) database

def loadWidePageState (paths : Paths) (database : Core.Database) :
    IO (Option (ValidatedWideState database)) := do
  let input ← IO.FS.readBinFile paths.main
  -- Only page zero becomes a list, and `byteArrayPageSource` materializes each
  -- later page on demand. Converting the whole buffer with `input.data.toList`
  -- and splitting it with `CoreDecode.pages` allocated one cons cell per byte of
  -- the database on every write open: at 11 MB that is eleven million cells, and
  -- it made opening a database for writing cost about 490 ms/MB while opening for
  -- reading stayed flat at 11 ms. `loadOpenState` already reads this way.
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let some (header, _) := FileFormat.decodeDatabaseHeader firstPageBytes |
    return none
  let count := header.databaseSizePages.val
  unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
      header.headerPrefix.reservedSpace = 0 && input.size = count * PhysicalCodec.pageSize do return none
  let source := byteArrayPageSource input count
  match loaded : CoreWidePageLoad.load? source database with
  | none => return none
  | some state => return some ⟨state, CoreWidePageLoad.load?_represents loaded⟩

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
  rcases Option.bind_eq_some_iff.mp generated with ⟨built, builtResult, generated⟩
  exact (retainGeneratedState?_state generated).trans
    (CoreChunkPageState.State.build?_represents builtResult).1

theorem generatedOpenState?_allocationWellFormed
    {database : Core.Database} {pageCount : Nat} {freePages : List Nat}
    {validated : ValidatedOpenState}
    (generated : generatedOpenState? database pageCount freePages =
      some validated) :
    validated.state.AllocationWellFormed := by
  unfold generatedOpenState? at generated
  rcases Option.bind_eq_some_iff.mp generated with ⟨built, builtResult, generated⟩
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

/-- Exact pure preparation for the ordinary localized writer.  The executable
engine used to unpack `beforeWrites` and `writes` independently after a
Boolean sufficiency check.  Keeping their defining equations, allocation,
distinctness, and physical-index preservation mode in one dependent object
makes the value consumed by the syscall path the same value consumed by the
durability proof.

The final disjunction is deliberate.  An indexed changed table preserves the
existing physical index runs; a wholly indexless database has no such runs.
A growing indexless table beside another table's physical index is routed to
the bulk path because it does not preserve `TablePagesBeforeIndexRoots`. -/
structure PreparedOrdinaryDelta
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta) where
  expectedBefore : List
    (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  updated : CoreChunkPageDelta.updateState? state database = some delta
  expectedBeforeEq : CoreChunkPageDelta.beforeWrites delta.table =
    some expectedBefore
  writesEq : CoreChunkPageDelta.writes delta.table = some writes
  distinct : writes.Pairwise (fun left right => left.pageId ≠ right.pageId)
  allocation : state.AllocationWellFormed
  preservationMode : delta.table.before.table.indexes ≠ [] ∨
    ∀ table ∈ database.tables, table.indexes = []

/-- Certify the already-computed candidate selected by the live engine.  No
table delta is recomputed: the proof that `updateState?` chose this candidate
is derived from the same `candidate` and `sufficient` branch equations. -/
def prepareOrdinaryDelta?
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (candidate : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (sufficient : delta.table.tablePagesSufficient = true) :
    Option (PreparedOrdinaryDelta state database delta) :=
  let updated : CoreChunkPageDelta.updateState? state database = some delta := by
    simp [CoreChunkPageDelta.updateState?, candidate, sufficient]
  match beforeResult : CoreChunkPageDelta.beforeWrites delta.table with
  | none => none
  | some expectedBefore =>
      match writesResult : CoreChunkPageDelta.writes delta.table with
      | none => none
      | some writes =>
          if distinct : writes.Pairwise
              (fun left right => left.pageId ≠ right.pageId) then
            if allocation : state.AllocationWellFormed then
              if preservationMode : delta.table.before.table.indexes ≠ [] ∨
                  ∀ table ∈ database.tables, table.indexes = [] then
                some {
                  expectedBefore
                  writes
                  updated
                  expectedBeforeEq := beforeResult
                  writesEq := writesResult
                  distinct
                  allocation
                  preservationMode }
              else none
            else none
          else none

theorem prepareOrdinaryDelta?_updated
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    {candidate : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta}
    {sufficient : delta.table.tablePagesSufficient = true}
    {prepared : PreparedOrdinaryDelta state database delta}
    (_success : prepareOrdinaryDelta? state database delta candidate sufficient =
      some prepared) :
    CoreChunkPageDelta.updateState? state database = some delta := by
  exact prepared.updated

/-- The growable-storage image denoted by one exact in-memory file buffer.
Unlike `physicalImage?`, this representation keeps positional reads over the
array and therefore does not materialize a list of every page. -/
def byteArrayStorageImage (input : ByteArray) (pageCount : Nat)
    (exactSize : input.size = pageCount * PhysicalCodec.pageSize) :
    GrowableStorage.Image PhysicalCodec.pageSize := {
  pageCount
  read := fun pageId =>
    if bound : pageId < pageCount then
      let start := pageId * PhysicalCodec.pageSize
      let stop := start + PhysicalCodec.pageSize
      {
        bytes := (input.extract start stop).data
        sizeInvariant := by
          have stopBound : stop ≤ pageCount * PhysicalCodec.pageSize := by
            have countBound : pageId + 1 ≤ pageCount := by omega
            have scaled := Nat.mul_le_mul_right PhysicalCodec.pageSize countBound
            simpa [stop, start, Nat.add_mul] using scaled
          have inputSize : input.data.size =
              pageCount * PhysicalCodec.pageSize := by
            exact exactSize
          have pageSize : (input.data.extract start stop).size =
              PhysicalCodec.pageSize := by
            rw [Array.size_extract, inputSize, Nat.min_eq_left stopBound]
            simp only [stop, start, Nat.add_sub_cancel_left]
          change (input.extract start stop).data.size =
            PhysicalCodec.pageSize
          simpa only [ByteArray.data_extract] using pageSize }
    else Storage.Page.zero PhysicalCodec.pageSize }

end CoreFileAdapter

end SQLeanite
