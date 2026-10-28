import SQLeanite.CoreMultiFreelist
import SQLeanite.CorePageCodec.EncodeBulkFromState
import SQLeanite.CoreWidePageCodec
import SQLeanite.PhysicalFileAdapter
import SQLeanite.SQLite.DatabaseSize
import SQLeanite.SQLite.HeaderVersion

namespace SQLeanite
namespace CoreFileAdapter

abbrev Paths := PhysicalFileAdapter.Paths

abbrev SyncOps := PhysicalFileAdapter.SyncOps

abbrev Request := GrowableStorage.VFSRequest PhysicalCodec.pageSize

/-- A zero text-encoding cookie leaves SQLite's new connection at its default
UTF-8 encoding (prepare.c:sqlite3InitOne). It occurs naturally in persisted
empty schemas and is also readable in populated UTF-8 files. UTF-16 still
requires a separate record/comparison implementation. -/
def utf8TextEncoding (encoding : Nat) : Bool := encoding == 0 || encoding == 1

theorem utf8TextEncoding_zero : utf8TextEncoding 0 = true := by decide

theorem utf8TextEncoding_iff (encoding : Nat) :
    utf8TextEncoding encoding = true ↔ encoding = 0 ∨ encoding = 1 := by
  simp [utf8TextEncoding]

/-- In-memory defaults for an existing zero-byte database. Opening it does
not materialize a page or attach generated-image provenance. -/
def emptyDatabaseHeader : FileFormat.DatabaseHeader := {
  PhysicalCodec.databaseHeader with
  headerPrefix := { PhysicalCodec.databaseHeader.headerPrefix with changeCounter := ⟨0, by decide⟩ }
  databaseSizePages := ⟨0, by decide⟩
  schemaCookie := ⟨0, by decide⟩
  schemaFormat := ⟨0, by decide⟩
  textEncoding := ⟨0, by decide⟩
  versionValidFor := ⟨0, by decide⟩ }

def headerOrEmpty (bytes : List UInt8) (fileSize : Nat) : Option FileFormat.DatabaseHeader :=
  -- unixFileSize reports one-byte files as empty (SQLite ticket #3260).
  if bytes.length == fileSize && fileSize ≤ 1 then some emptyDatabaseHeader
  else (FileFormat.decodeDatabaseHeader bytes).map Prod.fst

theorem headerOrEmpty_empty : headerOrEmpty [] 0 = some emptyDatabaseHeader := rfl

theorem headerOrEmpty_singleton (byte : UInt8) :
    headerOrEmpty [byte] 1 = some emptyDatabaseHeader := rfl

theorem headerOrEmpty_short_nonempty (size : Nat) (nonzero : size ≠ 0) :
    headerOrEmpty [] size = none := by
  have emptyDecode : FileFormat.decodeDatabaseHeader [] = none := rfl
  simp [headerOrEmpty, Ne.symm nonzero, emptyDecode]

/-- Read the actual file header before entering an optimized path. -/
def readHeader (path : System.FilePath) : IO FileFormat.DatabaseHeader := do
  let bytes ← SyscallVFS.preadBytes path.toString 0 100
  let some header := headerOrEmpty bytes.toList (← path.metadata).byteSize.toNat |
    throw (IO.userError "file is not a database")
  return header

def requireReadable (path : System.FilePath) : IO Unit := do
  if let some message := SQLite.HeaderVersion.readError? (← readHeader path) then
    throw (IO.userError message)

/-- Opening an existing database read/write preserves its bytes. Check actual
OS access before a mutating statement: atomic replacement alone could otherwise
replace a read-only file in a writable directory. -/
def requireWritableAccess (path : System.FilePath) : IO Unit := do
  if ← path.pathExists then
    try
      IO.FS.withFile path .readWrite fun _ => pure ()
    catch _ => throw (IO.userError "attempt to write a readonly database")

def requireWritableFormat (path : System.FilePath) : IO Unit := do
  let header ← readHeader path
  if let some message := SQLite.HeaderVersion.writeError? header then
    throw (IO.userError message)
  unless utf8TextEncoding header.textEncoding.val do
    throw (IO.userError "unsupported UTF-16 database writes")

def storageImage (image : CoreFile.Image) :
    GrowableStorage.Image PhysicalCodec.pageSize :=
  let pages := image.pages.toArray
  {
  pageCount := pages.size
  read := fun pageId =>
    (pages[pageId]?).map CoreFile.Page.storage |>.getD
      (Storage.Page.zero PhysicalCodec.pageSize) }

def transactionWrites (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (image : CoreFile.Image) :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize) :=
  GrowableStorage.deltaWrites old (storageImage image)

/-- The two byte-image forms selected by the live bulk writer.  This is a
lower-layer, proof-carrying description of the choice; `CoreDurability` turns
it into the corresponding `PostImageCertificate` without creating an import
cycle back into the file adapter. -/
inductive PreparedBulkImage (canonical : CoreFile.Image) :
    CoreFile.Image → Prop where
  | canonical : PreparedBulkImage canonical canonical
  | padded (layout : CoreMultiFreelist.Layout)
      (sameImage : layout.image = canonical) :
      PreparedBulkImage canonical layout.paddedImage

/-- Pure preparation consumed by the actual bulk commit.  It retains the
encoder equation, exact selected image, non-shrinking allocation fact, and
exact delta-write equation as erased fields. -/
structure PreparedBulkCommit
    (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (database : Core.Database) where
  state : CoreChunkPageState.State
  canonicalImage : CoreFile.Image
  newImage : CoreFile.Image
  freePages : List Nat
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  encodedWithState : CorePageCodec.encodeBulkWithState database =
    some (canonicalImage, state)
  choice : PreparedBulkImage canonicalImage newImage
  doesNotShrink : old.pageCount ≤ (storageImage newImage).pageCount
  writesEq : writes = transactionWrites old newImage

/-- Decide the exact bulk image and page delta before performing any syscall.
The returned object is both the executable input to `commit` and the erased
proof input to the durability layer. -/
def headerMetadata? (image : GrowableStorage.Image PhysicalCodec.pageSize) :
    Option CoreMultiFreelist.HeaderMetadata :=
  if image.pageCount == 0 then some {}
  else CoreMultiFreelist.HeaderMetadata.decode? (image.read 0).bytes.toList

def prepareBulkCommit? (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (database : Core.Database) (previousMetadata : Option CoreMultiFreelist.HeaderMetadata := none) :
    Option (PreparedBulkCommit old database) := do
  let metadata ← previousMetadata.orElse (fun _ => headerMetadata? old)
  match encoded : CorePageCodec.encodeBulkWithState database with
  | none => none
  | some (canonicalImage, state) =>
      if grows : old.pageCount ≤ canonicalImage.pageCount ∧ metadata = {} then
        let writes := transactionWrites old canonicalImage
        some {
          state
          canonicalImage
          newImage := canonicalImage
          freePages := []
          writes
          encodedWithState := encoded
          choice := .canonical
          doesNotShrink := by
            simpa [storageImage, CoreFile.Image.pageCount] using grows.1
          writesEq := rfl }
      else
        match layoutResult : CoreMultiFreelist.ofImageTotal? canonicalImage
            (max old.pageCount canonicalImage.pageCount) with
        | none => none
        | some baseLayout =>
            let layout := { baseLayout with metadata }
            let writes := transactionWrites old layout.paddedImage
            some {
              state
              canonicalImage
              newImage := layout.paddedImage
              freePages := List.range' (canonicalImage.pageCount + 1)
                (old.pageCount - canonicalImage.pageCount)
              writes
              encodedWithState := encoded
              choice := .padded layout (by
                change baseLayout.image = canonicalImage
                exact CoreMultiFreelist.ofImageTotal?_image layoutResult)
              doesNotShrink := by
                change old.pageCount ≤ layout.paddedImage.pageCount
                rw [CoreMultiFreelist.Layout.paddedImage_pageCount]
                change old.pageCount ≤ baseLayout.totalPageCount
                rw [CoreMultiFreelist.ofImageTotal?_totalPageCount layoutResult]
                exact Nat.le_max_left _ _
              writesEq := rfl }

/-- Growing bulk commits for the high-fanout representation.  Shrinking keeps
using the established freelist-aware path until the wide state owns freelist
metadata as well. -/
structure PreparedWideBulkCommit
    (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (database : Core.Database) where
  state : CoreWidePageState.State
  image : CoreFile.Image
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  encodedWithState : CoreWidePageCodec.encodeBulkInlineWithState database =
    some (image, state)
  doesNotShrink : old.pageCount ≤ (storageImage image).pageCount
  writesEq : writes = transactionWrites old image

structure ValidatedWideState (database : Core.Database) where
  state : CoreWidePageState.State
  represents : state.Represents database

def prepareWideBulkCommit?
    (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (database : Core.Database) : Option (PreparedWideBulkCommit old database) := do
  let metadata ← headerMetadata? old
  unless metadata == {} do none
  match encoded : CoreWidePageCodec.encodeBulkInlineWithState database with
  | none => none
  | some (image, state) =>
      if grows : old.pageCount ≤ image.pageCount then
        some {
          state
          image
          writes := transactionWrites old image
          encodedWithState := encoded
          doesNotShrink := by
            simpa [storageImage, CoreFile.Image.pageCount] using grows
          writesEq := rfl }
      else none

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

def bytes (values : List UInt8) : ByteArray :=
  ByteArray.mk values.toArray

def physicalImage? (input : List UInt8) :
    Option (GrowableStorage.Image PhysicalCodec.pageSize) := do
  if input.length ≤ 1 then return {
    pageCount := 0, read := fun _ => Storage.Page.zero PhysicalCodec.pageSize }
  let (header, _) ← FileFormat.decodeDatabaseHeader input
  if _pageSize : header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize then
    let count ← SQLite.DatabaseSize.pageCount? header input.length PhysicalCodec.pageSize
    let needed := count * PhysicalCodec.pageSize
    let normalized := input.take needed ++ List.replicate (needed - input.length) 0
    let (decoded, suffix) ← DiskFormat.decodeSizedPages PhysicalCodec.pageSize count normalized
    if _consumed : suffix = [] then
      let pages := decoded.pages.toArray
      some {
        pageCount := count
        read := fun pageId => pages[pageId]?.getD
          (Storage.Page.zero PhysicalCodec.pageSize) }
    else none
  else none

/-- Read exactly one SQLite page. Regular-file short reads are rejected rather
than silently zero-filled. -/
def readPageBytesOf (handle : IO.FS.Handle) (pageSize : Nat) :
    IO (Option (List UInt8)) := do
  let chunk ← handle.read (USize.ofNat pageSize)
  if chunk.size = pageSize then
    return some chunk.toList
  else return none

def readPageBytes (handle : IO.FS.Handle) : IO (Option (List UInt8)) :=
  readPageBytesOf handle PhysicalCodec.pageSize

def skipPagesOf (handle : IO.FS.Handle) (pageSize : Nat) : Nat → IO Bool
  | 0 => pure true
  | count + 1 => do
      let some _ ← readPageBytesOf handle pageSize | return false
      skipPagesOf handle pageSize count

private def skipPages (handle : IO.FS.Handle) : Nat → IO Bool :=
  skipPagesOf handle PhysicalCodec.pageSize

def pageTransfer
    (write : GrowableStorage.PageWrite PhysicalCodec.pageSize) :
    SyscallVFS.PageTransfer := {
  bytes := ByteArray.mk write.page.bytes
  offset := UInt64.ofNat (write.pageId * PhysicalCodec.pageSize) }

def pageTransfers
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    Array SyscallVFS.PageTransfer :=
  writes.toArray.map pageTransfer

theorem pageTransfers_toList
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    (pageTransfers writes).toList = writes.map pageTransfer := by
  simp [pageTransfers]

/-- Publish exactly the pages represented by the verified transaction. The C
boundary performs only positional writes; ordering and page bytes stay Lean. -/
def writeMainPages (path : System.FilePath)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : IO Unit := do
  SyscallVFS.pwritePages path.toString (pageTransfers writes)

/-- The recurrent syscall trace used when page pre-images have already been
read from the concrete file.  The journal inode is initialized once, outside
the transaction; each commit changes only its contents.  The separate journal
argument makes the concrete read boundary explicit. -/
def preparedCommitPlan
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    List (POSIXVFS.Request PhysicalCodec.pageSize) :=
  [.writePersistentJournal (some journal), .fdatasyncPersistentJournal] ++
    writes.map POSIXVFS.Request.pwriteMain ++
      [.fdatasyncMain, .writePersistentJournal none,
        .fdatasyncPersistentJournal]

theorem preparedCommitPlan_eq_persistentCommitPlan
    (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    preparedCommitPlan (GrowableStorage.makeJournal old writes) writes =
      POSIXVFS.persistentCommitPlan old writes := rfl

def readPageCount (handle : IO.FS.Handle)
    (path : System.FilePath) : IO Nat := do
  handle.rewind
  let some firstPage ← readPageBytes handle |
    throw (IO.userError s!"invalid general MVP SQLite image: {path}")
  let (header, _) ← match FileFormat.decodeDatabaseHeader firstPage with
    | some decoded => pure decoded
    | none => throw (IO.userError s!"invalid general MVP SQLite image: {path}")
  let metadata ← path.metadata
  let some count := SQLite.DatabaseSize.pageCount? header metadata.byteSize.toNat PhysicalCodec.pageSize |
    throw (IO.userError s!"invalid general MVP SQLite image: {path}")
  unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize do
    throw (IO.userError s!"invalid general MVP SQLite image: {path}")
  return count

def targetPageCount (current : Nat)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : Nat :=
  writes.foldl (fun count write => max count (write.pageId + 1)) current

theorem targetPageCount_eq_of_forall_lt (current : Nat) :
    ∀ writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize),
      (∀ write ∈ writes, write.pageId < current) →
      targetPageCount current writes = current
  | [], _ => rfl
  | head :: tail, bounded => by
      unfold targetPageCount
      simp only [List.foldl_cons]
      have headBound := bounded head (by simp)
      have first : max current (head.pageId + 1) = current := by omega
      rw [first]
      exact targetPageCount_eq_of_forall_lt current tail
        (by intro write member; exact bounded write (by simp [member]))

/-- Add the one-trunk SQLite freelist image without removing any logical page
write. Bounds on the trunk and leaves are checked by the enclosing planner. -/
def addFreelistWrite? (freePages : List Nat)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :=
  match freePages with
  | [] => some writes
  | trunk :: leaves => do
      let trunkPrefix := FileFormat.encodeUnsignedFixed 4 0 ++
        FileFormat.encodeUnsignedFixed 4 leaves.length ++
          CoreFreelist.encodePageNumbers leaves
      if _fits : trunkPrefix.length ≤ PhysicalCodec.pageSize then
        let trunkBytes := trunkPrefix ++
          List.replicate (PhysicalCodec.pageSize - trunkPrefix.length) 0
        let (trunkPage, trunkRest) ←
          DiskFormat.decodeStoragePage PhysicalCodec.pageSize trunkBytes
        if _trunkExact : trunkRest = [] then
          some (⟨trunk - 1, trunkPage⟩ :: writes)
        else none
      else none

/-- Add page zero exactly when neither the base delta nor an identical current
header already supplies it. -/
def addLocalizedHeaderWrite (firstPage : List UInt8)
    (headerPage : Storage.Page PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize) :=
  if writes.any (fun write => write.pageId = 0) then writes
  else if headerPage.bytes.toList == firstPage then writes
  else ⟨0, headerPage⟩ :: writes

/-- Pure header/freelist augmentation for a localized delta.  Keeping this
planner outside `IO` is important: the exact list returned here is retained in
`PreparedLocalizedWrites` and is also the exact list journaled and written by
the live commit protocol. -/
def planLocalizedWrites? (current : Nat) (firstPage : List UInt8)
    (freePages : List Nat)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) := do
  let target := targetPageCount current writes
  if bounds : target < 2 ^ 32 ∧ freePages.length < 2 ^ 32 ∧
      freePages.Nodup ∧
      ∀ page ∈ freePages, 1 < page ∧ page ≤ target ∧ page < 2 ^ 32 then
    let (header, suffix) ← FileFormat.decodeDatabaseHeader firstPage
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
    let (headerPage, headerRest) ←
      DiskFormat.decodeStoragePage PhysicalCodec.pageSize patched
    if _headerExact : headerRest = [] then
      let writes ← addFreelistWrite? freePages writes
      some (addLocalizedHeaderWrite firstPage headerPage writes)
    else none
  else none

/-- Freelist augmentation only prepends its trunk; it never drops or replaces
a logical table/index write. -/
theorem addFreelistWrite?_base_mem
    {freePages : List Nat}
    {writes finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (success : addFreelistWrite? freePages writes = some finalWrites) :
    ∀ write ∈ writes, write ∈ finalWrites := by
  intro write member
  cases freePages with
  | nil =>
      simp only [addFreelistWrite?, Option.some.injEq] at success
      subst finalWrites
      exact member
  | cons trunk leaves =>
      simp only [addFreelistWrite?] at success
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨trunkAndRest, decoded, success⟩
        rcases trunkAndRest with ⟨trunkPage, trunkRest⟩
        split at success
        next =>
          injection success with equal
          subst finalWrites
          exact List.mem_cons_of_mem _ member
        next => contradiction
      next => contradiction

end CoreFileAdapter

end SQLeanite
