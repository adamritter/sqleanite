import SQLeanite.CoreDecode
import SQLeanite.CoreFreelist
import SQLeanite.CoreMultiFreelist
import SQLeanite.CoreOverflow
import SQLeanite.CoreChunkPageDelta
import SQLeanite.CorePageLoad
import SQLeanite.CorePageSource
import SQLeanite.CoreLocalizedRepresentation
import SQLeanite.CoreWidePageInverse
import SQLeanite.CoreWidePageLoad
import SQLeanite.CoreWidePageDelta
import SQLeanite.PhysicalFileAdapter
import SQLeanite.Runtime.Record

namespace SQLeanite
namespace CoreFileAdapter

abbrev Paths := PhysicalFileAdapter.Paths
abbrev SyncOps := PhysicalFileAdapter.SyncOps
abbrev Request := GrowableStorage.VFSRequest PhysicalCodec.pageSize

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
def prepareBulkCommit? (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (database : Core.Database) : Option (PreparedBulkCommit old database) :=
  match encoded : CorePageCodec.encodeBulkWithState database with
  | none => none
  | some (canonicalImage, state) =>
      if grows : old.pageCount ≤ canonicalImage.pageCount then
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
            simpa [storageImage, CoreFile.Image.pageCount] using grows
          writesEq := rfl }
      else
        match layoutResult : CoreMultiFreelist.ofImageTotal? canonicalImage
            old.pageCount with
        | none => none
        | some layout =>
            let writes := transactionWrites old layout.paddedImage
            some {
              state
              canonicalImage
              newImage := layout.paddedImage
              freePages := List.range' (canonicalImage.pageCount + 1)
                (old.pageCount - canonicalImage.pageCount)
              writes
              encodedWithState := encoded
              choice := .padded layout
                (CoreMultiFreelist.ofImageTotal?_image layoutResult)
              doesNotShrink := by
                change old.pageCount ≤ layout.paddedImage.pageCount
                rw [CoreMultiFreelist.Layout.paddedImage_pageCount,
                  CoreMultiFreelist.ofImageTotal?_totalPageCount layoutResult]
                exact Nat.le_refl _
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
    (database : Core.Database) : Option (PreparedWideBulkCommit old database) :=
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

private def bytes (values : List UInt8) : ByteArray :=
  ByteArray.mk values.toArray

def physicalImage? (input : List UInt8) :
    Option (GrowableStorage.Image PhysicalCodec.pageSize) := do
  let (header, _) ← FileFormat.decodeDatabaseHeader input
  if _pageSize : header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize then
    let count := header.databaseSizePages.val
    let (decoded, suffix) ← DiskFormat.decodeSizedPages PhysicalCodec.pageSize count input
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
private def writeMainPages (path : System.FilePath)
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

private theorem targetPageCount_eq_of_forall_lt (current : Nat) :
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

theorem addLocalizedHeaderWrite_base_mem
    (firstPage : List UInt8)
    (headerPage : Storage.Page PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    ∀ write ∈ writes,
      write ∈ addLocalizedHeaderWrite firstPage headerPage writes := by
  intro write member
  unfold addLocalizedHeaderWrite
  split
  next => exact member
  next =>
    split
    next => exact member
    next => exact List.mem_cons_of_mem _ member

/- The exact syscall write set is an extension of the logical delta selected
by the table/index preparation. This is the first half of the frame proof for
lifting component certificates across page-zero/freelist augmentation. -/
set_option maxRecDepth 10000 in
theorem planLocalizedWrites?_base_mem
    {current : Nat} {firstPage : List UInt8} {freePages : List Nat}
    {baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (planned : planLocalizedWrites? current firstPage freePages baseWrites =
      some finalWrites) :
    ∀ write ∈ baseWrites, write ∈ finalWrites := by
  intro write member
  simp only [planLocalizedWrites?] at planned
  split at planned
  next =>
    rcases Option.bind_eq_some_iff.mp planned with
      ⟨headerAndSuffix, headerResult, planned⟩
    rcases headerAndSuffix with ⟨header, suffix⟩
    rcases Option.bind_eq_some_iff.mp planned with
      ⟨pageAndRest, pageResult, planned⟩
    rcases pageAndRest with ⟨headerPage, headerRest⟩
    split at planned
    next =>
      rcases Option.bind_eq_some_iff.mp planned with
        ⟨augmented, augmentedResult, finalResult⟩
      injection finalResult with finalEq
      subst finalWrites
      exact addLocalizedHeaderWrite_base_mem firstPage headerPage
        augmented write
        (addFreelistWrite?_base_mem augmentedResult write member)
    next => contradiction
  next => contradiction

theorem addFreelistWrite?_sources
    {freePages : List Nat}
    {writes finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (success : addFreelistWrite? freePages writes = some finalWrites) :
    ∀ write ∈ finalWrites,
      write ∈ writes ∨ ∃ trunk ∈ freePages, write.pageId = trunk - 1 := by
  intro write member
  cases freePages with
  | nil =>
      simp only [addFreelistWrite?, Option.some.injEq] at success
      subst finalWrites
      exact .inl member
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
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact .inr ⟨trunk, by simp, rfl⟩
          · exact .inl member
        next => contradiction
      next => contradiction

theorem addLocalizedHeaderWrite_sources
    (firstPage : List UInt8)
    (headerPage : Storage.Page PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    ∀ write ∈ addLocalizedHeaderWrite firstPage headerPage writes,
      write ∈ writes ∨ write.pageId = 0 := by
  intro write member
  unfold addLocalizedHeaderWrite at member
  split at member
  next => exact .inl member
  next =>
    split at member
    next => exact .inl member
    next =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact .inr rfl
      · exact .inl member

/- Every final write is either a logical delta write, page zero, or the one
freelist trunk selected from the post-state free-page list. -/
set_option maxRecDepth 10000 in
theorem planLocalizedWrites?_sources
    {current : Nat} {firstPage : List UInt8} {freePages : List Nat}
    {baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (planned : planLocalizedWrites? current firstPage freePages baseWrites =
      some finalWrites) :
    ∀ write ∈ finalWrites,
      write ∈ baseWrites ∨ write.pageId = 0 ∨
        ∃ trunk ∈ freePages, write.pageId = trunk - 1 := by
  intro write member
  simp only [planLocalizedWrites?] at planned
  split at planned
  next =>
    rcases Option.bind_eq_some_iff.mp planned with
      ⟨headerAndSuffix, headerResult, planned⟩
    rcases headerAndSuffix with ⟨header, suffix⟩
    rcases Option.bind_eq_some_iff.mp planned with
      ⟨pageAndRest, pageResult, planned⟩
    rcases pageAndRest with ⟨headerPage, headerRest⟩
    split at planned
    next =>
      rcases Option.bind_eq_some_iff.mp planned with
        ⟨augmented, augmentedResult, finalResult⟩
      injection finalResult with finalEq
      subst finalWrites
      rcases addLocalizedHeaderWrite_sources firstPage headerPage augmented
          write member with augmentedMember | pageZero
      · rcases addFreelistWrite?_sources augmentedResult write augmentedMember
            with baseMember | trunk
        · exact .inl baseMember
        · exact .inr (.inr trunk)
      · exact .inr (.inl pageZero)
    next => contradiction
  next => contradiction

/-- The exact final write set selected before the journal protocol begins.
`planned` is proof-only, while `writes` is the executable value consumed by
the journal, main-file writer, read-back verifier, and crash-trace builder. -/
structure PreparedLocalizedWrites
    (freePages : List Nat)
    (baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) where
  currentPageCount : Nat
  firstPage : List UInt8
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  planned : planLocalizedWrites? currentPageCount firstPage freePages
    baseWrites = some writes
  distinct : writes.Pairwise (fun left right => left.pageId ≠ right.pageId)

/-- The pure localized plan was prepared from this exact pre-commit image.
Both equalities are erased.  Grouping them prevents a durability proof from
combining a page count from one file with page zero from another file while
leaving the executable planner and write list unchanged. -/
structure PreparedLocalizedWrites.OnImage
    {freePages : List Nat}
    {baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (prepared : PreparedLocalizedWrites freePages baseWrites)
    (image : GrowableStorage.Image PhysicalCodec.pageSize) : Prop where
  pageCount : prepared.currentPageCount = image.pageCount
  pageZero : prepared.firstPage = (image.read 0).bytes.toList

theorem PreparedLocalizedWrites.base_mem
    {freePages : List Nat}
    {baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (prepared : PreparedLocalizedWrites freePages baseWrites) :
    ∀ write ∈ baseWrites, write ∈ prepared.writes :=
  planLocalizedWrites?_base_mem prepared.planned

theorem PreparedLocalizedWrites.sources
    {freePages : List Nat}
    {baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (prepared : PreparedLocalizedWrites freePages baseWrites) :
    ∀ write ∈ prepared.writes,
      write ∈ baseWrites ∨ write.pageId = 0 ∨
        ∃ trunk ∈ freePages, write.pageId = trunk - 1 :=
  planLocalizedWrites?_sources prepared.planned

/-- With no free pages, the localized planner can add only the SQLite header
write at page zero.  This is the common point-update/YCSB shape and is the
exact framing fact needed to extend table/index noninterference from the base
delta to the final journaled write list. -/
theorem PreparedLocalizedWrites.added_pageZero_of_noFreePages
    {freePages : List Nat} {baseWrites : List
      (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (prepared : PreparedLocalizedWrites freePages baseWrites)
    (noFree : freePages = [])
    {write : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (member : write ∈ prepared.writes) (notBase : write ∉ baseWrites) :
    write.pageId = 0 := by
  rcases prepared.sources write member with base | pageZero | trunk
  · exact False.elim (notBase base)
  · exact pageZero
  · rcases trunk with ⟨trunk, member, equal⟩
    rw [noFree] at member
    simp at member

set_option maxRecDepth 10000 in
/-- Stable point-update planning emits no page-zero write.  The proof unfolds
the actual planner: an empty freelist and bounded base writes preserve the
header's size/freelist fields, so the canonical patched header is byte-equal
to the page already on disk. -/
theorem PreparedLocalizedWrites.pageZero_not_mem_of_stable
    {freePages : List Nat} {baseWrites : List
      (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (prepared : PreparedLocalizedWrites freePages baseWrites)
    (noFree : freePages = [])
    (baseBound : ∀ write ∈ baseWrites,
      write.pageId < prepared.currentPageCount)
    (baseNoZero : ∀ write ∈ baseWrites, 0 ≠ write.pageId)
    (header : FileFormat.DatabaseHeader) (suffix : List UInt8)
    (decoded : FileFormat.decodeDatabaseHeader prepared.firstPage =
      some (header, suffix))
    (canonical : prepared.firstPage =
      FileFormat.encodeDatabaseHeader header ++ suffix)
    (pageCount : header.databaseSizePages.val = prepared.currentPageCount)
    (firstFree : header.firstFreelistTrunk.val = 0)
    (freeCount : header.freelistPageCount.val = 0) :
    ∀ write ∈ prepared.writes, 0 ≠ write.pageId := by
  subst freePages
  have target := targetPageCount_eq_of_forall_lt
    prepared.currentPageCount baseWrites baseBound
  have planned := prepared.planned
  unfold planLocalizedWrites? at planned
  rw [decoded] at planned
  simp only [List.length_nil] at planned
  split at planned
  next bounds =>
    let count : FileFormat.U32Value :=
      ⟨targetPageCount prepared.currentPageCount baseWrites, bounds.1⟩
    let zeroCount : FileFormat.U32Value := ⟨0, by omega⟩
    have countEq : count = header.databaseSizePages := by
      apply Fin.ext
      exact target.trans pageCount.symm
    have firstFreeEq : zeroCount = header.firstFreelistTrunk := by
      apply Fin.ext
      exact firstFree.symm
    have freeCountEq : zeroCount = header.freelistPageCount := by
      apply Fin.ext
      exact freeCount.symm
    have updatedHeaderEq :
        ({ header with
          databaseSizePages := count
          firstFreelistTrunk := zeroCount
          freelistPageCount := zeroCount } : FileFormat.DatabaseHeader) =
          header := by
      cases header
      simp only at countEq firstFreeEq freeCountEq ⊢
      congr
    change
      (do
        let (headerPage, headerRest) ←
          DiskFormat.decodeStoragePage PhysicalCodec.pageSize
            (FileFormat.encodeDatabaseHeader
              ({ header with
                databaseSizePages := count
                firstFreelistTrunk := zeroCount
                freelistPageCount := zeroCount } :
                FileFormat.DatabaseHeader) ++ suffix)
        if _headerExact : headerRest = [] then
          let writes ← addFreelistWrite? [] baseWrites
          some (addLocalizedHeaderWrite prepared.firstPage headerPage writes)
        else none) = some prepared.writes at planned
    rw [updatedHeaderEq] at planned
    rcases Option.bind_eq_some_iff.mp planned with
      ⟨pageAndRest, pageResult, planned⟩
    rcases pageAndRest with ⟨headerPage, headerRest⟩
    split at planned
    next pairExact =>
      cases pairExact
      split at planned
      next headerExact =>
        have pageBytes := DiskFormat.decodeStoragePage_sound pageResult
        rw [headerExact, List.append_nil] at pageBytes
        simp only [addFreelistWrite?, Option.bind_eq_bind, Option.bind] at planned
        have headerSame :
            (headerPage.bytes.toList == prepared.firstPage) = true := by
          simp [canonical, ← pageBytes]
        unfold addLocalizedHeaderWrite at planned
        rw [if_neg (by
          simp only [List.any_eq_true]
          rintro ⟨witness, member, equal⟩
          have pageZero : witness.pageId = 0 := of_decide_eq_true equal
          exact baseNoZero witness member pageZero.symm)] at planned
        rw [if_pos headerSame] at planned
        injection planned with finalEq
        intro write member
        apply baseNoZero write
        rw [finalEq]
        exact member
      next => contradiction
  next => contradiction

/-- Header/freelist framing added after the logical delta cannot alias any
table-tree page owned by the allocator state. This closes the table-page part
of the frame argument without inspecting bytes at runtime. -/
theorem PreparedLocalizedWrites.added_disjoint_active
    {state : CoreChunkPageState.State}
    {baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (prepared : PreparedLocalizedWrites state.freePages baseWrites)
    (allocation : state.AllocationWellFormed)
    {write : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (member : write ∈ prepared.writes) (notBase : write ∉ baseWrites) :
    ∀ pageId ∈ state.activePageIds, write.pageId + 1 ≠ pageId := by
  intro pageId active equal
  rcases prepared.sources write member with base | pageZero | trunk
  · exact notBase base
  · have afterCatalog := allocation.active_after_catalog pageId active
    rw [pageZero] at equal
    omega
  · rcases trunk with ⟨trunk, free, writePage⟩
    have trunkAfterCatalog := allocation.free_after_catalog trunk free
    have freeNotActive := allocation.free_not_active trunk free
    rw [writePage] at equal
    have trunkEq : trunk = pageId := by omega
    rw [trunkEq] at freeNotActive
    exact freeNotActive active

/-- The allocator-level frame theorem specializes to every numbered tree page
in the strong physical representation. This is the form consumed when an
ordinary table certificate is transported from the logical delta to the final
header/freelist-augmented syscall write set. -/
theorem PreparedLocalizedWrites.added_disjoint_table_tree
    {state : CoreChunkPageState.State}
    {baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (prepared : PreparedLocalizedWrites state.freePages baseWrites)
    (allocation : state.AllocationWellFormed)
    {source : CoreDecode.PageSource}
    {table : CoreChunkPageState.TableState}
    (tableMember : table ∈ state.tables)
    (physical : CoreLocalizedRepresentation.TableOnSource source table)
    {write : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (writeMember : write ∈ prepared.writes)
    (notBase : write ∉ baseWrites)
    {numbered : CorePageCodec.NumberedPage}
    (pageMember : numbered ∈ physical.encoding.treePages) :
    write.pageId + 1 ≠ numbered.pageNumber := by
  have pageNumberMember : numbered.pageNumber ∈ table.tree.root.pageIds := by
    rw [← CorePageCodec.encodeChunkNodeWithOverflow_pageNumbers
      table.table.schema table.tree.root physical.nextOverflow
        physical.encoding physical.encoded]
    exact List.mem_map_of_mem pageMember
  have active : numbered.pageNumber ∈ state.activePageIds := by
    unfold CoreChunkPageState.State.activePageIds
      CoreChunkPageState.tablePageIds
    exact List.mem_flatMap.mpr ⟨table, tableMember, by
      simpa [CoreChunkPageState.TableState.pageIds] using pageNumberMember⟩
  exact prepared.added_disjoint_active allocation writeMember notBase
    numbered.pageNumber active

/-- Representation-independent form of `added_disjoint_table_tree`.  It is
used while constructing the changed-table representation itself, where an
already-built `TableOnSource` witness for the post-state would be circular.
The successful tree encoding identifies each numbered page with the live
allocator's active page-ID set. -/
theorem PreparedLocalizedWrites.added_disjoint_encoded_table_tree
    {state : CoreChunkPageState.State}
    {baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (prepared : PreparedLocalizedWrites state.freePages baseWrites)
    (allocation : state.AllocationWellFormed)
    {table : CoreChunkPageState.TableState}
    (tableMember : table ∈ state.tables)
    {pages : List CorePageCodec.NumberedPage}
    (encoded : CorePageCodec.encodeChunkNode table.table.schema
      table.tree.root = some pages)
    {write : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (writeMember : write ∈ prepared.writes)
    (notBase : write ∉ baseWrites)
    {numbered : CorePageCodec.NumberedPage}
    (pageMember : numbered ∈ pages) :
    write.pageId + 1 ≠ numbered.pageNumber := by
  have pageNumberMember : numbered.pageNumber ∈ table.tree.root.pageIds := by
    rw [← CorePageCodec.encodeChunkNode_pageNumbers
      table.table.schema table.tree.root pages encoded]
    exact List.mem_map_of_mem pageMember
  have active : numbered.pageNumber ∈ state.activePageIds := by
    unfold CoreChunkPageState.State.activePageIds
      CoreChunkPageState.tablePageIds
    exact List.mem_flatMap.mpr ⟨table, tableMember, by
      simpa [CoreChunkPageState.TableState.pageIds] using pageNumberMember⟩
  exact prepared.added_disjoint_active allocation writeMember notBase
    numbered.pageNumber active

private def certifyLocalizedWrites?
    (current : Nat) (firstPage : List UInt8) (freePages : List Nat)
    (baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    Option (PreparedLocalizedWrites freePages baseWrites) :=
  match planned : planLocalizedWrites? current firstPage freePages baseWrites with
  | none => none
  | some writes =>
      if distinct : writes.Pairwise
          (fun left right => left.pageId ≠ right.pageId) then
        some { currentPageCount := current, firstPage, writes, planned, distinct }
      else none

/-- Read only the current page count and page zero, then run the pure planner.
This function performs no journal or main-file mutation. -/
private def prepareLocalizedWrites (path : System.FilePath)
    (freePages : List Nat)
    (baseWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    IO (PreparedLocalizedWrites freePages baseWrites) := do
  IO.FS.withFile path .read fun handle => do
    let current ← readPageCount handle path
    let first ← SyscallVFS.preadBytes path.toString 0
      (USize.ofNat PhysicalCodec.pageSize)
    unless first.size = PhysicalCodec.pageSize do
      throw (IO.userError "short read while updating the SQLite header")
    match certifyLocalizedWrites? current first.toList freePages baseWrites with
    | some prepared => pure prepared
    | none => throw (IO.userError
        "localized allocation, freelist, or write identity is invalid")

private def journalFromFile (path : System.FilePath)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    IO (GrowableStorage.Journal PhysicalCodec.pageSize) :=
  IO.FS.withFile path .read fun handle => do
    let count ← readPageCount handle path
    let writes := writes.toArray
    let reversedUndo ← IO.iterate (0, []) fun state => do
      let index := state.1
      if bound : index < writes.size then
        let write := writes[index]
        if write.pageId < count then
          let bytes ← SyscallVFS.preadBytes path.toString
            (UInt64.ofNat (write.pageId * PhysicalCodec.pageSize))
            (USize.ofNat PhysicalCodec.pageSize)
          if exact : bytes.size = PhysicalCodec.pageSize then
            let before : Storage.Page PhysicalCodec.pageSize := {
              bytes := bytes.data
              sizeInvariant := exact }
            return .inl (index + 1, ⟨write.pageId, before⟩ :: state.2)
          else
            throw (IO.userError s!"short read for main page {write.pageId}")
        else
          return .inl (index + 1, state.2)
      else
        return .inr state.2
    return ⟨count, reversedUndo.reverse⟩

private def verifyWrittenPages (path : System.FilePath)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : IO Unit := do
  SyscallVFS.verifyPages path.toString (pageTransfers writes)

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

private def preadPageSourceCached (path : System.FilePath)
    (pageCount : Nat) (cache : PageReadCache) : CoreDecode.IOPageSource := {
  pageCount
  readPage := fun page => do
    return (← (readPager path pageCount cache).get page).map ByteArray.toList }

/-- Compatibility adapter: the pager owns bytes, the table cursor locates a
cell, and the record layer decodes its payload. Existing generated-index and
primary-key readers share the same bounded transaction-local resources. -/
private def lookupTableRowidBytesCached (path : System.FilePath)
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

private def decodedIndexPageCached (cache : PageReadCache)
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
    -- Read the file once and slice pages out of the buffer rather than issuing a
    -- read per page. The streaming source cost one syscall per page, which
    -- dominated the general open: at 11 MB this step alone was 3.4 s and is now
    -- about 1.3 s. The page size comes from the validated header, not from
    -- `PhysicalCodec.pageSize`, so files written with a non-default page size
    -- still decode -- using the fixed-size `byteArrayPageSource` here silently
    -- broke the 1024-byte differential case.
    let whole ← IO.FS.readBinFile paths.main
    let pageBytes := usable.val
    let source : CoreDecode.IOPageSource := {
      -- `usable` is defaulted on `IOPageSource`, and omitting it here is what
      -- broke the 1024-byte differential case: the slices were the header's page
      -- size while the decoder's cell and overflow thresholds stayed at 4096, so
      -- every page parsed as garbage and the open reported a corrupt image.
      usable
      pageCount := count
      readPage := fun pageNumber => pure <|
        if pageNumber = 0 || count < pageNumber then none
        else
          let start := (pageNumber - 1) * pageBytes
          let stop := start + pageBytes
          if stop ≤ whole.size then some (whole.extract start stop).data.toList
          else none }
    match ← CoreDecode.decodeFromIOPageSource source with
    | some database => return database
    | none => throw (IO.userError s!"invalid general MVP SQLite image: {paths.main}")

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
  unless input.size = count * PhysicalCodec.pageSize do return none
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
  unless input.size = count * PhysicalCodec.pageSize do return none
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

/-- The fast array-backed decoder source and the growable-storage view read
the same page bytes.  The equality is proof-only: live opens retain O(1)
array slicing and never build the range/list used by `ofStorageImage`. -/
theorem byteArrayPageSource_eq_storageImage
    (input : ByteArray) (pageCount : Nat)
    (exactSize : input.size = pageCount * PhysicalCodec.pageSize) :
    byteArrayPageSource input pageCount =
      CorePageSource.ofStorageImage
        (byteArrayStorageImage input pageCount exactSize) := by
  apply CorePageSource.pageSource_ext
  · simp [byteArrayPageSource, byteArrayStorageImage]
  · funext pageNumber
    by_cases zero : pageNumber = 0
    · subst pageNumber
      simp [byteArrayPageSource, CorePageSource.readPage_zero]
    by_cases high : pageCount < pageNumber
    · rw [CorePageSource.readPage_out_of_bounds _ _ high]
      simp [byteArrayPageSource, zero, high]
    · have bound : pageNumber - 1 < pageCount := by omega
      have pageNumberEq : pageNumber - 1 + 1 = pageNumber := by omega
      have stopBound : (pageNumber - 1) * PhysicalCodec.pageSize +
          PhysicalCodec.pageSize ≤ input.size := by
        rw [exactSize]
        have pageWithin : pageNumber - 1 + 1 ≤ pageCount := by omega
        have scaled := Nat.mul_le_mul_right PhysicalCodec.pageSize pageWithin
        simpa [Nat.add_mul] using scaled
      have pageWithin : pageNumber - 1 + 1 ≤ pageCount := by omega
      rw [← pageNumberEq,
        CorePageSource.readPage_ofStorageImage _ (pageNumber - 1) bound]
      simp [byteArrayPageSource, byteArrayStorageImage, zero, high, bound,
        stopBound, pageWithin]

/-- Read a supported physical image once and recover its logical database and
persistent page identities together.  The returned capability records that
the index images were validated by this same open. Returning `none` is an
optimization miss: callers retain the general compatibility path. -/
def loadOpenState (paths : Paths) :
    IO (Option ValidatedOpenState) := do
  let input ← IO.FS.readBinFile paths.main
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let some (header, _) := FileFormat.decodeDatabaseHeader firstPageBytes |
    return none
  let count := header.databaseSizePages.val
  unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
      header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
      input.size = count * PhysicalCodec.pageSize do return none
  let source := byteArrayPageSource input count
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

/-- Retain the source identity hidden by the ordinary optional certificate.
This wrapper is proof-only and lets the localized writer connect a successful
decoder check to the exact storage overlay it checked. -/
structure CertifiedDecodedIndexAt (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) (source : CoreDecode.PageSource) where
  certificate : DecodedIndexCertificate rootPage table index
  sourceExact : certificate.source = source

def certifyDecodedIndexAt? (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) (source : CoreDecode.PageSource) :
    Option (CertifiedDecodedIndexAt rootPage table index source) :=
  match success : certifyDecodedIndex? rootPage table index source with
  | none => none
  | some certificate =>
      some ⟨certificate, certifyDecodedIndex?_source success⟩

inductive LocalizedIndexCertificate (rootPage : Nat) (table : Core.Table)
    (index : Core.Index) where
  | encoded (certificate : CertifiedIndexEncoding rootPage table index)
  | decoded (certificate : DecodedIndexCertificate rootPage table index)

/-- A routed index mutation was decoded over the finite write overlay of an
exact old storage image. -/
def DecodedIndexCertificate.OnStorage
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    (certificate : DecodedIndexCertificate rootPage table index)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : Prop :=
  ∃ oldImage : GrowableStorage.Image PhysicalCodec.pageSize,
    certificate.source = CorePageSource.ofStorageImage
      (GrowableStorage.applyWrites oldImage writes)

def CertifiedIndexEncoding.OnStorage
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    (certificate : CertifiedIndexEncoding rootPage table index)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) : Prop :=
  ∃ oldImage : GrowableStorage.Image PhysicalCodec.pageSize,
    CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites oldImage writes))
      rootPage certificate.value.pages ∧
    0 < rootPage ∧
    rootPage + certificate.value.pages.length < 2 ^ 32 ∧
    rootPage + certificate.value.pages.length ≤
      (GrowableStorage.applyWrites oldImage writes).pageCount + 1

structure LocalizedLastIndexDelta
    (delta : CoreChunkPageDelta.StateDelta) where
  candidate : CoreChunkPageDelta.updateStateCandidate? delta.before
    delta.after.database = some delta
  state : CoreChunkPageState.State
  index : Core.Index
  rootPage : Nat
  entry : CoreDecode.CatalogEntry
  entryTable : entry.table = delta.table.after.table.schema.name
  entryRoot : entry.rootPage = rootPage
  entryMetadata : CoreDecode.decodeCanonicalIndex
    delta.table.after.table.schema delta.table.after.table.schema.name entry =
      some index
  tableExpectedBefore : List
    (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  tableWrites : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  tableExpectedBeforeEq : CoreChunkPageDelta.beforeWrites delta.table =
    some tableExpectedBefore
  tableWritesEq : CoreChunkPageDelta.writes delta.table = some tableWrites
  expectedBefore : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  certificate : LocalizedIndexCertificate rootPage
    delta.table.after.table index
  storage : match certificate with
    | .encoded encoded => encoded.OnStorage writes
    | .decoded decoded => decoded.OnStorage writes
  writesDistinct : writes.Pairwise (fun left right => left.pageId ≠ right.pageId)
  allocation : state.AllocationWellFormed
  validated : ValidatedOpenState

/-- Turn one small decidable boundary check into erased evidence retained by a
prepared delta.  This is used only for catalog identity, never to validate a
table or index by re-running its logical operation. -/
private def decideProof? (proposition : Prop) [Decidable proposition] :
    Option (PLift proposition) :=
  if proof : proposition then some ⟨proof⟩ else none

/-- Retain the defining equation of an `Option` value selected by executable
preparation.  The equation is erased when used in proof fields, but prevents
the durability layer from attaching a page list reconstructed separately. -/
private structure ExactOptionResult (result : Option α) where
  value : α
  exact : result = some value

private def exactOptionResult? (result : Option α) :
    Option (ExactOptionResult result) :=
  match exact : result with
  | none => none
  | some value => some ⟨value, by cases exact; rfl⟩

private def storagePage? (bytes : List UInt8) :
    Option (Storage.Page PhysicalCodec.pageSize) :=
  if exact : bytes.length = PhysicalCodec.pageSize then
    some {
      bytes := bytes.toArray
      sizeInvariant := by simp [exact] }
  else none

private theorem storagePage?_bytes {bytes : List UInt8}
    {page : Storage.Page PhysicalCodec.pageSize}
    (success : storagePage? bytes = some page) :
    page.bytes.toList = bytes := by
  unfold storagePage? at success
  split at success
  next =>
    injection success with equal
    subst page
    simp
  next => contradiction

/-- Read one exact contiguous pre-image run.  The recursive form retains a
simple kernel proof that every returned page really came from its numbered
source read. -/
private def readPageWrites? (source : CoreDecode.PageSource) :
    Nat → Nat → Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
  | _, 0 => some []
  | pageNumber, count + 1 => do
      let bytes ← source.readPage pageNumber
      let page ← storagePage? bytes
      let tail ← readPageWrites? source (pageNumber + 1) count
      some (⟨pageNumber - 1, page⟩ :: tail)

private structure ReadPageWritesResult (source : CoreDecode.PageSource)
    (start count : Nat) where
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  exact : readPageWrites? source start count = some writes

private def readPageWritesCertified? (source : CoreDecode.PageSource)
    (start count : Nat) : Option (ReadPageWritesResult source start count) :=
  match success : readPageWrites? source start count with
  | none => none
  | some writes => some ⟨writes, success⟩

private theorem readPageWrites?_reads
    (source : CoreDecode.PageSource) :
    ∀ {start count : Nat}
      {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)},
      0 < start →
      readPageWrites? source start count = some writes →
      ∀ write ∈ writes,
        source.readPage (write.pageId + 1) = some write.page.bytes.toList
  | _, 0, writes, _, success => by
      simp only [readPageWrites?, Option.some.injEq] at success
      subst writes
      simp
  | start, count + 1, writes, positive, success => by
      simp only [readPageWrites?, Option.bind_eq_bind, Option.bind] at success
      cases readResult : source.readPage start with
      | none => simp [readResult] at success
      | some bytes =>
          simp only [readResult] at success
          cases pageResult : storagePage? bytes with
          | none => simp [pageResult] at success
          | some page =>
              simp only [pageResult] at success
              cases tailResult : readPageWrites? source (start + 1) count with
              | none => simp [tailResult] at success
              | some tail =>
                  simp only [tailResult, Option.some.injEq] at success
                  subst writes
                  intro write member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · have pageNumber : start - 1 + 1 = start := by omega
                    rw [pageNumber, readResult, storagePage?_bytes pageResult]
                  · exact readPageWrites?_reads source (by omega) tailResult
                      write member

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

theorem indexPageWrites_covers (rootPage : Nat) (pages : List CoreFile.Page)
    (positive : 0 < rootPage) :
    ∀ (offset : Nat) (inBounds : offset < pages.length),
      ∃ write ∈ indexPageWrites rootPage pages,
        write.pageId + 1 = rootPage + offset ∧
        write.page.bytes.toList = (pages.get ⟨offset, inBounds⟩).bytes := by
  induction pages generalizing rootPage with
  | nil => simp
  | cons page pages induction =>
      intro offset inBounds
      cases offset with
      | zero =>
          refine ⟨⟨rootPage - 1, page.storage⟩, by simp [indexPageWrites], ?_, ?_⟩
          · change rootPage - 1 + 1 = rootPage
            omega
          · simp [CoreFile.Page.storage]
      | succ offset =>
          have tailBound : offset < pages.length := by
            simpa using inBounds
          rcases induction (rootPage := rootPage + 1) (by omega) offset tailBound
            with ⟨write, member, pageNumber, bytes⟩
          refine ⟨write, by simp [indexPageWrites, member], ?_, ?_⟩
          · omega
          · simpa using bytes

theorem indexPageWrites_member_exact (rootPage : Nat)
    (pages : List CoreFile.Page) :
    ∀ {write : GrowableStorage.PageWrite PhysicalCodec.pageSize},
      write ∈ indexPageWrites rootPage pages →
      ∃ (offset : Nat) (inBounds : offset < pages.length),
        write = ⟨rootPage + offset - 1,
          (pages.get ⟨offset, inBounds⟩).storage⟩ := by
  induction pages generalizing rootPage with
  | nil => simp [indexPageWrites]
  | cons page pages induction =>
      intro write member
      simp only [indexPageWrites, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨0, by simp, by simp⟩
      · rcases induction (rootPage := rootPage + 1) member with
          ⟨offset, inBounds, exactWrite⟩
        refine ⟨offset + 1, by simpa, ?_⟩
        rw [exactWrite]
        congr 1 <;> omega

theorem indexPageWrites_eq_of_pageId_eq (rootPage : Nat)
    (pages : List CoreFile.Page)
    (positive : 0 < rootPage)
    {left right : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (leftMember : left ∈ indexPageWrites rootPage pages)
    (rightMember : right ∈ indexPageWrites rootPage pages)
    (samePage : left.pageId = right.pageId) : left = right := by
  rcases indexPageWrites_member_exact rootPage pages leftMember with
    ⟨leftOffset, leftBound, leftExact⟩
  rcases indexPageWrites_member_exact rootPage pages rightMember with
    ⟨rightOffset, rightBound, rightExact⟩
  subst left
  subst right
  simp only [GrowableStorage.PageWrite.pageId] at samePage
  have offsets : leftOffset = rightOffset := by omega
  subst rightOffset
  rfl

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

structure IndexPageMutations where
  source : CoreDecode.PageSource
  changed : List (Nat × List UInt8) := []

/-- The file-backed counterpart of `IndexPageMutations`.  It retains only the
pages on the routed index path; unchanged pages are fetched positionally from
the main file instead of materializing the whole database before every
autocommit insert. -/
structure IOIndexPageMutations where
  source : CoreDecode.IOPageSource
  changed : List (Nat × List UInt8) := []
  nextPage : Nat

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

def IOIndexPageMutations.readPage? (state : IOIndexPageMutations)
    (pageNumber : Nat) : IO (Option (List UInt8)) :=
  match state.changed.find? (fun changed => changed.1 == pageNumber) with
  | some changed => pure (some changed.2)
  | none => state.source.readPage pageNumber

def IOIndexPageMutations.pageSource (state : IOIndexPageMutations) :
    CoreDecode.IOPageSource := {
  usable := state.source.usable
  pageCount := state.nextPage - 1
  readPage := state.readPage? }

def IOIndexPageMutations.writePage? (state : IOIndexPageMutations)
    (pageNumber : Nat) (page : CoreFile.Page) : Option IOIndexPageMutations := do
  if _valid : 0 < pageNumber ∧ pageNumber < state.nextPage then
    some { state with
      changed := replaceChangedPage pageNumber page.bytes state.changed }
  else none

def IOIndexPageMutations.allocatePage? (state : IOIndexPageMutations)
    (page : CoreFile.Page) : Option (Nat × IOIndexPageMutations) := do
  if _fits : state.nextPage < 2 ^ 32 then
    some (state.nextPage, {
      state with
      changed := replaceChangedPage state.nextPage page.bytes state.changed
      nextPage := state.nextPage + 1 })
  else none

/-- Split exactly `count` elements in one traversal, rejecting a short input. -/
def takeExact : Nat → List α → Option (List α × List α)
  | 0, input => some ([], input)
  | _ + 1, [] => none
  | count + 1, byte :: input => do
      let (front, suffix) ← takeExact count input
      some (byte :: front, suffix)

theorem takeExact_spec {count : Nat} {input front suffix : List α}
    (success : takeExact count input = some (front, suffix)) :
    front.length = count ∧ front ++ suffix = input := by
  induction count generalizing input front suffix with
  | zero =>
      simp only [takeExact, Option.some.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      simp
  | succ count induction =>
      cases input with
      | nil => simp [takeExact] at success
      | cons byte input =>
          simp only [takeExact, Option.bind_eq_bind, Option.bind] at success
          cases recursive : takeExact count input with
          | none => simp [recursive] at success
          | some result =>
              rcases result with ⟨tail, rest⟩
              simp only [recursive, Option.some.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              rcases induction recursive with ⟨length, reconstruct⟩
              simp [length, reconstruct]

def splitInlineIndexCells : Nat → List UInt8 →
    Option (List (List UInt8) × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (payloadSize, _afterSize) ← FileFormat.decodeVarint input
      if _inline : payloadSize.val ≤
          FileFormat.indexMaxLocal PhysicalCodec.usablePageSize then
        -- This path only accepts canonical packed generated pages.  Derive
        -- the canonical varint width from its decoded value instead of
        -- repeatedly traversing the shrinking page suffix twice per cell.
        -- A non-minimal external varint therefore fails closed below when
        -- its suffix does not line up with the declared cell count.
        let prefixLength := FileFormat.sqliteVarintSize payloadSize.val
        let cellLength := prefixLength + payloadSize.val
        let (cell, rest) ← takeExact cellLength input
        let tail ← splitInlineIndexCells count rest
        some (cell :: tail.1, tail.2)
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

/-- Page-directed I/O implementation of `insertIndexEntryNoSplit?`.  Its
control decisions and leaf rewrite are identical; only the unchanged-page
reads are performed through `pread`. -/
def insertIndexEntryNoSplitIO? : Nat → Nat → CoreDecode.IndexEntry →
    List UInt8 → IOIndexPageMutations → IO (Option IOIndexPageMutations)
  | 0, _, _, _, _ => pure none
  | fuel + 1, pageNumber, target, targetCell, state => do
      let some page ← state.readPage? pageNumber | return none
      let source := state.pageSource
      match ← CoreDecode.decodeIndexInteriorIOFrom source page with
      | some (entries, rightmost) =>
          let rec descend : List (Nat × CoreDecode.IndexEntry) →
              IO (Option IOIndexPageMutations)
            | [] =>
                insertIndexEntryNoSplitIO? fuel rightmost target targetCell state
            | (child, separator) :: remaining =>
                if target = separator then pure none
                else if CoreChunkPageDelta.indexEntryLess target separator then
                  insertIndexEntryNoSplitIO? fuel child target targetCell state
                else descend remaining
          descend entries
      | none =>
          match inlineIndexLeafCells? page with
          | none => pure none
          | some cells =>
              match insertSortedIndexCell? target targetCell cells with
              | none => pure none
              | some inserted =>
                  match CoreFile.indexLeafPage? inserted with
                  | none => pure none
                  | some rewritten => pure (state.writePage? pageNumber rewritten)

inductive IOIndexInsertResult where
  | done (state : IOIndexPageMutations)
  | split (state : IOIndexPageMutations) (leftPage : Nat)
      (promoted : CoreDecode.IndexEntry) (rightPage : Nat)

private def coreFilePage? (bytes : List UInt8) : Option CoreFile.Page :=
  if exact : bytes.length = PhysicalCodec.pageSize then
    some ⟨bytes, exact⟩
  else none

/-- Encode an enlarged interior node, splitting it around one promoted entry
when its exact byte representation no longer fits.  Promoted entries are
removed from both children, matching SQLite index-B-tree semantics. -/
private def rewriteOrSplitIndexInteriorIO?
    (pageNumber : Nat) (entries : List (Nat × CoreDecode.IndexEntry))
    (rightmost : Nat) (state : IOIndexPageMutations) :
    Option IOIndexInsertResult :=
  match indexInteriorPageFromEntries? entries rightmost with
  | some page => (state.writePage? pageNumber page).map IOIndexInsertResult.done
  | none => do
      let middleIndex := entries.length / 2
      let middle ← entries[middleIndex]?
      let leftEntries := entries.take middleIndex
      let rightEntries := entries.drop (middleIndex + 1)
      let leftPage ← indexInteriorPageFromEntries? leftEntries middle.1
      let rightPage ← indexInteriorPageFromEntries? rightEntries rightmost
      let leftState ← state.writePage? pageNumber leftPage
      let (rightNumber, finalState) ← leftState.allocatePage? rightPage
      some (.split finalState pageNumber middle.2 rightNumber)

private structure IndexInsertRoute where
  child : Nat
  prior : List (Nat × CoreDecode.IndexEntry)
  boundary : Option (Nat × CoreDecode.IndexEntry)
  remaining : List (Nat × CoreDecode.IndexEntry)

private def indexInsertRoute? (target : CoreDecode.IndexEntry)
    (rightmost : Nat) : List (Nat × CoreDecode.IndexEntry) →
      List (Nat × CoreDecode.IndexEntry) → Option IndexInsertRoute
  | [], reversed => some {
      child := rightmost
      prior := reversed.reverse
      boundary := none
      remaining := [] }
  | current :: remaining, reversed =>
      if target = current.2 then none
      else if CoreChunkPageDelta.indexEntryLess target current.2 then
        some {
          child := current.1
          prior := reversed.reverse
          boundary := some current
          remaining }
      else indexInsertRoute? target rightmost remaining (current :: reversed)

/-- Full high-fanout index insertion.  A leaf split promotes one cell; an
interior page either absorbs that promotion or splits recursively. -/
def insertIndexEntryIO? : Nat → Nat → CoreDecode.IndexEntry → List UInt8 →
    IOIndexPageMutations → IO (Option IOIndexInsertResult)
  | 0, _, _, _, _ => pure none
  | fuel + 1, pageNumber, target, targetCell, state => do
      let some page ← state.readPage? pageNumber | return none
      let source := state.pageSource
      match ← CoreDecode.decodeIndexInteriorIOFrom source page with
      | some (entries, rightmost) =>
          let some route := indexInsertRoute? target rightmost entries [] |
            return none
          let some child ← insertIndexEntryIO? fuel route.child target
            targetCell state | return none
          match child with
          | .done next => return some (.done next)
          | .split next left promoted right =>
              match route.boundary with
              | none =>
                  return rewriteOrSplitIndexInteriorIO? pageNumber
                    (route.prior ++ [(left, promoted)]) right next
              | some current =>
                  return rewriteOrSplitIndexInteriorIO? pageNumber
                    (route.prior ++ [(left, promoted), (right, current.2)] ++
                      route.remaining) rightmost next
      | none =>
          match inlineIndexLeafCells? page with
          | none => return none
          | some cells =>
              match insertSortedIndexCell? target targetCell cells with
              | none => return none
              | some inserted =>
                  match CoreFile.indexLeafPage? inserted with
                  | some rewritten =>
                      return (state.writePage? pageNumber rewritten).map
                        IOIndexInsertResult.done
                  | none =>
                      let middleIndex := inserted.length / 2
                      let some middleCell := inserted[middleIndex]? | return none
                      let some (promoted, suffix) :=
                        CoreDecode.decodeIndexCellWithSuffix middleCell |
                          return none
                      unless suffix = [] do return none
                      let some leftPage :=
                        CoreFile.indexLeafPage? (inserted.take middleIndex) |
                          return none
                      let some rightPage := CoreFile.indexLeafPage?
                        (inserted.drop (middleIndex + 1)) | return none
                      let some leftState := state.writePage? pageNumber leftPage |
                        return none
                      let some (rightNumber, finalState) :=
                        leftState.allocatePage? rightPage | return none
                      return some (.split finalState pageNumber promoted rightNumber)

/-- Keep the catalog root page stable.  When the old root splits, its left
image is copied to a fresh page and the old root becomes a one-separator
interior node. -/
def insertIndexEntryAtRootIO? (rootPage : Nat)
    (target : CoreDecode.IndexEntry) (targetCell : List UInt8)
    (state : IOIndexPageMutations) : IO (Option IOIndexPageMutations) := do
  let some result ← insertIndexEntryIO? (state.source.pageCount + 1)
    rootPage target targetCell state | return none
  match result with
  | .done next => return some next
  | .split next _ promoted rightPage =>
      let some leftBytes ← next.readPage? rootPage | return none
      let some leftPage := coreFilePage? leftBytes | return none
      let some (leftNumber, allocated) := next.allocatePage? leftPage | return none
      let some newRoot := indexInteriorPageFromEntries?
        [(leftNumber, promoted)] rightPage | return none
      return allocated.writePage? rootPage newRoot

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
              rcases Option.bind_eq_some_iff.mp success with ⟨tail, recursive, equal⟩
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

def insertIndexRowIntoPagesIO? (rootPage : Nat) (index : Core.Index)
    (row : Core.Row) (source : CoreDecode.IOPageSource) (nextPage : Nat) :
    IO (Option IOIndexPageMutations) := do
  let entry := CoreChunkPageDelta.indexEntryOfRow index row
  let some cell := indexEntryCell? entry | return none
  insertIndexEntryAtRootIO? rootPage entry cell {
    source
    nextPage }

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

def mutationPageWritesIO? (mutated : IOIndexPageMutations) :
    IO (Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize) ×
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))) := do
  let mut oldWrites := []
  let mut newWrites := []
  for changed in mutated.changed do
    let pageNumber := changed.1
    let newBytes := changed.2
    let some newPage := storagePage? newBytes | return none
    if pageNumber ≤ mutated.source.pageCount then
      let some oldBytes ← mutated.source.readPage pageNumber | return none
      let some oldPage := storagePage? oldBytes | return none
      oldWrites := (⟨pageNumber - 1, oldPage⟩ :
        GrowableStorage.PageWrite PhysicalCodec.pageSize) :: oldWrites
    newWrites := (⟨pageNumber - 1, newPage⟩ :
      GrowableStorage.PageWrite PhysicalCodec.pageSize) :: newWrites
  return some (oldWrites.reverse, newWrites.reverse)

private def currentWritesFor? (source : CoreDecode.PageSource) (count : Nat) :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize) →
      Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
  | [] => some []
  | write :: writes => do
      let tail ← currentWritesFor? source count writes
      if write.pageId < count then
        let bytes ← source.readPage (write.pageId + 1)
        let page ← storagePage? bytes
        some (⟨write.pageId, page⟩ :: tail)
      else some tail

private def currentWritesForIO? (source : CoreDecode.IOPageSource)
    (count : Nat) : List (GrowableStorage.PageWrite PhysicalCodec.pageSize) →
      IO (Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)))
  | [] => pure (some [])
  | write :: writes => do
      let some tail ← currentWritesForIO? source count writes | return none
      if write.pageId < count then
        let some bytes ← source.readPage (write.pageId + 1) | return none
        let some page := storagePage? bytes | return none
        return some (⟨write.pageId, page⟩ :: tail)
      else return some tail

structure PreparedWideAppend {state : CoreWidePageState.State}
    {snapshot : Option Core.Database} {tableName : String}
    {values : List Core.Value}
    (executed : CoreWidePageDelta.ExecutedInsert state snapshot tableName values) where
  state : CoreWidePageState.State
  textState : state.SingleIndexValuesText
  expectedBefore : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)
  index : Core.Index
  rootPage : Nat
  logicalIndexExact : CoreDecode.expectedIndexEntries
      executed.append.mutation.after.table index =
    CoreChunkPageDelta.insertIndexEntry
      (CoreChunkPageDelta.indexEntryOfRow index executed.row)
      (CoreDecode.expectedIndexEntries executed.append.table.table index)
  writesDistinct : writes.Pairwise (fun left right => left.pageId ≠ right.pageId)

/-- Prepare the live one-row wide append.  Table pages come only from the
changed right spine; the generated TEXT-primary index follows one routed path.
Any page-fit or index-split miss returns `none` to the proved bulk fallback. -/
def prepareWideAppend? {state : CoreWidePageState.State}
    {snapshot : Option Core.Database} {tableName : String}
    {values : List Core.Value}
    (input : ByteArray)
    (executed : CoreWidePageDelta.ExecutedInsert state snapshot tableName values) :
    Option (PreparedWideAppend executed) := do
  let firstPageBytes := (input.extract 0 PhysicalCodec.pageSize).toList
  let (header, _) ← FileFormat.decodeDatabaseHeader firstPageBytes
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noFree : header.freelistPageCount.val = 0 then
      if _length : input.size = count * PhysicalCodec.pageSize then
        let source := byteArrayPageSource input count
        let firstPage ← source.readPage 1
        let catalog ← CoreDecode.decodeCatalogForOpen firstPage
        let before := executed.append.table
        let after := executed.append.mutation.after
        if _sameSchema : before.table.schema = after.table.schema then
          if _sameIndexes : before.table.indexes = after.table.indexes then
            match afterIndexes : after.table.indexes with
            | [index] => do
                if beforeText : CoreFile.indexValuesText before.table index = true then
                  match rowValue : executed.row.value index.column with
                  | .text _ => do
                      let entry ← catalog.find? fun entry =>
                        entry.kind == "index" && entry.name == index.name &&
                          entry.table == after.table.schema.name
                      if _rootRange :
                          1 < entry.rootPage ∧ entry.rootPage ≤ count then
                        let tablePages ←
                          match executed.append.mutation.mode with
                          | .extendedTerminalChunk =>
                              CoreWidePageCodec.encodeTerminalReplacement
                                after.table.schema after.tree
                          | .appendedChunk =>
                              CoreWidePageCodec.encodeTerminalAppend
                                after.table.schema before.tree after.tree
                        let tableWrites ← tablePages.mapM
                          CoreChunkPageDelta.numberedWrite?
                        let tableBefore ← currentWritesFor? source count tableWrites
                        let mutated ← insertIndexRowIntoPages? entry.rootPage index
                          executed.row source
                        let indexDelta ← mutationPageWrites? mutated
                        let expectedBefore := tableBefore ++ indexDelta.1
                        let writes := tableWrites ++ indexDelta.2
                        if distinct : writes.Pairwise
                            (fun left right => left.pageId ≠ right.pageId) then
                          have rowsEq : after.table.rows =
                              before.table.rows ++ [executed.row] := by
                            rw [← after.represents,
                              executed.append.mutation.logicalRows]
                          have logicalIndexExact :=
                            CoreChunkPageDelta.expectedIndexEntries_append_text
                              before.table after.table index executed.row rowsEq
                              beforeText rowValue
                          have afterText :=
                            CoreChunkPageDelta.indexValuesText_append_text
                              before.table after.table index executed.row rowsEq
                              beforeText rowValue
                          have textState :
                              executed.append.after.SingleIndexValuesText :=
                            CoreWidePageState.State.singleIndexValuesText_of_exact
                              executed.append.after_tables afterIndexes afterText
                          some {
                            state := executed.append.after
                            textState
                            expectedBefore
                            writes
                            index
                            rootPage := entry.rootPage
                            logicalIndexExact
                            writesDistinct := distinct }
                        else none
                      else none
                  | _ => none
                else none
            | _ => none
          else none
        else none
      else none
    else none
  else none

/-- File-backed preparation for the same proof-carrying append.  Only the
catalog page, the changed table spine, and one routed index path are read.  In
particular this function performs no `readBinFile`, so an autocommit insert is
independent of the total database byte size when no split is required. -/
def prepareWideAppendIO? {state : CoreWidePageState.State}
    {snapshot : Option Core.Database} {tableName : String}
    {values : List Core.Value}
    (path : System.FilePath)
    (executed : CoreWidePageDelta.ExecutedInsert state snapshot tableName values)
    (stateText : state.SingleIndexValuesText) :
    IO (Option (PreparedWideAppend executed)) := do
  let firstBytes ← SyscallVFS.preadBytes path.toString 0
    (USize.ofNat PhysicalCodec.pageSize)
  unless firstBytes.size = PhysicalCodec.pageSize do return none
  let firstPage := firstBytes.toList
  let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
    return none
  let count := header.databaseSizePages.val
  let metadata ← path.metadata
  unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
      metadata.byteSize.toNat = count * PhysicalCodec.pageSize do return none
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noFree : header.freelistPageCount.val = 0 then
      -- The index mutator decodes each routed page and the write preparation
      -- subsequently asks for that page's old pre-image.  Retain the handful
      -- of pages touched by this one statement so the latter request neither
      -- issues another syscall nor converts the same 4 KiB array to a list a
      -- second time.  Page one is already in hand for the header.
      let base := preadPageSource path count
      let cache ← IO.mkRef [(1, firstPage)]
      let source : CoreDecode.IOPageSource := {
        usable := base.usable
        pageCount := base.pageCount
        readPage := fun pageNumber => do
          let retained ← cache.get
          match retained.find? (fun entry => entry.1 == pageNumber) with
          | some entry => return some entry.2
          | none =>
              let read ← base.readPage pageNumber
              match read with
              | some bytes =>
                  cache.modify ((pageNumber, bytes) :: ·)
                  return some bytes
              | none => return none }
      let some catalog := CoreDecode.decodeCatalogForOpen firstPage | return none
      let before := executed.append.table
      let after := executed.append.mutation.after
      if _sameSchema : before.table.schema = after.table.schema then
        if _sameIndexes : before.table.indexes = after.table.indexes then
          match afterIndexes : after.table.indexes with
          | [index] =>
              have beforeIndexes : before.table.indexes = [index] := by
                rw [_sameIndexes]
                exact afterIndexes
              have beforeText :=
                CoreWidePageState.State.singleIndexValuesText_exact stateText
                  executed.append.before_eq beforeIndexes
              match rowValue : executed.row.value index.column with
              | .text _ => do
                  let some entry := catalog.find? fun entry =>
                    entry.kind == "index" && entry.name == index.name &&
                      entry.table == after.table.schema.name | return none
                  if _rootRange :
                      1 < entry.rootPage ∧ entry.rootPage ≤ count then
                    let some tablePages :=
                      (match executed.append.mutation.mode with
                      | .extendedTerminalChunk =>
                          CoreWidePageCodec.encodeTerminalReplacement
                            after.table.schema after.tree
                      | .appendedChunk =>
                          CoreWidePageCodec.encodeTerminalAppend
                            after.table.schema before.tree after.tree) |
                      return none
                    let some tableWrites := tablePages.mapM
                      CoreChunkPageDelta.numberedWrite? | return none
                    let some tableBefore ←
                      currentWritesForIO? source count tableWrites | return none
                    let indexNextPage := targetPageCount count tableWrites + 1
                    let some mutated ← insertIndexRowIntoPagesIO?
                      entry.rootPage index executed.row source indexNextPage |
                        return none
                    let some indexDelta ← mutationPageWritesIO? mutated |
                      return none
                    let expectedBefore := tableBefore ++ indexDelta.1
                    let writes := tableWrites ++ indexDelta.2
                    if distinct : writes.Pairwise
                        (fun left right => left.pageId ≠ right.pageId) then
                      have rowsEq : after.table.rows =
                          before.table.rows ++ [executed.row] := by
                        rw [← after.represents,
                          executed.append.mutation.logicalRows]
                      have logicalIndexExact :=
                        CoreChunkPageDelta.expectedIndexEntries_append_text
                          before.table after.table index executed.row rowsEq
                          beforeText rowValue
                      have afterText :=
                        CoreChunkPageDelta.indexValuesText_append_text
                          before.table after.table index executed.row rowsEq
                          beforeText rowValue
                      let nextState := executed.append.after.reserveThrough
                        mutated.nextPage
                      have nextTables : nextState.tables =
                          [executed.append.mutation.after.withNextPage
                            mutated.nextPage] := by
                        simp [nextState, CoreWidePageState.State.reserveThrough,
                          executed.append.after_tables]
                      have nextIndexes :
                          (executed.append.mutation.after.withNextPage
                            mutated.nextPage).table.indexes = [index] := by
                        exact afterIndexes
                      have textState : nextState.SingleIndexValuesText :=
                        CoreWidePageState.State.singleIndexValuesText_of_exact
                          nextTables nextIndexes afterText
                      return some {
                        state := nextState
                        textState
                        expectedBefore
                        writes
                        index
                        rootPage := entry.rootPage
                        logicalIndexExact
                        writesDistinct := distinct }
                    else return none
                  else return none
              | _ => return none
          | _ => return none
        else return none
      else return none
    else return none
  else return none

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
    (input : ByteArray) (delta : CoreChunkPageDelta.StateDelta)
    (candidate : CoreChunkPageDelta.updateStateCandidate? delta.before
      delta.after.database = some delta) :
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
              match afterIndexes : after.indexes with
              | index :: previous =>
                  if _oneAdded : previous = before.indexes then
                    let tableBeforeResult ← exactOptionResult?
                      (CoreChunkPageDelta.beforeWrites delta.table)
                    let tableBefore := tableBeforeResult.value
                    let tableWritesResult ← exactOptionResult?
                      (CoreChunkPageDelta.writes delta.table)
                    let tableWrites := tableWritesResult.value
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
                        let indexWrites :=
                          (⟨0, schemaPage.storage⟩ :
                            GrowableStorage.PageWrite PhysicalCodec.pageSize) ::
                          indexPageWrites rootPage encoding.pages
                        let writes := tableWrites ++ indexWrites
                        let expectedBefore := tableBefore ++ [⟨0, oldPage⟩]
                        let state := { delta.after with
                          nextPage := newCount + 1 }
                        if distinct : writes.Pairwise
                            (fun left right => left.pageId ≠ right.pageId) then
                          if allocation : state.AllocationWellFormed then
                            if decodeBound :
                                rootPage + encoding.pages.length < 2 ^ 32 then
                              some {
                                candidate
                                state
                                index
                                rootPage
                                entry := CoreDecode.CatalogEntry.ofEncoded
                                  encoding.catalogEntry
                                entryTable := by
                                  have identity := CoreOverflow.encodeIndex_identity
                                    certified.encoded
                                  change encoding.table.schema.name =
                                    after.schema.name
                                  dsimp only [encoding]
                                  rw [identity.1]
                                entryRoot := by
                                  have identity := CoreOverflow.encodeIndex_identity
                                    certified.encoded
                                  change encoding.rootPage = rootPage
                                  dsimp only [encoding]
                                  exact identity.2.2
                                entryMetadata := by
                                  have member : index ∈ after.indexes := by
                                    rw [afterIndexes]
                                    simp
                                  have decoded := CoreDecode.decodeCanonicalIndex_encoded
                                    after index member rootPage
                                  have identity := CoreOverflow.encodeIndex_identity
                                    certified.encoded
                                  have tableEq : encoding.table = after := by
                                    simpa only [encoding] using identity.1
                                  have indexEq : encoding.index = index := by
                                    simpa only [encoding] using identity.2.1
                                  have rootEq : encoding.rootPage = rootPage := by
                                    simpa only [encoding] using identity.2.2
                                  have encodingMember :
                                      encoding.index ∈ encoding.table.indexes := by
                                    rw [tableEq, indexEq]
                                    exact member
                                  have encodingDecoded :=
                                    CoreDecode.decodeCanonicalIndex_encoded
                                      encoding.table encoding.index encodingMember
                                      encoding.rootPage
                                  change CoreDecode.decodeCanonicalIndex
                                    after.schema after.schema.name
                                    (CoreDecode.CatalogEntry.ofEncoded
                                      encoding.catalogEntry) = some index
                                  simpa [CoreOverflow.IndexEncoding.catalogEntry,
                                    tableEq, indexEq, rootEq] using encodingDecoded
                                tableExpectedBefore := tableBefore
                                tableWrites
                                tableExpectedBeforeEq := tableBeforeResult.exact
                                tableWritesEq := tableWritesResult.exact
                                certificate := .encoded certified
                                expectedBefore
                                writes
                                storage := by
                                  let oldImage := byteArrayStorageImage input
                                    count _length
                                  refine ⟨oldImage, ?_, by omega, decodeBound, ?_⟩
                                  · exact CoreLocalizedRepresentation.readsPagesFrom_applyWrites_of_covered
                                      oldImage writes distinct rootPage encoding.pages
                                      (by
                                        intro offset inBounds
                                        rcases indexPageWrites_covers rootPage
                                            encoding.pages (by omega) offset
                                            inBounds with
                                          ⟨write, member, pageNumber, bytes⟩
                                        exact ⟨write, List.mem_append.mpr (.inr
                                          (by simp [indexWrites, member])),
                                          pageNumber, bytes⟩)
                                  · have lastBound :
                                        encoding.pages.length - 1 <
                                          encoding.pages.length := by omega
                                    rcases indexPageWrites_covers rootPage
                                        encoding.pages (by omega)
                                        (encoding.pages.length - 1) lastBound with
                                      ⟨write, member, pageNumber, _⟩
                                    have present : write ∈ writes := by
                                      apply List.mem_append.mpr
                                      exact .inr (by simp [indexWrites, member])
                                    have writeBound :=
                                      CorePageSource.pageId_lt_applyWrites_of_mem
                                        oldImage present
                                    change rootPage + encoding.pages.length ≤
                                      (GrowableStorage.applyWrites oldImage writes).pageCount + 1
                                    omega
                                writesDistinct := distinct
                                allocation
                                validated := ⟨state, ()⟩ }
                            else none
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
    (input : ByteArray) (delta : CoreChunkPageDelta.StateDelta)
    (candidate : CoreChunkPageDelta.updateStateCandidate? delta.before
      delta.after.database = some delta) :
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
                          let indexDelta ← mutationPageWrites? mutated
                          let tableBeforeResult ← exactOptionResult?
                            (CoreChunkPageDelta.beforeWrites delta.table)
                          let tableBefore := tableBeforeResult.value
                          let tableWritesResult ← exactOptionResult?
                            (CoreChunkPageDelta.writes delta.table)
                          let tableWrites := tableWritesResult.value
                          let expectedBefore := tableBefore ++ indexDelta.1
                          let writes := tableWrites ++ indexDelta.2
                          let certified ← certifyDecodedIndexAt? entry.rootPage
                            after index (CorePageSource.applyWrites source writes)
                          if _tableBeforeIndex :
                                delta.table.before.tree.root.pageIds.all
                                    (fun pageId => pageId < entry.rootPage) &&
                              delta.table.after.tree.root.pageIds.all
                                    (fun pageId => pageId < entry.rootPage) then
                            if writesBounded : ∀ write ∈ writes,
                                write.pageId < count then
                              if distinct : writes.Pairwise
                                  (fun left right => left.pageId ≠ right.pageId) then
                                if allocation : delta.after.AllocationWellFormed then
                                  let entryTable ← decideProof? (entry.table =
                                    delta.table.after.table.schema.name)
                                  let entryMetadata ← decideProof?
                                    (CoreDecode.decodeCanonicalIndex
                                      delta.table.after.table.schema
                                      delta.table.after.table.schema.name entry =
                                        some index)
                                  some {
                                    candidate
                                    state := delta.after
                                    index
                                    rootPage := entry.rootPage
                                    entry
                                    entryTable := entryTable.down
                                    entryRoot := rfl
                                    entryMetadata := entryMetadata.down
                                    tableExpectedBefore := tableBefore
                                    tableWrites
                                    tableExpectedBeforeEq := tableBeforeResult.exact
                                    tableWritesEq := tableWritesResult.exact
                                    certificate := .decoded certified.certificate
                                    expectedBefore
                                    writes
                                    storage := by
                                      let oldImage := byteArrayStorageImage input
                                        count _length
                                      refine ⟨oldImage,
                                        certified.sourceExact.trans ?_⟩
                                      dsimp only [source, oldImage]
                                      rw [byteArrayPageSource_eq_storageImage
                                        input count _length]
                                      apply CorePageSource.applyWrites_ofStorageImage
                                      intro write member
                                      simpa [oldImage, byteArrayStorageImage] using
                                        writesBounded write member
                                    writesDistinct := distinct
                                    allocation
                                    validated := ⟨delta.after, ()⟩ }
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
    else none
  else none

/-- Delete a set of rows from the one tail-owned generated secondary index by
descending only through pages that contain those entries. No index sort,
pagination, or whole-index encoding occurs. A promoted interior entry is
replaced by the greatest entry of its left subtree, so SQLite's promoted-key
semantics are preserved without duplication. Any overflow, page-fit, routing,
or allocation miss returns `none` and retains the certified rebuild path. -/
def preparePageDirectedIndexDelete? (validated : ValidatedOpenState)
    (input : ByteArray) (delta : CoreChunkPageDelta.StateDelta)
    (candidate : CoreChunkPageDelta.updateStateCandidate? delta.before
      delta.after.database = some delta) :
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
                        let indexDelta ← mutationPageWrites? mutated
                        let tableBeforeResult ← exactOptionResult?
                          (CoreChunkPageDelta.beforeWrites delta.table)
                        let tableBefore := tableBeforeResult.value
                        let tableWritesResult ← exactOptionResult?
                          (CoreChunkPageDelta.writes delta.table)
                        let tableWrites := tableWritesResult.value
                        let expectedBefore := tableBefore ++ indexDelta.1
                        let writes := tableWrites ++ indexDelta.2
                        let certified ← certifyDecodedIndexAt? entry.rootPage
                          after index (CorePageSource.applyWrites source writes)
                        if _tableBeforeIndex :
                              delta.table.before.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) &&
                            delta.table.after.tree.root.pageIds.all
                                  (fun pageId => pageId < entry.rootPage) then
                          if writesBounded : ∀ write ∈ writes,
                              write.pageId < count then
                            if distinct : writes.Pairwise
                                (fun left right => left.pageId ≠ right.pageId) then
                              if allocation : delta.after.AllocationWellFormed then
                                let entryTable ← decideProof? (entry.table =
                                  delta.table.after.table.schema.name)
                                let entryMetadata ← decideProof?
                                  (CoreDecode.decodeCanonicalIndex
                                    delta.table.after.table.schema
                                    delta.table.after.table.schema.name entry =
                                      some index)
                                some {
                                  candidate
                                  state := delta.after
                                  index
                                  rootPage := entry.rootPage
                                  entry
                                  entryTable := entryTable.down
                                  entryRoot := rfl
                                  entryMetadata := entryMetadata.down
                                  tableExpectedBefore := tableBefore
                                  tableWrites
                                  tableExpectedBeforeEq := tableBeforeResult.exact
                                  tableWritesEq := tableWritesResult.exact
                                  certificate := .decoded certified.certificate
                                  expectedBefore
                                  writes
                                  storage := by
                                    let oldImage := byteArrayStorageImage input
                                      count _length
                                    refine ⟨oldImage,
                                      certified.sourceExact.trans ?_⟩
                                    dsimp only [source, oldImage]
                                    rw [byteArrayPageSource_eq_storageImage
                                      input count _length]
                                    apply CorePageSource.applyWrites_ofStorageImage
                                    intro write member
                                    simpa [oldImage, byteArrayStorageImage] using
                                      writesBounded write member
                                  writesDistinct := distinct
                                  allocation
                                  validated := ⟨delta.after, ()⟩ }
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
  else none

/-- Tail replacement is safe only when the old canonical index occupies
exactly that physical interval. A last catalog root can still have children
below it, notably after a wide-tree root split. Such layouts must be rebuilt. -/
def pageWriteContents (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :
    List (Nat × Array UInt8) := writes.map (fun write => (write.pageId, write.page.bytes))

def indexTailMatches (source : CoreDecode.PageSource) (rootPage : Nat)
    (pages : List CoreFile.Page) : Bool :=
  pages.length == source.pageCount + 1 - rootPage &&
    (readPageWrites? source rootPage pages.length).map pageWriteContents ==
      some (pageWriteContents (indexPageWrites rootPage pages))

theorem indexTailMatches_exact {source : CoreDecode.PageSource} {rootPage : Nat}
    {pages : List CoreFile.Page} (accepted : indexTailMatches source rootPage pages = true) :
    pages.length = source.pageCount + 1 - rootPage ∧
      (readPageWrites? source rootPage pages.length).map pageWriteContents =
        some (pageWriteContents (indexPageWrites rootPage pages)) := by
  simpa [indexTailMatches, Bool.and_eq_true] using accepted

/-- Localize one changed generated index when it owns the final file interval.
The validating-open capability records that the old index matched the logical
pre-state; the replacement is the ordinary proved index encoder rooted at the
same page. Every page after the shorter replacement becomes freelist space.
General files, multiple changed indexes, non-tail ownership, or replacement
indexes that exceed the old tail return `none` and keep the full compatibility
commit. -/
def prepareLocalizedLastIndex? (validated : ValidatedOpenState)
    (input : List UInt8)
    (delta : CoreChunkPageDelta.StateDelta)
    (candidate : CoreChunkPageDelta.updateStateCandidate? delta.before
      delta.after.database = some delta) :
    Option (LocalizedLastIndexDelta delta) := do
  let (header, _) ← FileFormat.decodeDatabaseHeader input
  let count := header.databaseSizePages.val
  if _generated : CoreFile.hasGeneratedImageStamp header then
    if _noExistingFree : header.freelistPageCount.val = 0 then
      if _length : input.length = count * PhysicalCodec.pageSize then
        let inputBytes := ByteArray.mk input.toArray
        have inputBytesSize : inputBytes.size =
            count * PhysicalCodec.pageSize := by
          simpa only [inputBytes, ByteArray.size, List.size_toArray] using _length
        let source := byteArrayPageSource inputBytes count
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
                      let prior ← certifyIndexEncoding? entry.rootPage before index
                      unless indexTailMatches source entry.rootPage prior.value.pages do none
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
                          let tableBeforeResult ← exactOptionResult?
                            (CoreChunkPageDelta.beforeWrites delta.table)
                          let tableBefore := tableBeforeResult.value
                          let tableWritesResult ← exactOptionResult?
                            (CoreChunkPageDelta.writes delta.table)
                          let tableWrites := tableWritesResult.value
                          if tableWritesBounded : ∀ write ∈ tableWrites,
                              write.pageId + 1 < entry.rootPage then
                            let oldTailRun ← readPageWritesCertified? source
                              entry.rootPage oldCount
                            let oldTail := oldTailRun.writes
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
                            if decodeBound : entry.rootPage +
                                encoding.pages.length < 2 ^ 32 then
                              if distinct : writes.Pairwise
                                  (fun left right => left.pageId ≠ right.pageId) then
                                if allocation : state.AllocationWellFormed then
                                  let entryTable ← decideProof? (entry.table =
                                    delta.table.after.table.schema.name)
                                  let entryMetadata ← decideProof?
                                    (CoreDecode.decodeCanonicalIndex
                                      delta.table.after.table.schema
                                      delta.table.after.table.schema.name entry =
                                        some index)
                                  some {
                                  candidate
                                  state
                                  index
                                  rootPage := entry.rootPage
                                  entry
                                  entryTable := entryTable.down
                                  entryRoot := rfl
                                  entryMetadata := entryMetadata.down
                                  tableExpectedBefore := tableBefore
                                  tableWrites
                                  tableExpectedBeforeEq := tableBeforeResult.exact
                                  tableWritesEq := tableWritesResult.exact
                                  certificate := .encoded certified
                                  expectedBefore
                                  writes
                                  storage := by
                                    let oldImage := byteArrayStorageImage inputBytes
                                      count inputBytesSize
                                    refine ⟨oldImage, ?_, by omega, decodeBound, ?_⟩
                                    · apply CoreLocalizedRepresentation.readsPagesFrom_applyWrites
                                        oldImage writes distinct entry.rootPage
                                        encoding.pages
                                      intro offset inBounds
                                      rcases indexPageWrites_covers entry.rootPage
                                          encoding.pages (by omega) offset inBounds with
                                        ⟨candidate, candidateMember, candidatePage,
                                          candidateBytes⟩
                                      by_cases changed : candidate ∈ indexWrites
                                      · exact .inl ⟨candidate, by simp [writes, changed],
                                          candidatePage, candidateBytes⟩
                                      · rcases omitted_changedPageWrites_matches
                                            candidateMember changed with
                                          ⟨old, oldMember, oldSameId, oldSamePage⟩
                                        refine .inr ⟨by omega, ?_, ?_, ?_⟩
                                        · change entry.rootPage + offset ≤ count
                                          omega
                                        · have oldRead := readPageWrites?_reads source
                                              (by omega) oldTailRun.exact old oldMember
                                          have sourceRead : source.readPage
                                              (entry.rootPage + offset) =
                                                some (encoding.pages.get
                                                  ⟨offset, inBounds⟩).bytes := by
                                            rw [← candidatePage, ← oldSameId, oldRead,
                                              oldSamePage, candidateBytes]
                                          rw [← byteArrayPageSource_eq_storageImage
                                            inputBytes count inputBytesSize]
                                          exact sourceRead
                                        · intro write writeMember samePage
                                          rcases List.mem_append.mp writeMember with
                                            tableMember | indexMember
                                          · have beforeRoot := tableWritesBounded write
                                                tableMember
                                            omega
                                          · have fullMember : write ∈
                                                indexPageWrites entry.rootPage
                                                  encoding.pages :=
                                              (changedPageWrites_sublist oldTail
                                                (indexPageWrites entry.rootPage
                                                  encoding.pages)).subset indexMember
                                            have sameId : write.pageId =
                                                candidate.pageId := by omega
                                            have equal := indexPageWrites_eq_of_pageId_eq
                                              entry.rootPage encoding.pages
                                                (by omega) fullMember
                                                candidateMember sameId
                                            exact changed (by simpa [equal] using indexMember)
                                    · have growth :=
                                          CorePageSource.applyWrites_pageCount_ge
                                            oldImage writes
                                      have oldCountExact : oldImage.pageCount = count := rfl
                                      rw [oldCountExact] at growth
                                      change entry.rootPage + encoding.pages.length ≤
                                        (GrowableStorage.applyWrites oldImage writes).pageCount + 1
                                      omega
                                  writesDistinct := distinct
                                  allocation
                                  validated := ⟨state, ()⟩ }
                                else none
                              else none
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
  | text (certificate : CoreDecode.CertifiedWideTextIndex
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
  | .text certificate => certificate.valueEntries target
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
  | text certificate => exact certificate.valueEntries_exact target
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
  | .text certificate => certificate.rangeEntries operation target
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
  | text certificate => exact certificate.rangeEntries_exact operation target
  | allValues certificate => exact certificate.rangeEntries_exact operation target

/-- A certificate retained by a live connection.  Its dependent proof ties a
specific physical page source to the exact logical entries of `table/index`.
The connection invalidates these values on mutation until localized
certificate maintenance is implemented. -/
structure StoredIntegerIndex (database : Core.Database) where
  table : Core.Table
  tableMember : table ∈ database.tables
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
def StoredIntegerIndex.retarget {before : Core.Database}
    (stored : StoredIntegerIndex before) (database : Core.Database)
    (table : Core.Table) (tableMember : table ∈ database.tables)
    (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) : StoredIntegerIndex database := {
  table
  tableMember
  index
  source := stored.source
  fuel := stored.fuel
  rootPage := stored.rootPage
  expected := stored.expected
  expected_eq := sameExpected.symm
  certificate := stored.certificate }

@[simp] theorem StoredIntegerIndex.retarget_expected
    {before : Core.Database} (stored : StoredIntegerIndex before)
    (database : Core.Database) (table : Core.Table)
    (tableMember : table ∈ database.tables) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) :
    (stored.retarget database table tableMember index sameExpected).expected =
      stored.expected := rfl

theorem StoredIntegerIndex.retarget_value_exact
    {before : Core.Database} (stored : StoredIntegerIndex before)
    (database : Core.Database) (table : Core.Table)
    (tableMember : table ∈ database.tables) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) (target : Core.Value) :
    (stored.retarget database table tableMember index sameExpected).certificate.valueEntries target =
      (CoreDecode.expectedIndexEntries table index).filter
        (fun entry => entry.matchesValue target) := by
  change stored.certificate.valueEntries target = _
  rw [stored.certificate.valueEntries_exact, sameExpected]

theorem StoredIntegerIndex.retarget_range_exact
    {before : Core.Database} (stored : StoredIntegerIndex before)
    (database : Core.Database) (table : Core.Table)
    (tableMember : table ∈ database.tables) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) (operation : PhysicalQuery.Comparison)
    (target : Core.Value) :
    (stored.retarget database table tableMember index sameExpected).certificate.rangeEntries
        operation target =
      (CoreDecode.expectedIndexEntries table index).filter
        (fun entry => entry.matchesRange operation target) := by
  change stored.certificate.rangeEntries operation target = _
  rw [stored.certificate.rangeEntries_exact, sameExpected]

/-- Checked certificate maintenance for a localized table mutation.  Schema,
index identity and the complete logical index image must all agree. -/
def StoredIntegerIndex.retarget? {before : Core.Database}
    (stored : StoredIntegerIndex before) (database : Core.Database) :
    Option (StoredIntegerIndex database) :=
  match found : database.findTable? stored.table.schema.name with
  | none => none
  | some table =>
      have tableMember : table ∈ database.tables :=
        database.findTable?_mem found
      if _sameSchema : table.schema = stored.table.schema then
        match table.indexes.find? fun candidate =>
            candidate.name == stored.index.name with
        | none => none
        | some index =>
            if _sameIndex : index = stored.index then
              if sameExpected : CoreDecode.expectedIndexEntries table index =
                  stored.expected then
                some (stored.retarget database table tableMember index
                  sameExpected)
              else none
            else none
      else none

def retargetIntegerIndexCertificates
    {before : Core.Database}
    (certificates : List (StoredIntegerIndex before))
    (database : Core.Database) : List (StoredIntegerIndex database) :=
  certificates.filterMap fun stored => stored.retarget? database

def certifyIntegerIndexes (physicalPages : List (List UInt8))
    (catalog : List CoreDecode.CatalogEntry) (database : Core.Database) :
    List (StoredIntegerIndex database) :=
  let source := CoreDecode.PageSource.ofList physicalPages
  let fuel := physicalPages.length + 1
  database.tables.attach.flatMap fun attached =>
    let table := attached.val
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
                  match CoreDecode.certifyWideTextIndex source fuel
                      catalogEntry.rootPage expected with
                  | none =>
                      match CoreDecode.certifyAllValueIndex source fuel
                          catalogEntry.rootPage expected with
                      | none => none
                      | some certificate =>
                          some ⟨table, attached.property, index, source, fuel,
                            catalogEntry.rootPage,
                            expected, rfl, .allValues certificate⟩
                  | some certificate =>
                      some ⟨table, attached.property, index, source, fuel,
                        catalogEntry.rootPage,
                        expected, rfl, .text certificate⟩
              | some certificate =>
                  some ⟨table, attached.property, index, source, fuel,
                    catalogEntry.rootPage,
                    expected, rfl, .general certificate⟩
          | some certificate =>
              some ⟨table, attached.property, index, source, fuel,
                catalogEntry.rootPage,
                expected, rfl, .generated certificate⟩

def loadIntegerIndexCertificates (paths : Paths) (database : Core.Database) :
    IO (List (StoredIntegerIndex database)) := do
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
    List.pairwise_mergeSort rowidLeTrans rowidLeTotal candidates
  have tableSorted : (table.rows.filter keepRow).Pairwise
      (fun left right => rowidLe left right = true) := by
    have strict := table.rowsWellFormed.2.filter keepRow
    exact strict.imp fun less => by
      simp only [rowidLe, decide_eq_true_eq]
      exact Int.le_of_lt less
  unfold rowsForIndexEntries
  change candidates.mergeSort rowidLe = table.rows.filter keepRow
  apply candidatePerm.eq_of_pairwise _ candidatesSorted tableSorted
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
    Core.Predicate.eval, Core.indexColumnMatches] <;> rfl

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
    Core.Predicate.eval] <;> rfl

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

def certifiedEqualityCandidates {database : Core.Database}
    (stored : StoredIntegerIndex database)
    (table : Core.Table) (query : Core.Query) (target : Core.Value)
    (sameTable : stored.table = table)
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
    have rowsEqual : stored.table.rows = table.rows :=
      congrArg Core.Table.rows sameTable
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

def certifiedRangeCandidates {database : Core.Database}
    (stored : StoredIntegerIndex database)
    (table : Core.Table) (query : Core.Query)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (sameTable : stored.table = table)
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
    have rowsEqual : stored.table.rows = table.rows :=
      congrArg Core.Table.rows sameTable
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

def lookupCertifiedIndexCandidates {database : Core.Database}
    (certificates : List (StoredIntegerIndex database))
    (table : Core.Table) (tableMember : table ∈ database.tables)
    (query : Core.Query) :
    Option (CertifiedCandidates table query) :=
  match predicateResult : query.predicate with
  | some (.equal column target) =>
      match table.chooseAccessPath query.predicate with
      | .equalityIndex index =>
          if columnEqual : column = index.column then
            match storedResult : certificates.find? fun stored =>
                stored.table.schema.name == table.schema.name &&
                  stored.index.name == index.name with
            | none => none
            | some stored =>
                if indexEqual : stored.index = index then
                  have storedName : stored.table.schema.name =
                      table.schema.name := by
                    have selected := List.find?_some storedResult
                    simp only [Bool.and_eq_true, beq_iff_eq] at selected
                    exact selected.1
                  have sameTable : stored.table = table :=
                    database.table_eq_of_mem_of_name_eq stored.tableMember
                      tableMember storedName
                  have predicateEqual : query.predicate =
                      some (.equal stored.index.column target) := by
                    calc
                      query.predicate = some (.equal column target) :=
                        predicateResult
                      _ = some (.equal stored.index.column target) := by
                        simp [indexEqual, columnEqual]
                  some (certifiedEqualityCandidates stored table query target
                    sameTable predicateEqual)
                else none
          else none
      | _ => none
  | some (.compare operation column target) =>
      match table.chooseAccessPath query.predicate with
      | .rangeIndex index =>
          if columnEqual : column = index.column then
            match storedResult : certificates.find? fun stored =>
                stored.table.schema.name == table.schema.name &&
                  stored.index.name == index.name with
            | none => none
            | some stored =>
                if indexEqual : stored.index = index then
                  have storedName : stored.table.schema.name =
                      table.schema.name := by
                    have selected := List.find?_some storedResult
                    simp only [Bool.and_eq_true, beq_iff_eq] at selected
                    exact selected.1
                  have sameTable : stored.table = table :=
                    database.table_eq_of_mem_of_name_eq stored.tableMember
                      tableMember storedName
                  have predicateEqual : query.predicate =
                      some (.compare operation stored.index.column target) := by
                    calc
                      query.predicate =
                          some (.compare operation column target) :=
                        predicateResult
                      _ = some (.compare operation stored.index.column target) := by
                        simp [indexEqual, columnEqual]
                  some (certifiedRangeCandidates stored table query operation
                    target sameTable predicateEqual)
                else none
          else none
      | _ => none
  | _ => none

/-- Page count and catalog for a validated main file.

Used by the persisted-index lookup below, which reads the catalog and only
value-compatible index branches; returned rowids are projected back into table
order so queries without ORDER BY retain Core's observable list semantics.
Unsupported query shapes return `none`.

Split out of `lookupIndexCandidates` so a connection can decode it once instead
of once per statement. Reading page zero and decoding the header and catalog is
per-query fixed cost that does not change until a write, and writes already
invalidate the connection's caches. -/
structure FileGeometry where
  pageCount : Nat
  catalog : List CoreDecode.CatalogEntry

/-- Header/catalog facts checked once for a read-only batch over a stamped
Lean-generated image.  Reusing this value does not cache mutable table pages;
it only removes repeated file opens and repeated catalog decoding while the
outer process lock keeps the batch image stable. -/
structure GeneratedFileGeometry where
  pageCount : Nat
  catalog : List CoreDecode.CatalogEntry
  schemas : List (String × Core.Schema)

def readGeneratedFileGeometry (paths : Paths) :
    IO (Option GeneratedFileGeometry) := do
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
    let schemas := catalog.filterMap fun entry =>
      if entry.kind == "table" then do
        let sql ← entry.sql
        let schema ← CoreDecode.parseTableSchema sql
        if schema.name = entry.name then some (entry.name, schema) else none
      else none
    return some ⟨count, catalog, schemas⟩

def GeneratedFileGeometry.tableSchema? (geometry : GeneratedFileGeometry)
    (tableName : String) : Option Core.Schema := do
  let entry ← geometry.schemas.find? fun entry => entry.1 == tableName
  some entry.2

/-- Primary-key counterpart of the generated secondary-index reader. The
caller retains the generated geometry and bounded byte-page cache for one
immutable, process-locked read batch. Use the same routed byte reader already
used to resolve secondary-index rowids: it decodes the selected record rather
than every record in its leaf. Foreign images continue through
`lookupPrimaryRowDecision`, including its full local decoding checks.

Neither geometry nor cache may be reused across a write. A malformed routed
page or an invalid selected row is an optimization miss, not a successful
empty result. Only a valid leaf miss returns `some none`. -/
def lookupGeneratedPrimaryRowWith (geometry : GeneratedFileGeometry)
    (paths : Paths) (tableName : String) (schema : Core.Schema)
    (cache : PageReadCache) (target : Core.Integer) :
    IO (Option (Option Core.Row)) := do
  let some tableEntry := geometry.catalog.find? fun entry =>
    entry.kind == "table" && entry.name == tableName | return none
  let some decodedSchema := geometry.tableSchema? tableName | return none
  unless decodedSchema = schema do return none
  let source := preadPageSourceCached paths.main geometry.pageCount cache
  let some result ← lookupTableRowidBytesCached paths.main schema source cache
      target (geometry.pageCount + 1) tableEntry.rootPage | return none
  match result with
  | none => return some none
  | some row =>
      unless row.rowid = target && row.WellFormed schema do return none
      return some (some row)

/-- Validate the header and decode the catalog. The header checks are exactly
those `lookupIndexCandidates` performed inline, so a cached geometry carries the
same premises a fresh read would. -/
def readFileGeometry (paths : Paths) : IO (Option FileGeometry) := do
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
    return some ⟨count, catalog⟩

/-- The index selected by a query's predicate, or `none` for shapes this path
does not serve. -/
private def selectedIndexTarget (table : Core.Table) (query : Core.Query) :
    Option (Core.Index × IndexLookupTarget) :=
  match query.predicate, table.chooseAccessPath query.predicate with
  | some (.equal column target), .equalityIndex index =>
      if column = index.column then
        some (index, IndexLookupTarget.equality target)
      else none
  | some (.compare operation column target), .rangeIndex index =>
      if column = index.column then
        some (index, IndexLookupTarget.range operation target)
      else none
  | _, _ => none

/-- Index lookup against an already-decoded geometry. -/
def lookupIndexCandidatesWith (geometry : FileGeometry) (paths : Paths)
    (table : Core.Table) (query : Core.Query) : IO (Option IndexLookup) := do
  let some (index, target) := selectedIndexTarget table query | return none
  let some entry := geometry.catalog.find? fun entry =>
    entry.kind == "index" && entry.name == index.name &&
      entry.table == table.schema.name | return none
  let count := geometry.pageCount
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

def lookupIndexCandidates (paths : Paths) (table : Core.Table)
    (query : Core.Query) : IO (Option IndexLookup) := do
  let some geometry ← readFileGeometry paths | return none
  lookupIndexCandidatesWith geometry paths table query

/-- Recognize exactly the two index-catalog shapes emitted by the certified
encoder. Explicit indexes carry the canonical proof marker in their SQL text;
SQLite's required automatic index for a non-aliasing primary key has NULL SQL,
so its certificate is instead the canonical name/column pair derived from the
decoded table schema. The generated-image stamp remains the outer provenance
gate for both cases. -/
private def generatedIndexEntryMatches (schema : Core.Schema)
    (tableName : String) (column : Nat) (columnName : String)
    (entry : CoreDecode.CatalogEntry) : Bool :=
  entry.kind == "index" && entry.table == tableName &&
    match entry.sql with
    | some sql =>
        match CanonicalIndexSQL.parseGeneratedCertified sql with
        | some spec => spec.name == entry.name && spec.table == tableName &&
            spec.column == columnName
        | none => false
    | none =>
        Core.Index.isImplicitPrimary schema { name := entry.name, column }

/-- Cold secondary-index lookup for a stamped image emitted by the proved
encoder. The exact canonical catalog suffix records the INTEGER-only premise
of `lookupIndexValueFrom_encodeIndex_exact` and
`lookupIndexRangeFrom_encodeIndex_exact`. Only selected index branches and
the corresponding primary-tree paths are read; every returned rowid/value
link is checked locally before it reaches SQL evaluation. -/
def lookupGeneratedIndexCandidatesWith (geometry : GeneratedFileGeometry)
    (paths : Paths) (tableName : String)
    (schema : Core.Schema) (query : Core.Query)
    (cache : Option PageReadCache := none) : IO (Option IndexLookup) := do
  let selected := match query.predicate with
    | some (.equal column target) =>
        some (column, IndexLookupTarget.equality target)
    | some (.compare operation column target) =>
        some (column, IndexLookupTarget.range operation target)
    | _ => none
  let some (column, target) := selected | return none
  let some columnSpec := schema.columns[column]? | return none
  let count := geometry.pageCount
  let some tableEntry := geometry.catalog.find? fun entry =>
    entry.kind == "table" && entry.name == tableName | return none
  let some decodedSchema := geometry.tableSchema? tableName | return none
  unless decodedSchema = schema do return none
  let some indexEntry := geometry.catalog.find? (generatedIndexEntryMatches schema
    tableName column columnSpec.name) | return none
  let reads ← IO.mkRef 0
  let base := match cache with
    | some cache => preadPageSourceCached paths.main count cache
    | none => preadPageSource paths.main count
  let source : CoreDecode.IOPageSource := {
    pageCount := count
    readPage := fun pageNumber => do
      reads.modify (· + 1)
      base.readPage pageNumber }
  let entries ← match target with
    | .equality value =>
        match cache with
        | some cache =>
            CoreDecode.lookupIndexValueDecodedWith
              (decodedIndexPageCached cache source) value
              (count + 1) indexEntry.rootPage
        | none =>
            CoreDecode.lookupIndexValueIOFrom source value (count + 1)
              indexEntry.rootPage
    | .range operation value =>
        CoreDecode.lookupIndexRangeIOFrom source operation value
          (count + 1) indexEntry.rootPage
  let some entries := entries | return none
  let mut candidates := []
  for entry in entries do
    let resolve : IO (Option (Option Core.Row)) := match cache with
      | some retained =>
          lookupTableRowidBytesCached paths.main schema source retained
            entry.rowid (count + 1) tableEntry.rootPage
      | none =>
          CoreDecode.lookupTableRowidTargetIOFrom schema source entry.rowid
            (count + 1) tableEntry.rootPage
    let resolved ← resolve
    let some resolved := resolved | return none
    let some row := resolved | return none
    unless row.rowid = entry.rowid && row.WellFormed schema &&
        row.value column = entry.value do return none
    candidates := row :: candidates
  return some ⟨candidates.mergeSort rowidLe, ← reads.get⟩

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

private def activatePersistentJournal (syncOps : SyncOps) (paths : Paths)
    (journal : PhysicalJournalCodec.PersistentEncodable) : IO Unit := do
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

def commit (syncOps : SyncOps) (paths : Paths) (new : Core.Database) :
    IO (ValidatedOpenState × List (POSIXVFS.Request PhysicalCodec.pageSize)) := do
  recoverInPlace syncOps paths
  let current ← IO.FS.readBinFile paths.main
  let oldImage ← match physicalImage? current.data.toList with
    | some image => pure image
    | none => throw (IO.userError "could not page the current general MVP image")
  -- The pure preparation retains the exact encoder branch and write equation
  -- later consumed by `PreparedBulkCommit.postImageCertificate`; syscalls do
  -- not recompute or reinterpret either choice.
  let prepared ← match prepareBulkCommit? oldImage new with
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

end CoreFileAdapter
end SQLeanite
