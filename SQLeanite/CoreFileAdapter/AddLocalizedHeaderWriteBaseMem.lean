import SQLeanite.CoreFileAdapter.Paths
import SQLeanite.CoreLocalizedRepresentation.TableOnSource

namespace SQLeanite
namespace CoreFileAdapter

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
def prepareLocalizedWrites (path : System.FilePath)
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

def journalFromFile (path : System.FilePath)
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

def verifyWrittenPages (path : System.FilePath)
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

end CoreFileAdapter

end SQLeanite
