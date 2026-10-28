import SQLeanite.PageFormat.BTreeCellBodyPageType

namespace SQLeanite
namespace FileFormat

/-- A complete physical write set with exactly one distinguished SQLite page
one and no conflicting pager ids across the remaining verified pages. -/
structure VerifiedDatabasePageSet (usable : UsablePageSize) (pageCount : Nat) where
  firstPage : DatabaseFirstPage usable pageCount
  otherPages : VerifiedPageSet usable pageCount
  pageIdsNodup :
    ((firstPage.toPageWrite :: otherPages.writes).map
      (fun write => write.pageId)).Nodup
  deriving DecidableEq

def VerifiedDatabasePageSet.writes
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedDatabasePageSet usable pageCount) :
    List (Storage.PageWrite usable.val pageCount) :=
  pages.firstPage.toPageWrite :: pages.otherPages.writes

theorem VerifiedDatabasePageSet.writes_nonempty
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedDatabasePageSet usable pageCount) : pages.writes ≠ [] := by
  simp [VerifiedDatabasePageSet.writes]

theorem VerifiedDatabasePageSet.first_write_pageId
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedDatabasePageSet usable pageCount) :
    pages.writes.head?.map (fun write => write.pageId.val) = some 0 := by
  simp [VerifiedDatabasePageSet.writes, DatabaseFirstPage.toPageWrite_pageId]

theorem VerifiedDatabasePageSet.applyWrites_read_first
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedDatabasePageSet usable pageCount)
    (old : Storage.Disk usable.val pageCount) :
    (Storage.applyWrites old pages.writes).read
        pages.firstPage.toPageWrite.pageId = pages.firstPage.encodePage := by
  have firstNotInOther :
      pages.firstPage.toPageWrite.pageId ∉
        pages.otherPages.writes.map (fun write => write.pageId) :=
    (List.nodup_cons.mp pages.pageIdsNodup).1
  unfold VerifiedDatabasePageSet.writes Storage.applyWrites
  simp only [List.foldl_cons]
  change
    (Storage.applyWrites
      (old.write pages.firstPage.toPageWrite.pageId
        pages.firstPage.toPageWrite.page)
      pages.otherPages.writes).read pages.firstPage.toPageWrite.pageId = _
  rw [Storage.applyWrites_read_of_not_written]
  · simp [DatabaseFirstPage.toPageWrite]
  · intro write member equal
    apply firstNotInOther
    exact List.mem_map.mpr ⟨write, member, equal.symm⟩

theorem VerifiedDatabasePageSet.rollbackCommit_crash_atomic
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedDatabasePageSet usable pageCount)
    (old : Storage.Disk usable.val pageCount) (phase : Storage.CommitPhase)
    (recoveredMain : Storage.Disk usable.val pageCount)
    (recoveredJournal : Option (Storage.Disk usable.val pageCount))
    (outcome : Storage.JournaledCrashOutcome
      (Storage.rollbackCommitState old pages.writes phase)
      recoveredMain recoveredJournal) :
    Storage.recoverWithJournal recoveredMain recoveredJournal = old ∨
      Storage.recoverWithJournal recoveredMain recoveredJournal =
        Storage.applyWrites old pages.writes := by
  exact Storage.rollbackCommit_crash_atomic old pages.writes phase
    recoveredMain recoveredJournal outcome

structure DecodedTypedBTreeCell (usable : UsablePageSize)
    (pageType : BTreePageType) where
  body : BTreeCellBody usable
  matchesPage : body.pageType = pageType
  deriving DecidableEq

def decodeTypedBTreeCell (usable : UsablePageSize) :
    (pageType : BTreePageType) → List UInt8 →
      Option (DecodedTypedBTreeCell usable pageType × List UInt8)
  | .interiorTable, input => do
    let (cell, suffix) ← decodeInteriorTableCell input
    some (⟨.interiorTable cell, rfl⟩, suffix)
  | .leafTable, input => do
    let (cell, suffix) ← decodeTableLeafCell usable input
    some (⟨.leafTable cell, rfl⟩, suffix)
  | .interiorIndex, input => do
    let (cell, suffix) ← decodeInteriorIndexCell usable input
    some (⟨.interiorIndex cell, rfl⟩, suffix)
  | .leafIndex, input => do
    let (cell, suffix) ← decodeLeafIndexCell usable input
    some (⟨.leafIndex cell, rfl⟩, suffix)

structure DecodedBTreeCells (usable : UsablePageSize)
    (pageType : BTreePageType) (count : Nat) where
  cells : List (DecodedTypedBTreeCell usable pageType)
  length_eq : cells.length = count
  deriving DecidableEq

def decodeCellsAtPointers (usable : UsablePageSize) (pageType : BTreePageType)
    (pageBytes : List UInt8) : (pointers : List U16Value) →
    Option (DecodedBTreeCells usable pageType pointers.length)
  | [] => some ⟨[], rfl⟩
  | pointer :: pointers => do
    let (cell, _) ← decodeTypedBTreeCell usable pageType
      (pageBytes.drop pointer.val)
    let cells ← decodeCellsAtPointers usable pageType pageBytes pointers
    some ⟨cell :: cells.cells, by simp [cells.length_eq]⟩

def decodeBTreePageCells {usable : UsablePageSize}
    (pagePrefix : BTreePagePrefix usable.val) (page : Storage.Page usable.val) :
    Option (DecodedBTreeCells usable pagePrefix.header.header.pageType
      pagePrefix.pointers.values.length) :=
  decodeCellsAtPointers usable pagePrefix.header.header.pageType
    page.bytes.toList pagePrefix.pointers.values

theorem decodeBTreePageCells_cellCount {usable : UsablePageSize}
    (pagePrefix : BTreePagePrefix usable.val) (page : Storage.Page usable.val)
    (cells : DecodedBTreeCells usable pagePrefix.header.header.pageType
      pagePrefix.pointers.values.length)
    (_decoded : decodeBTreePageCells pagePrefix page = some cells) :
    cells.cells.length = pagePrefix.header.header.common.cellCount.val := by
  rw [cells.length_eq, pagePrefix.pointers.length_eq]

end FileFormat

end SQLeanite
