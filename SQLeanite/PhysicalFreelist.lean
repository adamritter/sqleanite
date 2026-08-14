import SQLeanite.PhysicalMultiPageCodec

namespace SQLeanite
namespace PhysicalFreelist

open FileFormat
open PhysicalCodec

def maxFreelistPages : Nat := PhysicalCodec.pageSize / 4 - 1

structure Layout where
  tree : PhysicalTableBTree.Tree
  totalPageCount : Nat
  active_le_total : PhysicalMultiPageCodec.filePageCount tree ≤ totalPageCount
  total_fits : totalPageCount < 2 ^ 32
  free_fits : totalPageCount - PhysicalMultiPageCodec.filePageCount tree ≤ maxFreelistPages

def Layout.activePageCount (layout : Layout) : Nat :=
  PhysicalMultiPageCodec.filePageCount layout.tree

def Layout.freePageCount (layout : Layout) : Nat :=
  layout.totalPageCount - layout.activePageCount

def ofTreeTotal? (tree : PhysicalTableBTree.Tree) (totalPageCount : Nat) : Option Layout :=
  if enough : PhysicalMultiPageCodec.filePageCount tree ≤ totalPageCount then
    if totalFits : totalPageCount < 2 ^ 32 then
      if freeFits : totalPageCount - PhysicalMultiPageCodec.filePageCount tree ≤
          maxFreelistPages then
        some ⟨tree, totalPageCount, enough, totalFits, freeFits⟩
      else none
    else none
  else none

def Layout.databaseHeader (layout : Layout) : DatabaseHeader :=
  let free := layout.freePageCount
  { PhysicalCodec.databaseHeader with
    databaseSizePages := ⟨layout.totalPageCount, layout.total_fits⟩
    firstFreelistTrunk := if positive : 0 < free then
      ⟨layout.activePageCount + 1, by
        have activePositive := PhysicalMultiPageCodec.filePageCount_pos layout.tree
        have below : layout.activePageCount + 1 ≤ layout.totalPageCount := by
          change 0 < layout.totalPageCount - layout.activePageCount at positive
          omega
        exact Nat.lt_of_le_of_lt below layout.total_fits⟩
      else ⟨0, by omega⟩
    freelistPageCount := ⟨free, by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) layout.total_fits⟩ }

def Layout.schemaPageBytes (layout : Layout) : List UInt8 :=
  encodeDatabaseHeader layout.databaseHeader ++ PhysicalMultiPageCodec.schemaPageBody

theorem Layout.schemaPageBytes_length (layout : Layout) :
    layout.schemaPageBytes.length = PhysicalCodec.pageSize := by
  rw [Layout.schemaPageBytes, List.length_append, encodeDatabaseHeader_length,
    PhysicalMultiPageCodec.schemaPageBody_length]
  simp [PhysicalCodec.pageSize]

def Layout.schemaPage (layout : Layout) : Storage.Page PhysicalCodec.pageSize := {
  bytes := layout.schemaPageBytes.toArray
  sizeInvariant := by simp [layout.schemaPageBytes_length] }

def encodePageNumbers (numbers : List Nat) : List UInt8 :=
  numbers.flatMap (encodeUnsignedFixed 4)

theorem encodePageNumbers_length (numbers : List Nat) :
    (encodePageNumbers numbers).length = 4 * numbers.length := by
  induction numbers with
  | nil => rfl
  | cons number numbers induction =>
      simp only [encodePageNumbers, List.flatMap_cons, List.length_append,
        encodeUnsignedFixed_length, List.length_cons]
      change 4 + (encodePageNumbers numbers).length = 4 * (numbers.length + 1)
      rw [induction]
      omega

def Layout.freelistLeafNumbers (layout : Layout) : List Nat :=
  (List.range (layout.freePageCount - 1)).map fun offset =>
    layout.activePageCount + 2 + offset

theorem Layout.freelistLeafNumbers_length (layout : Layout) :
    layout.freelistLeafNumbers.length = layout.freePageCount - 1 := by
  simp [Layout.freelistLeafNumbers]

def Layout.trunkPrefix (layout : Layout) : List UInt8 :=
  encodeUnsignedFixed 4 0 ++
    encodeUnsignedFixed 4 layout.freelistLeafNumbers.length ++
      encodePageNumbers layout.freelistLeafNumbers

theorem Layout.trunkPrefix_length (layout : Layout) :
    layout.trunkPrefix.length = 8 + 4 * (layout.freePageCount - 1) := by
  simp [Layout.trunkPrefix, encodeUnsignedFixed_length,
    encodePageNumbers_length, layout.freelistLeafNumbers_length]
  omega

theorem Layout.trunkPrefix_le (layout : Layout) :
    layout.trunkPrefix.length ≤ PhysicalCodec.pageSize := by
  rw [layout.trunkPrefix_length]
  have fit := layout.free_fits
  have freeDef : layout.freePageCount =
      layout.totalPageCount - layout.activePageCount := rfl
  have activeLe := layout.active_le_total
  simp [maxFreelistPages, PhysicalCodec.pageSize] at fit ⊢
  change 8 + 4 * ((layout.totalPageCount - layout.activePageCount) - 1) ≤ 4096
  unfold Layout.activePageCount
  omega

def Layout.trunkPage (layout : Layout) : Storage.Page PhysicalCodec.pageSize := {
  bytes := (layout.trunkPrefix ++
    List.replicate (PhysicalCodec.pageSize - layout.trunkPrefix.length) 0).toArray
  sizeInvariant := by
    simp only [List.size_toArray, List.length_append, List.length_replicate]
    exact Nat.add_sub_of_le layout.trunkPrefix_le }

def Layout.freelistPages (layout : Layout) : List (Storage.Page PhysicalCodec.pageSize) :=
  if layout.freePageCount = 0 then []
  else layout.trunkPage ::
    List.replicate (layout.freePageCount - 1) (Storage.Page.zero PhysicalCodec.pageSize)

theorem Layout.freelistPages_length (layout : Layout) :
    layout.freelistPages.length = layout.freePageCount := by
  unfold Layout.freelistPages
  split
  next noFree => simp [noFree]
  next free =>
    simp only [List.length_cons, List.length_replicate]
    omega

def Layout.pages (layout : Layout) : List (Storage.Page PhysicalCodec.pageSize) :=
  layout.schemaPage :: layout.tree.tablePages ++ layout.freelistPages

theorem Layout.pages_length (layout : Layout) :
    layout.pages.length = layout.totalPageCount := by
  rw [Layout.pages, List.length_append, List.length_cons,
    layout.freelistPages_length]
  have active := PhysicalMultiPageCodec.pages_length layout.tree
  have active' : layout.tree.tablePages.length + 1 = layout.activePageCount := by
    simpa [PhysicalMultiPageCodec.pages, Layout.activePageCount] using active
  rw [active']
  unfold Layout.freePageCount
  unfold Layout.activePageCount
  have activeLe := layout.active_le_total
  omega

def Layout.fileBytes (layout : Layout) : List UInt8 :=
  DiskFormat.encodePages layout.pages

theorem encodePages_length (pages : List (Storage.Page PhysicalCodec.pageSize)) :
    (DiskFormat.encodePages pages).length = PhysicalCodec.pageSize * pages.length := by
  induction pages with
  | nil => rfl
  | cons page pages induction =>
      simp only [DiskFormat.encodePages, List.length_append, List.length_cons]
      have pageLength : page.bytes.toList.length = PhysicalCodec.pageSize := by
        simpa using page.sizeInvariant
      rw [pageLength, induction]
      rw [Nat.mul_succ, Nat.add_comm]

theorem Layout.fileBytes_length (layout : Layout) :
    layout.fileBytes.length = PhysicalCodec.pageSize * layout.totalPageCount := by
  rw [Layout.fileBytes, encodePages_length, layout.pages_length]

def Layout.storageImage (layout : Layout) : GrowableStorage.Image PhysicalCodec.pageSize := {
  pageCount := layout.totalPageCount
  read := fun pageId => layout.pages[pageId]?.getD
    (Storage.Page.zero PhysicalCodec.pageSize) }

def Layout.transactionWrites (layout : Layout) :
    List (GrowableStorage.PageWrite PhysicalCodec.pageSize) :=
  GrowableStorage.replaceWrites layout.storageImage

def physicalImage? (input : List UInt8) :
    Option (GrowableStorage.Image PhysicalCodec.pageSize) := do
  let (header, _) ← decodeDatabaseHeader input
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

def decodeFile (input : List UInt8) : Option PhysicalCodec.Database := do
  let (header, _) ← decodeDatabaseHeader input
  if _pageSize : header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize then
    let total := header.databaseSizePages.val
    let free := header.freelistPageCount.val
    if _freeWithin : free ≤ total then
      let active := total - free
      let (decoded, suffix) ← DiskFormat.decodeSizedPages PhysicalCodec.pageSize total input
      if _consumed : suffix = [] then
        let leaves := if active = 2 then decoded.pages.drop 1 |>.take 1
          else if 2 < active then decoded.pages.drop 2 |>.take (active - 2)
          else []
        let rows ← PhysicalMultiPageCodec.decodeLeafPages leaves
        if sorted : rows.Pairwise PhysicalCodec.Row.keyLess then
          if fits : PhysicalCodec.PageFit 0 (rows.map PhysicalCodec.Row.encodeCell) then
            let database : PhysicalCodec.Database := ⟨rows, sorted, fits⟩
            let tree ← PhysicalTableBTree.build database
            let layout ← ofTreeTotal? tree total
            if _canonical : layout.fileBytes = input then some database else none
          else none
        else none
      else none
    else none
  else none

end PhysicalFreelist
end SQLeanite
