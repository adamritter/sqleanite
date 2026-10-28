import SQLeanite.PagedBTree
import SQLeanite.PhysicalCodec.PageSize

namespace SQLeanite
namespace PhysicalTableBTree

open FileFormat
open PhysicalCodec

/-!
# Physical two-level SQLite table B-tree for the persisted MVP

The logical `PagedBTree` deliberately uses leaf capacity two so split and merge
boundaries stay small enough to audit.  This module gives that partition a real
SQLite representation: page two is either the sole table leaf or an interior
table root whose children are leaf pages three and above.

Every child reference is constructed as a `BoundedPageNumber`; raw natural
numbers never enter the tree topology.  `Tree.toList_eq` is the abstraction
theorem connecting the physical partition to the logical row sequence.
-/

/-- Pairwise pagination used by both the logical and physical MVP trees.  The
empty database still receives one empty root leaf page. -/
def paginateRows : List PhysicalCodec.Row → List (List PhysicalCodec.Row)
  | [] => [[]]
  | [row] => [[row]]
  | first :: second :: rows => [first, second] ::
      match rows with
      | [] => []
      | _ => paginateRows rows

def flattenRows (pages : List (List PhysicalCodec.Row)) : List PhysicalCodec.Row :=
  pages.flatten

theorem flattenRows_paginateRows : (rows : List PhysicalCodec.Row) →
    flattenRows (paginateRows rows) = rows
  | [] => rfl
  | [row] => rfl
  | first :: second :: [] => rfl
  | first :: second :: third :: rows => by
      change first :: second ::
        flattenRows (paginateRows (third :: rows)) =
          first :: second :: third :: rows
      rw [flattenRows_paginateRows (third :: rows)]

theorem paginateRows_nonempty (rows : List PhysicalCodec.Row) :
    paginateRows rows ≠ [] := by
  cases rows with
  | nil => simp [paginateRows]
  | cons first rows =>
      cases rows with
      | nil => simp [paginateRows]
      | cons second rows => simp [paginateRows]

theorem paginateRows_page_sublist : (rows page : List PhysicalCodec.Row) →
    page ∈ paginateRows rows → page.Sublist rows
  | [], page, member => by
      simp [paginateRows] at member
      subst page
      exact List.nil_sublist _
  | [row], page, member => by
      simp [paginateRows] at member
      subst page
      exact List.Sublist.refl _
  | first :: second :: [], page, member => by
      simp [paginateRows] at member
      subst page
      exact List.Sublist.refl _
  | first :: second :: third :: rows, page, member => by
      simp only [paginateRows, List.mem_cons] at member
      rcases member with equal | member
      · subst page
        exact List.Sublist.cons₂ first
          (List.Sublist.cons₂ second (List.nil_sublist _))
      · exact List.Sublist.cons first (List.Sublist.cons second
          (paginateRows_page_sublist (third :: rows) page member))

private theorem flatten_length_le_of_sublist {small large : List (List UInt8)}
    (sublist : small.Sublist large) :
    small.flatten.length ≤ large.flatten.length := by
  induction sublist with
  | slnil => simp
  | @cons _ _ item sublist induction =>
      simp only [List.flatten_cons, List.length_append]
      exact Nat.le_trans induction (Nat.le_add_left _ _)
  | @cons_cons _ _ item sublist induction =>
      simp only [List.flatten_cons, List.length_append]
      exact Nat.add_le_add_left induction item.length

theorem PageFit.of_sublist {small large : List (List UInt8)}
    (sublist : small.Sublist large) (fits : PageFit headerOffset large) :
    PageFit headerOffset small := by
  unfold PageFit cellBytes at fits ⊢
  have countLe := sublist.length_le
  have bytesLe := flatten_length_le_of_sublist sublist
  omega

theorem paginateRows_page_fits (database : PhysicalCodec.Database)
    (page : List PhysicalCodec.Row) (member : page ∈ paginateRows database.rows) :
    PageFit 0 (page.map PhysicalCodec.Row.encodeCell) := by
  apply PageFit.of_sublist
  · exact (paginateRows_page_sublist database.rows page member).map _
  · exact database.pageFits

def encodeU32Nat (value : Nat) : List UInt8 :=
  encodeUnsignedFixed 4 value

theorem encodeU32Nat_length (value : Nat) :
    (encodeU32Nat value).length = 4 :=
  encodeUnsignedFixed_length 4 value

def interiorHeader (cellCount contentStart : Nat) (rightmost : U32Value) :
    List UInt8 :=
  [5, 0, 0] ++ encodeU16Nat cellCount ++ encodeU16Nat contentStart ++ [0] ++
    FileFormat.encodeU32Bytes rightmost

theorem interiorHeader_length (cellCount contentStart : Nat)
    (rightmost : U32Value) :
    (interiorHeader cellCount contentStart rightmost).length = 12 := by
  simp [interiorHeader, encodeU16Nat_length, FileFormat.encodeU32Bytes]

def InteriorPageFit (cells : List (List UInt8)) : Prop :=
  12 + 2 * cells.length + (cellBytes cells).length ≤ pageSize

instance (cells : List (List UInt8)) : Decidable (InteriorPageFit cells) := by
  unfold InteriorPageFit
  infer_instance

theorem InteriorPageFit.cellCount_lt (fits : InteriorPageFit cells) :
    cells.length < 65536 := by
  unfold InteriorPageFit at fits
  simp only [pageSize] at fits
  omega

def interiorPageBody (rightmost : U32Value) (cells : List (List UInt8)) :
    List UInt8 :=
  let content := cellBytes cells
  let contentStart := pageSize - content.length
  let headerAndPointers :=
    interiorHeader cells.length contentStart rightmost ++
      leafPointers contentStart cells
  headerAndPointers ++
    List.replicate (contentStart - headerAndPointers.length) 0 ++ content

theorem interiorPageBody_length (rightmost : U32Value)
    (cells : List (List UInt8)) (fits : InteriorPageFit cells) :
    (interiorPageBody rightmost cells).length = pageSize := by
  have prefixLength :
      (interiorHeader cells.length
          (pageSize - (cellBytes cells).length) rightmost ++
        leafPointers (pageSize - (cellBytes cells).length) cells).length =
          12 + 2 * cells.length := by
    simp [interiorHeader_length, leafPointers_length]
  unfold interiorPageBody
  dsimp only
  rw [List.length_append, List.length_append, List.length_replicate,
    prefixLength]
  unfold InteriorPageFit at fits
  simp only [pageSize] at fits ⊢
  omega

theorem interiorPageBody_drop_content (rightmost : U32Value)
    (cells : List (List UInt8)) (fits : InteriorPageFit cells) :
    (interiorPageBody rightmost cells).drop
        (pageSize - (cellBytes cells).length) = cellBytes cells := by
  let contentStart := pageSize - (cellBytes cells).length
  let headerAndPointers :=
    interiorHeader cells.length contentStart rightmost ++
      leafPointers contentStart cells
  have prefixSize : headerAndPointers.length = 12 + 2 * cells.length := by
    simp [headerAndPointers, interiorHeader_length, leafPointers_length]
  have contentLe : (cellBytes cells).length ≤ pageSize := by
    unfold InteriorPageFit at fits
    omega
  have prefixLe : headerAndPointers.length ≤ contentStart := by
    rw [prefixSize]
    unfold InteriorPageFit at fits
    omega
  let paddedPrefix := headerAndPointers ++
    List.replicate (contentStart - headerAndPointers.length) 0
  have prefixLength : paddedPrefix.length = contentStart := by
    unfold paddedPrefix
    simp only [List.length_append, List.length_replicate]
    omega
  unfold interiorPageBody
  change (paddedPrefix ++ cellBytes cells).drop contentStart = cellBytes cells
  rw [← prefixLength]
  simp

/-- Last row of every leaf except the rightmost.  These are exactly SQLite's
separator keys for a two-level table B-tree. -/
def separatorRows : List (List PhysicalCodec.Row) → List PhysicalCodec.Row
  | [] | [_] => []
  | page :: next :: pages =>
      page.getLast?.toList ++ separatorRows (next :: pages)

def pageCountFor (database : PhysicalCodec.Database) : Nat :=
  (paginateRows database.rows).length + 2

def leafPageNumbersFor (database : PhysicalCodec.Database)
    (pageCountFits : pageCountFor database < 2 ^ 32) :
    List (BoundedPageNumber (pageCountFor database)) :=
  List.ofFn fun pageId : Fin (paginateRows database.rows).length =>
    BoundedPageNumber.ofPageId pageCountFits
      ⟨pageId.val + 2, by simp [pageCountFor]⟩

def interiorCellBytesFor (database : PhysicalCodec.Database)
    (pageCountFits : pageCountFor database < 2 ^ 32) : List (List UInt8) :=
  List.zipWith
    (fun child row => (InteriorTableCell.mk child.number row.rowid).encode)
    (leafPageNumbersFor database pageCountFits)
    (separatorRows (paginateRows database.rows))

structure Tree where
  database : PhysicalCodec.Database
  leafFits : ∀ page ∈ paginateRows database.rows,
    PageFit 0 (page.map PhysicalCodec.Row.encodeCell)
  pageCountFits : pageCountFor database < 2 ^ 32
  rootFits : (paginateRows database.rows).length = 1 ∨
    InteriorPageFit (interiorCellBytesFor database pageCountFits)

def Tree.leaves (tree : Tree) : List (List PhysicalCodec.Row) :=
  paginateRows tree.database.rows

def Tree.pageCount (tree : Tree) : Nat := pageCountFor tree.database

def Tree.toList (tree : Tree) : List PhysicalCodec.Row := flattenRows tree.leaves

theorem Tree.toList_eq (tree : Tree) : tree.toList = tree.database.rows :=
  flattenRows_paginateRows _

def Tree.leafPageNumbers (tree : Tree) :
    List (BoundedPageNumber tree.pageCount) :=
  leafPageNumbersFor tree.database tree.pageCountFits

theorem Tree.leafPageNumbers_length (tree : Tree) :
    tree.leafPageNumbers.length = tree.leaves.length := by
  exact List.length_ofFn

def Tree.interiorCells (tree : Tree) : List InteriorTableCell :=
  List.zipWith (fun child row => ⟨child.number, row.rowid⟩)
    tree.leafPageNumbers (separatorRows tree.leaves)

def Tree.interiorCellBytes (tree : Tree) : List (List UInt8) :=
  interiorCellBytesFor tree.database tree.pageCountFits

def Tree.rightmostPage (tree : Tree) : U32Value :=
  ⟨tree.pageCount, tree.pageCountFits⟩

theorem Tree.all_child_references_within (tree : Tree)
    (child : BoundedPageNumber tree.pageCount)
    (_member : child ∈ tree.leafPageNumbers) :
    child.number.value.val ≤ tree.pageCount :=
  child.withinDatabase

def interiorStoragePage (rightmost : U32Value)
    (cells : List (List UInt8)) (fits : InteriorPageFit cells) :
    Storage.Page pageSize := {
  bytes := (interiorPageBody rightmost cells).toArray
  sizeInvariant := by simp [interiorPageBody_length rightmost cells fits] }

def Tree.leafDatabases (tree : Tree) : List PhysicalCodec.Database :=
  tree.leaves.attach.map fun page => {
    rows := page.val
    rowidsSorted := List.Pairwise.sublist
      (paginateRows_page_sublist tree.database.rows page.val page.property)
      tree.database.rowidsSorted
    pageFits := tree.leafFits page.val page.property }

theorem Tree.leafDatabases_length (tree : Tree) :
    tree.leafDatabases.length = tree.leaves.length := by
  simp [Tree.leafDatabases]

theorem Tree.leafDatabases_flatten_rows (tree : Tree) :
    (tree.leafDatabases.map PhysicalCodec.Database.rows).flatten = tree.toList := by
  simp [Tree.leafDatabases, Tree.toList, flattenRows]

def Tree.leafStoragePages (tree : Tree) : List (Storage.Page pageSize) :=
  tree.leafDatabases.map PhysicalCodec.Database.dataPage

theorem Tree.leafStoragePages_length (tree : Tree) :
    tree.leafStoragePages.length = tree.leaves.length := by
  rw [Tree.leafStoragePages, List.length_map, tree.leafDatabases_length]

def Tree.tablePages (tree : Tree) : List (Storage.Page pageSize) :=
  if single : tree.leaves.length = 1 then
    tree.leafStoragePages
  else
    let rootFit : InteriorPageFit tree.interiorCellBytes := by
      have fit := tree.rootFits.resolve_left single
      exact fit
    interiorStoragePage tree.rightmostPage tree.interiorCellBytes rootFit ::
      tree.leafStoragePages

theorem Tree.tablePages_nonempty (tree : Tree) : tree.tablePages ≠ [] := by
  unfold Tree.tablePages
  split
  · intro empty
    have lengthOne : tree.leafStoragePages.length = 1 := by
      rw [tree.leafStoragePages_length]
      assumption
    rw [empty] at lengthOne
    contradiction
  · simp

theorem Tree.tablePages_length (tree : Tree) :
    tree.tablePages.length =
      if tree.leaves.length = 1 then 1 else tree.leaves.length + 1 := by
  unfold Tree.tablePages
  split
  · simp [tree.leafStoragePages_length, *]
  · simp [tree.leafStoragePages_length]

set_option maxHeartbeats 600000 in
def build (database : PhysicalCodec.Database) : Option Tree :=
  if pageCountFits : pageCountFor database < 2 ^ 32 then
    if single : (paginateRows database.rows).length = 1 then
      some {
        database
        leafFits := paginateRows_page_fits database
        pageCountFits
        rootFits := .inl single }
    else
      if rootFit : InteriorPageFit
          (interiorCellBytesFor database pageCountFits) then
        some {
          database
          leafFits := paginateRows_page_fits database
          pageCountFits
          rootFits := .inr rootFit }
      else none
  else none

theorem build_toList {database : PhysicalCodec.Database} {tree : Tree}
    (built : build database = some tree) : tree.toList = database.rows := by
  unfold build at built
  split at built
  next pageCountFits =>
    split at built
    next single =>
      injection built with equal
      subst tree
      exact flattenRows_paginateRows _
    next notSingle =>
      split at built
      next rootFit =>
        injection built with equal
        subst tree
        exact flattenRows_paginateRows _
      next => contradiction
  next => contradiction

end PhysicalTableBTree
end SQLeanite
