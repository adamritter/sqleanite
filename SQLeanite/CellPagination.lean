import SQLeanite.PhysicalCodec

/-!
# Byte-aware leaf pagination

`PhysicalTableBTree.paginateRows` splits pairwise -- leaf capacity two -- which
exercises splits cheaply but wastes almost a whole page per leaf and is tied to
the fixed three-column row type. The arbitrary-schema core needs pagination
driven by actual encoded size, over already-encoded cells, so it is independent
of any schema.

`pack` fills the current leaf greedily and starts a new one as soon as the next
cell would not fit. Two facts are proved:

* `flatten_paginateCells` -- pagination loses and reorders nothing.
* `paginateCells_fits` -- every emitted leaf satisfies `PageFit`, provided each
  individual cell fits a page on its own. Without overflow pages that proviso is
  a real restriction, and it is exactly the "a row must fit in one page" limit
  documented in `TCB.md`.
-/

namespace SQLeanite.CellPagination

open PhysicalCodec

/-- Total encoded payload bytes without constructing `cells.flatten`.
Keeping this number in the pagination loop makes page fitting linear in the
number of cells instead of quadratic in the number of cells per page. -/
def encodedSize : List (List UInt8) → Nat
  | [] => 0
  | cell :: cells => cell.length + encodedSize cells

@[simp] theorem encodedSize_append (left right : List (List UInt8)) :
    encodedSize (left ++ right) = encodedSize left + encodedSize right := by
  induction left with
  | nil => simp [encodedSize]
  | cons cell cells induction =>
      simp [encodedSize, induction, Nat.add_assoc]

@[simp] theorem encodedSize_reverse (cells : List (List UInt8)) :
    encodedSize cells.reverse = encodedSize cells := by
  induction cells with
  | nil => rfl
  | cons cell cells induction =>
      simp [encodedSize, induction, Nat.add_comm]

theorem cellBytes_length (cells : List (List UInt8)) :
    (cellBytes cells).length = encodedSize cells := by
  unfold cellBytes
  induction cells with
  | nil => rfl
  | cons cell cells induction =>
      change (cell ++ cells.flatten).length = _
      rw [List.length_append, induction]
      rfl

/-- Greedy fill with the current payload byte count carried explicitly.
`current` is the leaf under construction, in reverse order. -/
def packSized (current : List (List UInt8)) (currentBytes : Nat) :
    List (List UInt8) → List (List (List UInt8))
  | [] => [current.reverse]
  | cell :: rest =>
      if 8 + 2 * (current.length + 1) + currentBytes + cell.length ≤ pageSize then
        packSized (cell :: current) (currentBytes + cell.length) rest
      else current.reverse :: packSized [cell] cell.length rest

/-- Compatibility wrapper. The live loop computes the current byte count once
and then maintains it incrementally. -/
def pack (current : List (List UInt8))
    (rest : List (List UInt8)) : List (List (List UInt8)) :=
  packSized current (encodedSize current) rest

/-- Split encoded cells into leaf-sized runs, preserving order. An empty table
still gets one empty leaf, matching the existing single-page convention. -/
def paginateCells (cells : List (List UInt8)) : List (List (List UInt8)) :=
  pack [] cells

theorem flatten_packSized (current : List (List UInt8)) (currentBytes : Nat) :
    (rest : List (List UInt8)) →
      (packSized current currentBytes rest).flatten = current.reverse ++ rest
  | [] => by simp [packSized]
  | cell :: rest => by
      unfold packSized
      split
      · rw [flatten_packSized (cell :: current)
          (currentBytes + cell.length) rest]
        simp
      · rw [List.flatten_cons, flatten_packSized [cell] cell.length rest]
        simp

theorem flatten_pack (current : List (List UInt8))
    (rest : List (List UInt8)) :
    (pack current rest).flatten = current.reverse ++ rest := by
  unfold pack
  exact flatten_packSized current (encodedSize current) rest

/-- Pagination is contents-preserving: no row is lost, duplicated or reordered. -/
theorem flatten_paginateCells (cells : List (List UInt8)) :
    (paginateCells cells).flatten = cells := by
  unfold paginateCells
  rw [flatten_pack]
  simp

theorem packSized_nonempty (current : List (List UInt8)) (currentBytes : Nat)
    (rest : List (List UInt8)) : packSized current currentBytes rest ≠ [] := by
  cases rest with
  | nil => simp [packSized]
  | cons cell rest =>
      unfold packSized
      split
      · exact packSized_nonempty _ _ _
      · simp

theorem pack_nonempty (current rest : List (List UInt8)) :
    pack current rest ≠ [] := by
  exact packSized_nonempty current (encodedSize current) rest

theorem paginateCells_nonempty (cells : List (List UInt8)) :
    paginateCells cells ≠ [] := pack_nonempty _ _

theorem fastFit_iff (current : List (List UInt8)) (currentBytes : Nat)
    (cell : List UInt8) (size : currentBytes = encodedSize current) :
    8 + 2 * (current.length + 1) + currentBytes + cell.length ≤ pageSize ↔
      PageFit 0 (cell :: current).reverse := by
  simp only [PageFit, List.length_reverse, List.length_cons, Nat.zero_add,
    cellBytes_length, encodedSize_reverse, encodedSize]
  omega

theorem packSized_pages_fit :
    (rest : List (List UInt8)) → (current : List (List UInt8)) →
      (currentBytes : Nat) → currentBytes = encodedSize current →
      PageFit 0 current.reverse →
      (∀ cell ∈ rest, PageFit 0 [cell]) →
      ∀ page ∈ packSized current currentBytes rest, PageFit 0 page
  | [], current, currentBytes, _, currentFits, _, page, member => by
      simp only [packSized, List.mem_singleton] at member
      exact member ▸ currentFits
  | cell :: rest, current, currentBytes, size, currentFits, singles,
      page, member => by
      unfold packSized at member
      split at member
      next fastFit =>
        have fits : PageFit 0 (cell :: current).reverse :=
          (fastFit_iff current currentBytes cell size).mp fastFit
        exact packSized_pages_fit rest (cell :: current)
          (currentBytes + cell.length) (by simp [encodedSize, size, Nat.add_comm]) fits
          (fun c m => singles c (List.mem_cons_of_mem _ m)) page member
      next =>
        rcases List.mem_cons.mp member with head | tail
        · exact head ▸ currentFits
        · refine packSized_pages_fit rest [cell] cell.length ?_ ?_
            (fun c m => singles c (List.mem_cons_of_mem _ m)) page tail
          · simp [encodedSize]
          simpa using singles cell List.mem_cons_self

theorem pack_pages_fit (rest current : List (List UInt8))
    (currentFits : PageFit 0 current.reverse)
    (singles : ∀ cell ∈ rest, PageFit 0 [cell]) :
    ∀ page ∈ pack current rest, PageFit 0 page := by
  unfold pack
  exact packSized_pages_fit rest current (encodedSize current) rfl
    currentFits singles

theorem empty_pageFit : PageFit 0 ([] : List (List UInt8)) := by
  simp [PageFit, cellBytes, pageSize]

/-- Every emitted leaf fits a page, given that each cell fits a page alone. -/
theorem paginateCells_fits (cells : List (List UInt8))
    (singles : ∀ cell ∈ cells, PageFit 0 [cell]) :
    ∀ page ∈ paginateCells cells, PageFit 0 page :=
  pack_pages_fit cells [] (by simpa using empty_pageFit) singles

end SQLeanite.CellPagination
