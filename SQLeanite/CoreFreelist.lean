import SQLeanite.CoreFile

namespace SQLeanite
namespace CoreFreelist

open FileFormat

/-- One SQLite freelist trunk can name this many leaf pages: its first two
32-bit words are the next-trunk pointer and leaf count. -/
def maxFreelistPages : Nat := PhysicalCodec.pageSize / 4 - 1

/-- A canonical Core image padded to an existing, larger file size.  Active
pages keep their page numbers.  The first unused page becomes a freelist trunk
and every later unused page is named as one of its leaves. -/
structure Layout where
  image : CoreFile.Image
  firstPage : CoreFile.Page
  remainingActive : List CoreFile.Page
  pages_eq : image.pages = firstPage :: remainingActive
  totalPageCount : Nat
  active_le_total : image.pageCount ≤ totalPageCount
  total_fits : totalPageCount < 2 ^ 32
  free_fits : totalPageCount - image.pageCount ≤ maxFreelistPages

def ofImageTotal? (image : CoreFile.Image) (totalPageCount : Nat) :
    Option Layout :=
  match pagesEq : image.pages with
  | [] => none
  | firstPage :: remainingActive =>
      if enough : image.pageCount ≤ totalPageCount then
        if totalFits : totalPageCount < 2 ^ 32 then
          if freeFits : totalPageCount - image.pageCount ≤ maxFreelistPages then
            some ⟨image, firstPage, remainingActive, pagesEq, totalPageCount,
              enough, totalFits, freeFits⟩
          else none
        else none
      else none

def Layout.activePageCount (layout : Layout) : Nat := layout.image.pageCount

def Layout.freePageCount (layout : Layout) : Nat :=
  layout.totalPageCount - layout.activePageCount

def Layout.totalU32 (layout : Layout) : U32Value :=
  ⟨layout.totalPageCount, layout.total_fits⟩

def Layout.freelistU32 (layout : Layout) : U32Value :=
  ⟨layout.freePageCount, Nat.lt_of_le_of_lt (Nat.sub_le _ _) layout.total_fits⟩

def Layout.firstTrunkU32 (layout : Layout) : U32Value :=
  if positive : 0 < layout.freePageCount then
    ⟨layout.activePageCount + 1, by
      have below : layout.activePageCount + 1 ≤ layout.totalPageCount := by
        unfold Layout.freePageCount at positive
        omega
      exact Nat.lt_of_le_of_lt below layout.total_fits⟩
  else ⟨0, by omega⟩

def Layout.databaseHeader (layout : Layout) : DatabaseHeader :=
  { CoreFile.databaseHeader layout.totalU32 with
    firstFreelistTrunk := layout.firstTrunkU32
    freelistPageCount := layout.freelistU32 }

/-- Replace only the 100-byte database header.  The schema B-tree page body is
byte-for-byte the canonical Core encoding. -/
def Layout.schemaPage (layout : Layout) : CoreFile.Page := {
  bytes := encodeDatabaseHeader layout.databaseHeader ++
    layout.firstPage.bytes.drop 100
  length_eq := by
    rw [List.length_append, encodeDatabaseHeader_length, List.length_drop,
      layout.firstPage.length_eq]
    simp [PhysicalCodec.pageSize] }

def Layout.activePages (layout : Layout) : List CoreFile.Page :=
  layout.schemaPage :: layout.remainingActive

theorem Layout.activePages_length (layout : Layout) :
    layout.activePages.length = layout.activePageCount := by
  unfold Layout.activePages Layout.activePageCount CoreFile.Image.pageCount
  rw [layout.pages_eq]
  rfl

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
  simp [maxFreelistPages, PhysicalCodec.pageSize] at fit ⊢
  change 8 + 4 * ((layout.totalPageCount - layout.image.pageCount) - 1) ≤ 4096
  omega

def Layout.trunkPage (layout : Layout) : CoreFile.Page := {
  bytes := layout.trunkPrefix ++
    List.replicate (PhysicalCodec.pageSize - layout.trunkPrefix.length) 0
  length_eq := by
    simp only [List.length_append, List.length_replicate]
    exact Nat.add_sub_of_le layout.trunkPrefix_le }

def zeroPage : CoreFile.Page := {
  bytes := List.replicate PhysicalCodec.pageSize 0
  length_eq := by simp }

def Layout.freelistPages (layout : Layout) : List CoreFile.Page :=
  if layout.freePageCount = 0 then []
  else layout.trunkPage ::
    List.replicate (layout.freePageCount - 1) zeroPage

theorem Layout.freelistPages_length (layout : Layout) :
    layout.freelistPages.length = layout.freePageCount := by
  unfold Layout.freelistPages
  split
  next noFree => simp [noFree]
  next hasFree =>
    simp only [List.length_cons, List.length_replicate]
    omega

def Layout.pages (layout : Layout) : List CoreFile.Page :=
  layout.activePages ++ layout.freelistPages

theorem Layout.pages_length (layout : Layout) :
    layout.pages.length = layout.totalPageCount := by
  rw [Layout.pages, List.length_append, layout.activePages_length,
    layout.freelistPages_length]
  unfold Layout.freePageCount Layout.activePageCount
  exact Nat.add_sub_of_le layout.active_le_total

def Layout.paddedImage (layout : Layout) : CoreFile.Image := {
  database := layout.image.database
  pages := layout.pages }

theorem Layout.paddedImage_pageCount (layout : Layout) :
    layout.paddedImage.pageCount = layout.totalPageCount :=
  layout.pages_length

theorem Layout.paddedImage_database (layout : Layout) :
    layout.paddedImage.database = layout.image.database := rfl

end CoreFreelist
end SQLeanite
