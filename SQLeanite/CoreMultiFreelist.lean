import SQLeanite.CoreFreelist
import SQLeanite.SQLite.ApplicationHeader

namespace SQLeanite
namespace CoreMultiFreelist

open FileFormat

def trunkCapacity : Nat := CoreFreelist.maxFreelistPages

theorem trunkCapacity_positive : 0 < trunkCapacity := by
  decide

def chunkSize (count : Nat) : Nat := min count trunkCapacity

theorem chunkSize_positive {count : Nat} (positive : 0 < count) :
    0 < chunkSize count := by
  unfold chunkSize
  exact (Nat.lt_min).2 ⟨positive, trunkCapacity_positive⟩

theorem remaining_lt {count : Nat} (positive : 0 < count) :
    count - chunkSize count < count := by
  have chunkPositive := chunkSize_positive positive
  omega

def leafNumbers (start count : Nat) : List Nat :=
  (List.range (chunkSize count - 1)).map (fun offset => start + 1 + offset)

theorem leafNumbers_length (start count : Nat) :
    (leafNumbers start count).length = chunkSize count - 1 := by
  simp [leafNumbers]

def nextTrunk (start count : Nat) : Nat :=
  if trunkCapacity < count then start + trunkCapacity else 0

theorem nextTrunk_valid (start count : Nat) :
    nextTrunk start count = 0 ∨
      (start < nextTrunk start count ∧ nextTrunk start count < start + count) := by
  unfold nextTrunk
  split
  next more =>
    right
    have capacityPositive := trunkCapacity_positive
    omega
  next final => exact .inl rfl

theorem leafNumbers_valid {start count pageNumber : Nat}
    (member : pageNumber ∈ leafNumbers start count) :
    start < pageNumber ∧ pageNumber < start + count := by
  simp only [leafNumbers, List.mem_map, List.mem_range] at member
  rcases member with ⟨offset, below, equal⟩
  subst pageNumber
  have chunkLe : chunkSize count ≤ count := Nat.min_le_left _ _
  omega

def trunkPrefix (start count : Nat) : List UInt8 :=
  encodeUnsignedFixed 4 (nextTrunk start count) ++
    encodeUnsignedFixed 4 (leafNumbers start count).length ++
      CoreFreelist.encodePageNumbers (leafNumbers start count)

theorem trunkPrefix_length (start count : Nat) :
    (trunkPrefix start count).length =
      8 + 4 * (chunkSize count - 1) := by
  simp [trunkPrefix, encodeUnsignedFixed_length,
    CoreFreelist.encodePageNumbers_length, leafNumbers_length]
  omega

theorem trunkPrefix_le (start count : Nat) :
    (trunkPrefix start count).length ≤ PhysicalCodec.pageSize := by
  rw [trunkPrefix_length]
  have bounded : chunkSize count ≤ trunkCapacity := by
    exact Nat.min_le_right _ _
  simp [trunkCapacity, CoreFreelist.maxFreelistPages,
    PhysicalCodec.pageSize] at bounded ⊢
  omega

def trunkPage (start count : Nat) : CoreFile.Page := {
  bytes := trunkPrefix start count ++
    List.replicate (PhysicalCodec.pageSize - (trunkPrefix start count).length) 0
  length_eq := by
    simp only [List.length_append, List.length_replicate]
    exact Nat.add_sub_of_le (trunkPrefix_le start count) }

/-- Emit pages in physical order. Each recursive segment starts with a trunk,
followed by the zero-filled leaf pages named by that trunk. -/
def freelistPages (start count : Nat) : List CoreFile.Page :=
  if _zero : count = 0 then []
  else
      let chunk := chunkSize count
      trunkPage start count ::
        List.replicate (chunk - 1) CoreFreelist.zeroPage ++
          freelistPages (start + chunk) (count - chunk)
termination_by count
decreasing_by
  exact remaining_lt (Nat.zero_lt_of_ne_zero _zero)

theorem freelistPages_length (start count : Nat) :
    (freelistPages start count).length = count := by
  unfold freelistPages
  split
  next zero => simp [zero]
  next nonzero =>
    simp only [List.length_append, List.length_cons, List.length_replicate]
    rw [freelistPages_length (start + chunkSize count) (count - chunkSize count)]
    have positive := Nat.zero_lt_of_ne_zero nonzero
    have chunkPositive := chunkSize_positive positive
    have chunkLe : chunkSize count ≤ count := Nat.min_le_left _ _
    omega
termination_by count
decreasing_by
  apply remaining_lt
  omega

/-- Application-owned header fields survive rewrites independently of the
logical schema, page allocation and generated-image optimization markers. -/
abbrev HeaderMetadata := SQLite.ApplicationHeader.Metadata

def HeaderMetadata.fromHeader (header : DatabaseHeader) : HeaderMetadata :=
  { applicationId := header.applicationId, userVersion := header.userVersion }

def HeaderMetadata.decode? (bytes : List UInt8) : Option HeaderMetadata :=
  (decodeDatabaseHeader bytes).map (fun (header, _) => HeaderMetadata.fromHeader header)

structure Layout where
  image : CoreFile.Image
  firstPage : CoreFile.Page
  remainingActive : List CoreFile.Page
  pages_eq : image.pages = firstPage :: remainingActive
  totalPageCount : Nat
  active_le_total : image.pageCount ≤ totalPageCount
  total_fits : totalPageCount < 2 ^ 32
  metadata : HeaderMetadata := {}

def ofImageTotal? (image : CoreFile.Image) (totalPageCount : Nat) :
    Option Layout :=
  match pagesEq : image.pages with
  | [] => none
  | firstPage :: remainingActive =>
      if enough : image.pageCount ≤ totalPageCount then
        if totalFits : totalPageCount < 2 ^ 32 then
          some ⟨image, firstPage, remainingActive, pagesEq, totalPageCount,
            enough, totalFits, {}⟩
        else none
      else none

theorem ofImageTotal?_image {image : CoreFile.Image} {totalPageCount : Nat}
    {layout : Layout}
    (prepared : ofImageTotal? image totalPageCount = some layout) :
    layout.image = image := by
  unfold ofImageTotal? at prepared
  split at prepared
  next => contradiction
  next firstPage remainingActive pagesEq =>
    split at prepared
    next enough =>
      split at prepared
      next totalFits =>
        injection prepared with equal
        exact congrArg Layout.image equal.symm
      next => contradiction
    next => contradiction

theorem ofImageTotal?_totalPageCount {image : CoreFile.Image}
    {totalPageCount : Nat} {layout : Layout}
    (prepared : ofImageTotal? image totalPageCount = some layout) :
    layout.totalPageCount = totalPageCount := by
  unfold ofImageTotal? at prepared
  split at prepared
  next => contradiction
  next firstPage remainingActive pagesEq =>
    split at prepared
    next enough =>
      split at prepared
      next totalFits =>
        injection prepared with equal
        exact congrArg Layout.totalPageCount equal.symm
      next => contradiction
    next => contradiction

def Layout.activePageCount (layout : Layout) : Nat := layout.image.pageCount
def Layout.freePageCount (layout : Layout) : Nat :=
  layout.totalPageCount - layout.activePageCount

def Layout.totalU32 (layout : Layout) : U32Value :=
  ⟨layout.totalPageCount, layout.total_fits⟩

def Layout.freelistU32 (layout : Layout) : U32Value :=
  ⟨layout.freePageCount,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) layout.total_fits⟩

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
    freelistPageCount := layout.freelistU32
    applicationId := layout.metadata.applicationId
    userVersion := layout.metadata.userVersion }

theorem Layout.applicationId_preserved (layout : Layout) :
    layout.databaseHeader.applicationId = layout.metadata.applicationId := rfl

theorem Layout.userVersion_preserved (layout : Layout) :
    layout.databaseHeader.userVersion = layout.metadata.userVersion := rfl

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

def Layout.freelistPages (layout : Layout) : List CoreFile.Page :=
  CoreMultiFreelist.freelistPages (layout.activePageCount + 1)
    layout.freePageCount

theorem Layout.freelistPages_length (layout : Layout) :
    layout.freelistPages.length = layout.freePageCount :=
  CoreMultiFreelist.freelistPages_length _ _

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

end CoreMultiFreelist
end SQLeanite
