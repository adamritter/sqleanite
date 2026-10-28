import SQLeanite.FileFormat.U16Value
import SQLeanite.Storage

namespace SQLeanite
namespace FileFormat

/-- SQLite database pages are numbered from one, while the on-disk field is a
32-bit unsigned integer. This type makes the invalid page number zero
unrepresentable. -/
structure PageNumber where
  value : U32Value
  positive : 0 < value.val
  deriving Repr, DecidableEq

def PageNumber.encode (page : PageNumber) : List UInt8 :=
  encodeU32Bytes page.value

def decodePageNumber (input : List UInt8) : Option (PageNumber × List UInt8) := do
  let (value, suffix) ← decodeU32Bytes input
  if positive : 0 < value.val then
    some (⟨value, positive⟩, suffix)
  else
    none

theorem decodePageNumber_encode (page : PageNumber) (suffix : List UInt8) :
    decodePageNumber (page.encode ++ suffix) = some (page, suffix) := by
  unfold PageNumber.encode decodePageNumber
  rw [decodeU32Bytes_encode]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos page.positive]

/-- A one-based SQLite page number proved to lie within a database containing
`pageCount` pages. -/
structure BoundedPageNumber (pageCount : Nat) where
  number : PageNumber
  withinDatabase : number.value.val ≤ pageCount
  deriving Repr, DecidableEq

def BoundedPageNumber.toPageId {pageCount : Nat}
    (page : BoundedPageNumber pageCount) : Storage.PageId pageCount :=
  ⟨page.number.value.val - 1, by
    have positive := page.number.positive
    have within := page.withinDatabase
    omega⟩

theorem BoundedPageNumber.toPageId_succ {pageCount : Nat}
    (page : BoundedPageNumber pageCount) :
    page.toPageId.val + 1 = page.number.value.val := by
  have positive := page.number.positive
  change page.number.value.val - 1 + 1 = page.number.value.val
  omega

def BoundedPageNumber.ofPageId {pageCount : Nat}
    (pageCountFits : pageCount < 2 ^ 32) (pageId : Storage.PageId pageCount) :
    BoundedPageNumber pageCount := {
  number := {
    value := ⟨pageId.val + 1, by
      have inRange := pageId.isLt
      omega⟩
    positive := Nat.zero_lt_succ pageId.val }
  withinDatabase := by
    have inRange := pageId.isLt
    change pageId.val + 1 ≤ pageCount
    omega }

theorem BoundedPageNumber.toPageId_ofPageId {pageCount : Nat}
    (pageCountFits : pageCount < 2 ^ 32) (pageId : Storage.PageId pageCount) :
    (BoundedPageNumber.ofPageId pageCountFits pageId).toPageId = pageId := by
  apply Fin.ext
  change pageId.val + 1 - 1 = pageId.val
  simp

theorem BoundedPageNumber.ofPageId_toPageId {pageCount : Nat}
    (pageCountFits : pageCount < 2 ^ 32)
    (page : BoundedPageNumber pageCount) :
    BoundedPageNumber.ofPageId pageCountFits page.toPageId = page := by
  rcases page with ⟨⟨⟨value, valueBound⟩, positive⟩, within⟩
  unfold BoundedPageNumber.ofPageId BoundedPageNumber.toPageId
  change 0 < value at positive
  change value ≤ pageCount at within
  have oneLe : 1 ≤ value := by omega
  simp [Nat.sub_add_cancel oneLe]

/-- Fields shared by all four SQLite B-tree page-header variants. -/
structure BTreePageHeaderCommon where
  firstFreeblock : U16Value
  cellCount : U16Value
  cellContentStart : U16Value
  fragmentedFreeBytes : UInt8
  deriving Repr, DecidableEq

inductive BTreePageType where
  | interiorIndex
  | interiorTable
  | leafIndex
  | leafTable
  deriving Repr, DecidableEq

def BTreePageType.typeByte : BTreePageType → UInt8
  | .interiorIndex => 2
  | .interiorTable => 5
  | .leafIndex => 10
  | .leafTable => 13

def decodeBTreePageType (typeByte : UInt8) : Option BTreePageType :=
  match typeByte.toNat with
  | 2 => some .interiorIndex
  | 5 => some .interiorTable
  | 10 => some .leafIndex
  | 13 => some .leafTable
  | _ => none

theorem decodeBTreePageType_typeByte (pageType : BTreePageType) :
    decodeBTreePageType pageType.typeByte = some pageType := by
  cases pageType <;> decide

/-- SQLite distinguishes table/index and leaf/interior pages in the first
header byte. Interior variants additionally carry a rightmost child page. -/
inductive BTreePageHeader where
  | interiorIndex (common : BTreePageHeaderCommon) (rightmostPage : U32Value)
  | interiorTable (common : BTreePageHeaderCommon) (rightmostPage : U32Value)
  | leafIndex (common : BTreePageHeaderCommon)
  | leafTable (common : BTreePageHeaderCommon)
  deriving Repr, DecidableEq

def BTreePageHeader.common : BTreePageHeader → BTreePageHeaderCommon
  | .interiorIndex common _ | .interiorTable common _ |
      .leafIndex common | .leafTable common => common

def BTreePageHeader.pageType : BTreePageHeader → BTreePageType
  | .interiorIndex _ _ => .interiorIndex
  | .interiorTable _ _ => .interiorTable
  | .leafIndex _ => .leafIndex
  | .leafTable _ => .leafTable

def BTreePageHeader.typeByte (header : BTreePageHeader) : UInt8 :=
  header.pageType.typeByte

def BTreePageHeader.headerSize : BTreePageHeader → Nat
  | .interiorIndex _ _ | .interiorTable _ _ => 12
  | .leafIndex _ | .leafTable _ => 8

private def encodeBTreePageHeaderCommon (common : BTreePageHeaderCommon) : List UInt8 :=
  encodeU16Bytes common.firstFreeblock ++ encodeU16Bytes common.cellCount ++
    encodeU16Bytes common.cellContentStart ++ [common.fragmentedFreeBytes]

def encodeBTreePageHeader (header : BTreePageHeader) : List UInt8 :=
  [header.typeByte] ++ encodeBTreePageHeaderCommon header.common ++
    match header with
    | .interiorIndex _ rightmostPage | .interiorTable _ rightmostPage =>
      encodeU32Bytes rightmostPage
    | .leafIndex _ | .leafTable _ => []

theorem encodeBTreePageHeader_interiorTable
    (common : BTreePageHeaderCommon) (rightmostPage : U32Value) :
    encodeBTreePageHeader (.interiorTable common rightmostPage) =
      [5] ++ encodeU16Bytes common.firstFreeblock ++
        encodeU16Bytes common.cellCount ++
        encodeU16Bytes common.cellContentStart ++
        [common.fragmentedFreeBytes] ++ encodeU32Bytes rightmostPage := by
  rfl

private def decodeBTreePageHeaderCommon (input : List UInt8) :
    Option (BTreePageHeaderCommon × List UInt8) := do
  let (firstFreeblock, afterFreeblock) ← decodeU16Bytes input
  let (cellCount, afterCellCount) ← decodeU16Bytes afterFreeblock
  let (cellContentStart, afterContentStart) ← decodeU16Bytes afterCellCount
  match afterContentStart with
  | fragmentedFreeBytes :: suffix =>
    some ({ firstFreeblock, cellCount, cellContentStart, fragmentedFreeBytes }, suffix)
  | [] => none

private theorem decodeBTreePageHeaderCommon_encode
    (common : BTreePageHeaderCommon) (suffix : List UInt8) :
    decodeBTreePageHeaderCommon
      (encodeBTreePageHeaderCommon common ++ suffix) = some (common, suffix) := by
  rcases common with ⟨firstFreeblock, cellCount, cellContentStart, fragmented⟩
  simp [encodeBTreePageHeaderCommon, decodeBTreePageHeaderCommon,
    decodeU16Bytes_encode, List.append_assoc]

def decodeBTreePageHeader : List UInt8 → Option (BTreePageHeader × List UInt8)
  | typeByte :: input => do
    let pageType ← decodeBTreePageType typeByte
    let (common, afterCommon) ← decodeBTreePageHeaderCommon input
    match pageType with
    | .interiorIndex => do
      let (rightmostPage, suffix) ← decodeU32Bytes afterCommon
      some (.interiorIndex common rightmostPage, suffix)
    | .interiorTable => do
      let (rightmostPage, suffix) ← decodeU32Bytes afterCommon
      some (.interiorTable common rightmostPage, suffix)
    | .leafIndex => some (.leafIndex common, afterCommon)
    | .leafTable => some (.leafTable common, afterCommon)
  | [] => none

theorem encodeBTreePageHeader_length (header : BTreePageHeader) :
    (encodeBTreePageHeader header).length = header.headerSize := by
  cases header <;> simp [encodeBTreePageHeader, encodeBTreePageHeaderCommon,
    BTreePageHeader.typeByte, BTreePageHeader.common, BTreePageHeader.headerSize,
    encodeU16Bytes, PageNumber.encode, encodeU32Bytes]

private theorem decodeBTreePageHeader_encode_interiorIndex
    (common : BTreePageHeaderCommon) (rightmostPage : U32Value)
    (suffix : List UInt8) :
    decodeBTreePageHeader
      (encodeBTreePageHeader (.interiorIndex common rightmostPage) ++ suffix) =
      some (.interiorIndex common rightmostPage, suffix) := by
  change (do
    let decodedType ← decodeBTreePageType BTreePageType.interiorIndex.typeByte
    let (decodedCommon, afterCommon) ← decodeBTreePageHeaderCommon
      (encodeBTreePageHeaderCommon common ++ (encodeU32Bytes rightmostPage ++ suffix))
    match decodedType with
    | .interiorIndex => do
      let (decodedPage, remaining) ← decodeU32Bytes afterCommon
      some (BTreePageHeader.interiorIndex decodedCommon decodedPage, remaining)
    | .interiorTable => do
      let (decodedPage, remaining) ← decodeU32Bytes afterCommon
      some (BTreePageHeader.interiorTable decodedCommon decodedPage, remaining)
    | .leafIndex => some (BTreePageHeader.leafIndex decodedCommon, afterCommon)
    | .leafTable => some (BTreePageHeader.leafTable decodedCommon, afterCommon)) = _
  rw [decodeBTreePageType_typeByte]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeBTreePageHeaderCommon_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeU32Bytes_encode]

private theorem decodeBTreePageHeader_encode_interiorTable
    (common : BTreePageHeaderCommon) (rightmostPage : U32Value)
    (suffix : List UInt8) :
    decodeBTreePageHeader
      (encodeBTreePageHeader (.interiorTable common rightmostPage) ++ suffix) =
      some (.interiorTable common rightmostPage, suffix) := by
  change (do
    let decodedType ← decodeBTreePageType BTreePageType.interiorTable.typeByte
    let (decodedCommon, afterCommon) ← decodeBTreePageHeaderCommon
      (encodeBTreePageHeaderCommon common ++ (encodeU32Bytes rightmostPage ++ suffix))
    match decodedType with
    | .interiorIndex => do
      let (decodedPage, remaining) ← decodeU32Bytes afterCommon
      some (BTreePageHeader.interiorIndex decodedCommon decodedPage, remaining)
    | .interiorTable => do
      let (decodedPage, remaining) ← decodeU32Bytes afterCommon
      some (BTreePageHeader.interiorTable decodedCommon decodedPage, remaining)
    | .leafIndex => some (BTreePageHeader.leafIndex decodedCommon, afterCommon)
    | .leafTable => some (BTreePageHeader.leafTable decodedCommon, afterCommon)) = _
  rw [decodeBTreePageType_typeByte]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeBTreePageHeaderCommon_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeU32Bytes_encode]

private theorem decodeBTreePageHeader_encode_leafIndex
    (common : BTreePageHeaderCommon) (suffix : List UInt8) :
    decodeBTreePageHeader (encodeBTreePageHeader (.leafIndex common) ++ suffix) =
      some (.leafIndex common, suffix) := by
  change (do
    let decodedType ← decodeBTreePageType BTreePageType.leafIndex.typeByte
    let (decodedCommon, remaining) ← decodeBTreePageHeaderCommon
      (encodeBTreePageHeaderCommon common ++ suffix)
    match decodedType with
    | .interiorIndex => do
      let (decodedPage, suffix) ← decodeU32Bytes remaining
      some (BTreePageHeader.interiorIndex decodedCommon decodedPage, suffix)
    | .interiorTable => do
      let (decodedPage, suffix) ← decodeU32Bytes remaining
      some (BTreePageHeader.interiorTable decodedCommon decodedPage, suffix)
    | .leafIndex => some (BTreePageHeader.leafIndex decodedCommon, remaining)
    | .leafTable => some (BTreePageHeader.leafTable decodedCommon, remaining)) = _
  rw [decodeBTreePageType_typeByte]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeBTreePageHeaderCommon_encode]

private theorem decodeBTreePageHeader_encode_leafTable
    (common : BTreePageHeaderCommon) (suffix : List UInt8) :
    decodeBTreePageHeader (encodeBTreePageHeader (.leafTable common) ++ suffix) =
      some (.leafTable common, suffix) := by
  change (do
    let decodedType ← decodeBTreePageType BTreePageType.leafTable.typeByte
    let (decodedCommon, remaining) ← decodeBTreePageHeaderCommon
      (encodeBTreePageHeaderCommon common ++ suffix)
    match decodedType with
    | .interiorIndex => do
      let (decodedPage, suffix) ← decodeU32Bytes remaining
      some (BTreePageHeader.interiorIndex decodedCommon decodedPage, suffix)
    | .interiorTable => do
      let (decodedPage, suffix) ← decodeU32Bytes remaining
      some (BTreePageHeader.interiorTable decodedCommon decodedPage, suffix)
    | .leafIndex => some (BTreePageHeader.leafIndex decodedCommon, remaining)
    | .leafTable => some (BTreePageHeader.leafTable decodedCommon, remaining)) = _
  rw [decodeBTreePageType_typeByte]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeBTreePageHeaderCommon_encode]

theorem decodeBTreePageHeader_encode (header : BTreePageHeader) (suffix : List UInt8) :
    decodeBTreePageHeader (encodeBTreePageHeader header ++ suffix) =
      some (header, suffix) := by
  cases header with
  | interiorIndex common rightmostPage =>
      exact decodeBTreePageHeader_encode_interiorIndex common rightmostPage suffix
  | interiorTable common rightmostPage =>
      exact decodeBTreePageHeader_encode_interiorTable common rightmostPage suffix
  | leafIndex common => exact decodeBTreePageHeader_encode_leafIndex common suffix
  | leafTable common => exact decodeBTreePageHeader_encode_leafTable common suffix

/-- A zero content-start field denotes byte offset 65536. -/
def resolvedCellContentStart (common : BTreePageHeaderCommon) : Nat :=
  if common.cellContentStart.val = 0 then 65536 else common.cellContentStart.val

/-- Interior-page child references cannot use SQLite's reserved page number
zero. Bounds against the database page count are added by the pager layer. -/
def BTreePageHeader.childReferenceNonzero : BTreePageHeader → Prop
  | .interiorIndex _ rightmostPage | .interiorTable _ rightmostPage =>
    0 < rightmostPage.val
  | .leafIndex _ | .leafTable _ => True

instance (header : BTreePageHeader) : Decidable header.childReferenceNonzero := by
  cases header <;> simp [BTreePageHeader.childReferenceNonzero] <;> infer_instance

/-- Concrete safety conditions needed before following cell pointers. -/
def BTreePageHeader.WellFormed (pageSize : Nat) (header : BTreePageHeader) : Prop :=
  header.common.fragmentedFreeBytes.toNat ≤ 60 ∧
  (header.common.firstFreeblock.val = 0 ∨
    header.headerSize ≤ header.common.firstFreeblock.val) ∧
  header.headerSize + 2 * header.common.cellCount.val ≤
    resolvedCellContentStart header.common ∧
  resolvedCellContentStart header.common ≤ pageSize ∧
  header.childReferenceNonzero

/-- A decoded B-tree header bundled with the bounds needed for safe page use. -/
structure ValidBTreePageHeader (pageSize : Nat) where
  header : BTreePageHeader
  wellFormed : header.WellFormed pageSize
  deriving DecidableEq

instance (pageSize : Nat) (header : BTreePageHeader) :
    Decidable (header.WellFormed pageSize) := by
  unfold BTreePageHeader.WellFormed
  infer_instance

def decodeValidBTreePageHeader (pageSize : Nat) (input : List UInt8) :
    Option (ValidBTreePageHeader pageSize × List UInt8) := do
  let (header, suffix) ← decodeBTreePageHeader input
  if valid : header.WellFormed pageSize then
    some (⟨header, valid⟩, suffix)
  else none

theorem decodeValidBTreePageHeader_encode {pageSize : Nat}
    (header : ValidBTreePageHeader pageSize) (suffix : List UInt8) :
    decodeValidBTreePageHeader pageSize (encodeBTreePageHeader header.header ++ suffix) =
      some (header, suffix) := by
  unfold decodeValidBTreePageHeader
  rw [decodeBTreePageHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos header.wellFormed]

theorem ValidBTreePageHeader.pointerArrayEnd_le_page {pageSize : Nat}
    (header : ValidBTreePageHeader pageSize) :
    header.header.headerSize + 2 * header.header.common.cellCount.val ≤ pageSize := by
  exact Nat.le_trans header.wellFormed.2.2.1 header.wellFormed.2.2.2.1

structure SizedU16Values (count : Nat) where
  values : List U16Value
  length_eq : values.length = count
  deriving DecidableEq

def encodeU16Values (values : List U16Value) : List UInt8 :=
  values.flatMap encodeU16Bytes

def decodeSizedU16Values : (count : Nat) → List UInt8 →
    Option (SizedU16Values count × List UInt8)
  | 0, input => some (⟨[], rfl⟩, input)
  | count + 1, input => do
    let (value, afterValue) ← decodeU16Bytes input
    let (values, suffix) ← decodeSizedU16Values count afterValue
    some (⟨value :: values.values, by simp [values.length_eq]⟩, suffix)

theorem decodeSizedU16Values_encode {count : Nat} (values : SizedU16Values count)
    (suffix : List UInt8) :
    decodeSizedU16Values count (encodeU16Values values.values ++ suffix) =
      some (values, suffix) := by
  rcases values with ⟨items, lengthEquality⟩
  induction items generalizing count with
  | nil =>
      simp only [List.length_nil] at lengthEquality
      subst count
      rfl
  | cons item items induction =>
      cases count with
      | zero => simp at lengthEquality
      | succ count =>
          simp only [List.length_cons, Nat.succ.injEq] at lengthEquality
          simp only [encodeU16Values, List.flatMap_cons, List.append_assoc,
            decodeSizedU16Values]
          rw [decodeU16Bytes_encode]
          simp only [Option.bind_eq_bind, Option.bind]
          have tailDecoded :
              decodeSizedU16Values count (encodeU16Values items ++ suffix) =
                some (⟨items, lengthEquality⟩, suffix) :=
            induction (count := count) lengthEquality
          rw [show List.flatMap encodeU16Bytes items = encodeU16Values items by rfl]
          rw [tailDecoded]

theorem encodeU16Values_length (values : List U16Value) :
    (encodeU16Values values).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      change (encodeU16Bytes value ++ encodeU16Values values).length =
        2 * (value :: values).length
      simp only [List.length_append, encodeU16Bytes, List.length_cons,
        List.length_nil, induction]
      omega

def cellPointersWithin (pageSize contentStart : Nat) (pointers : List U16Value) : Bool :=
  pointers.all fun pointer => decide (contentStart ≤ pointer.val ∧ pointer.val < pageSize)

theorem cellPointersWithin_member {pageSize contentStart : Nat}
    {pointers : List U16Value} (valid : cellPointersWithin pageSize contentStart pointers)
    {pointer : U16Value} (member : pointer ∈ pointers) :
    contentStart ≤ pointer.val ∧ pointer.val < pageSize := by
  have checked := List.all_eq_true.mp valid pointer member
  simpa [cellPointersWithin] using checked

structure BTreePagePrefix (pageSize : Nat) where
  header : ValidBTreePageHeader pageSize
  pointers : SizedU16Values header.header.common.cellCount.val
  pointersWithin :
    cellPointersWithin pageSize (resolvedCellContentStart header.header.common)
      pointers.values
  deriving DecidableEq

def BTreePagePrefix.encode (pagePrefix : BTreePagePrefix pageSize) : List UInt8 :=
  encodeBTreePageHeader pagePrefix.header.header ++
    encodeU16Values pagePrefix.pointers.values

def decodeBTreePagePrefix (pageSize : Nat) (input : List UInt8) :
    Option (BTreePagePrefix pageSize × List UInt8) := do
  let (header, afterHeader) ← decodeValidBTreePageHeader pageSize input
  let (pointers, suffix) ←
    decodeSizedU16Values header.header.common.cellCount.val afterHeader
  if valid : cellPointersWithin pageSize
      (resolvedCellContentStart header.header.common) pointers.values then
    some (⟨header, pointers, valid⟩, suffix)
  else none

theorem BTreePagePrefix.encode_length (pagePrefix : BTreePagePrefix pageSize) :
    pagePrefix.encode.length = pagePrefix.header.header.headerSize +
      2 * pagePrefix.header.header.common.cellCount.val := by
  simp only [BTreePagePrefix.encode, List.length_append,
    encodeBTreePageHeader_length, encodeU16Values_length,
    pagePrefix.pointers.length_eq]

theorem decodeBTreePagePrefix_encode (pagePrefix : BTreePagePrefix pageSize)
    (suffix : List UInt8) :
    decodeBTreePagePrefix pageSize (pagePrefix.encode ++ suffix) =
      some (pagePrefix, suffix) := by
  unfold BTreePagePrefix.encode decodeBTreePagePrefix
  rw [List.append_assoc, decodeValidBTreePageHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeSizedU16Values_encode]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos pagePrefix.pointersWithin]

theorem BTreePagePrefix.pointerArrayEnd_le_content
    (pagePrefix : BTreePagePrefix pageSize) :
    pagePrefix.encode.length ≤
      resolvedCellContentStart pagePrefix.header.header.common := by
  rw [pagePrefix.encode_length]
  exact pagePrefix.header.wellFormed.2.2.1

end FileFormat

end SQLeanite
