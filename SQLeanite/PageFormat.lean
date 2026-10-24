import SQLeanite.Record
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

def signedInteger64Bits (value : SignedInteger .eight) : U64Value :=
  ⟨value.toUnsigned, by
    have bound := value.toUnsigned_lt
    simpa [IntegerWidth.modulus] using bound⟩

theorem signedIntegerFromBits_toBits (value : SignedInteger .eight) :
    signedIntegerFromUnsigned .eight (signedInteger64Bits value) = value := by
  unfold signedInteger64Bits
  exact signedIntegerFromUnsigned_toUnsigned value

/-- An interior table-B-tree cell contains a left-child page number and the
largest signed rowid key in that child. -/
structure InteriorTableCell where
  leftChildPage : PageNumber
  key : SignedInteger .eight
  deriving DecidableEq

def InteriorTableCell.encode (cell : InteriorTableCell) : List UInt8 :=
  cell.leftChildPage.encode ++ encodeVarint (signedInteger64Bits cell.key)

def decodeInteriorTableCell (input : List UInt8) :
    Option (InteriorTableCell × List UInt8) := do
  let (leftChildPage, afterChild) ← decodePageNumber input
  let (keyBits, suffix) ← decodeVarint afterChild
  let key := signedIntegerFromUnsigned .eight keyBits
  some (⟨leftChildPage, key⟩, suffix)

theorem decodeInteriorTableCell_encode (cell : InteriorTableCell)
    (suffix : List UInt8) :
    decodeInteriorTableCell (cell.encode ++ suffix) = some (cell, suffix) := by
  unfold InteriorTableCell.encode decodeInteriorTableCell
  rw [List.append_assoc, decodePageNumber_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [signedIntegerFromBits_toBits]

theorem InteriorTableCell.encode_length (cell : InteriorTableCell) :
    cell.encode.length = 4 + sqliteVarintSize cell.key.toUnsigned := by
  simp [InteriorTableCell.encode, encodeU32Bytes, encodeVarint_length,
    PageNumber.encode, signedInteger64Bits]
  omega

/-- A leaf table cell whose entire payload is local to the B-tree page. The
separate overflow codec will refine larger payloads into local and overflow
segments. -/
structure InlineTableLeafCell where
  payloadSize : U64Value
  rowid : SignedInteger .eight
  payload : SizedBytes payloadSize.val
  deriving DecidableEq

def InlineTableLeafCell.encode (cell : InlineTableLeafCell) : List UInt8 :=
  encodeVarint cell.payloadSize ++ encodeVarint (signedInteger64Bits cell.rowid) ++
    cell.payload.bytes

def decodeInlineTableLeafCell (input : List UInt8) :
    Option (InlineTableLeafCell × List UInt8) := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (rowidBits, afterRowid) ← decodeVarint afterSize
  let (payload, suffix) ← decodeSizedBytes payloadSize.val afterRowid
  let rowid := signedIntegerFromUnsigned .eight rowidBits
  some (⟨payloadSize, rowid, payload⟩, suffix)

theorem decodeInlineTableLeafCell_encode (cell : InlineTableLeafCell)
    (suffix : List UInt8) :
    decodeInlineTableLeafCell (cell.encode ++ suffix) = some (cell, suffix) := by
  unfold InlineTableLeafCell.encode decodeInlineTableLeafCell
  simp only [List.append_assoc]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeSizedBytes_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [signedIntegerFromBits_toBits]

theorem InlineTableLeafCell.encode_length (cell : InlineTableLeafCell) :
    cell.encode.length = sqliteVarintSize cell.payloadSize.val +
      sqliteVarintSize cell.rowid.toUnsigned + cell.payloadSize.val := by
  simp [InlineTableLeafCell.encode, encodeVarint_length, signedInteger64Bits,
    cell.payload.length_eq]
  omega

/-- SQLite requires at least 480 usable bytes on every database page. The
upper bound is the largest supported SQLite page size. -/
structure UsablePageSize where
  val : Nat
  atLeastMinimum : 480 ≤ val
  atMostMaximum : val ≤ 65536
  deriving DecidableEq

/-- Maximum payload stored locally by a table leaf cell before overflow. -/
def tableLeafMaxLocal (usable : UsablePageSize) : Nat := usable.val - 35

/-- Minimum local payload used by SQLite's balanced overflow formula. -/
def minLocalPayload (usable : UsablePageSize) : Nat :=
  ((usable.val - 12) * 32) / 255 - 23

/-- Bytes available for payload on each overflow page after its next-page
pointer. -/
def overflowPayloadCapacity (usable : UsablePageSize) : Nat := usable.val - 4

theorem UsablePageSize.overflowPayloadCapacity_pos (usable : UsablePageSize) :
    0 < overflowPayloadCapacity usable := by
  unfold overflowPayloadCapacity
  have minimum := usable.atLeastMinimum
  omega

theorem minLocalPayload_le_tableLeafMaxLocal (usable : UsablePageSize) :
    minLocalPayload usable ≤ tableLeafMaxLocal usable := by
  let n := usable.val - 12
  have hn : n * 32 ≤ n * 255 := by omega
  have hdiv : n * 32 / 255 ≤ n :=
    Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hn)
  unfold minLocalPayload tableLeafMaxLocal
  change n * 32 / 255 - 23 ≤ usable.val - 35
  omega

/-- SQLite's exact local-payload rule for a table B-tree leaf cell. When a
payload does not fit entirely, `K` is selected only when it is no larger than
the table-leaf maximum; otherwise the minimum local payload is selected. -/
def tableLeafLocalPayloadSize (usable : UsablePageSize) (payloadSize : Nat) : Nat :=
  let maxLocal := tableLeafMaxLocal usable
  if payloadSize ≤ maxLocal then
    payloadSize
  else
    let minLocal := minLocalPayload usable
    let candidate := minLocal +
      (payloadSize - minLocal) % overflowPayloadCapacity usable
    if candidate ≤ maxLocal then candidate else minLocal

theorem tableLeafLocalPayloadSize_eq_payload_of_fits
    (usable : UsablePageSize) (payloadSize : Nat)
    (fits : payloadSize ≤ tableLeafMaxLocal usable) :
    tableLeafLocalPayloadSize usable payloadSize = payloadSize := by
  simp [tableLeafLocalPayloadSize, fits]

theorem tableLeafLocalPayloadSize_le_max (usable : UsablePageSize)
    (payloadSize : Nat) :
    tableLeafLocalPayloadSize usable payloadSize ≤
      tableLeafMaxLocal usable := by
  by_cases fits : payloadSize ≤ tableLeafMaxLocal usable
  · simp [tableLeafLocalPayloadSize, fits]
  · simp only [tableLeafLocalPayloadSize, fits, ↓reduceIte]
    by_cases candidateFits : minLocalPayload usable +
        (payloadSize - minLocalPayload usable) %
          overflowPayloadCapacity usable ≤ tableLeafMaxLocal usable
    · simp [candidateFits]
    · simp [candidateFits, minLocalPayload_le_tableLeafMaxLocal]

theorem tableLeafLocalPayloadSize_le_payload (usable : UsablePageSize)
    (payloadSize : Nat) :
    tableLeafLocalPayloadSize usable payloadSize ≤ payloadSize := by
  have minLeMax := minLocalPayload_le_tableLeafMaxLocal usable
  by_cases fits : payloadSize ≤ tableLeafMaxLocal usable
  · simp [tableLeafLocalPayloadSize, fits]
  · have minLePayload : minLocalPayload usable ≤ payloadSize := by omega
    have remainderLe := Nat.mod_le
      (payloadSize - minLocalPayload usable) (overflowPayloadCapacity usable)
    simp only [tableLeafLocalPayloadSize, fits, ↓reduceIte]
    split <;> omega

theorem tableLeafLocalPayloadSize_lt_payload_of_overflow
    (usable : UsablePageSize) (payloadSize : Nat)
    (overflow : tableLeafMaxLocal usable < payloadSize) :
    tableLeafLocalPayloadSize usable payloadSize < payloadSize := by
  have localLeMax := tableLeafLocalPayloadSize_le_max usable payloadSize
  omega

theorem tableLeafLocalPayloadSize_le_usable (usable : UsablePageSize)
    (payloadSize : Nat) :
    tableLeafLocalPayloadSize usable payloadSize ≤ usable.val := by
  have localLeMax := tableLeafLocalPayloadSize_le_max usable payloadSize
  unfold tableLeafMaxLocal at localLeMax
  omega

/-- Maximum local payload for both leaf and interior index B-tree cells. -/
def indexMaxLocal (usable : UsablePageSize) : Nat :=
  ((usable.val - 12) * 64) / 255 - 23

theorem minLocalPayload_le_indexMaxLocal (usable : UsablePageSize) :
    minLocalPayload usable ≤ indexMaxLocal usable := by
  let n := usable.val - 12
  have divided : n * 32 / 255 ≤ n * 64 / 255 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    have lower := Nat.div_mul_le_self (n * 32) 255
    omega
  unfold minLocalPayload indexMaxLocal
  change n * 32 / 255 - 23 ≤ n * 64 / 255 - 23
  omega

def indexLocalPayloadSize (usable : UsablePageSize) (payloadSize : Nat) : Nat :=
  let maxLocal := indexMaxLocal usable
  if payloadSize ≤ maxLocal then
    payloadSize
  else
    let minLocal := minLocalPayload usable
    let candidate := minLocal +
      (payloadSize - minLocal) % overflowPayloadCapacity usable
    if candidate ≤ maxLocal then candidate else minLocal

theorem indexLocalPayloadSize_eq_payload_of_fits
    (usable : UsablePageSize) (payloadSize : Nat)
    (fits : payloadSize ≤ indexMaxLocal usable) :
    indexLocalPayloadSize usable payloadSize = payloadSize := by
  simp [indexLocalPayloadSize, fits]

theorem indexLocalPayloadSize_le_max (usable : UsablePageSize)
    (payloadSize : Nat) :
    indexLocalPayloadSize usable payloadSize ≤ indexMaxLocal usable := by
  by_cases fits : payloadSize ≤ indexMaxLocal usable
  · simp [indexLocalPayloadSize, fits]
  · simp only [indexLocalPayloadSize, fits, ↓reduceIte]
    by_cases candidateFits : minLocalPayload usable +
        (payloadSize - minLocalPayload usable) %
          overflowPayloadCapacity usable ≤ indexMaxLocal usable
    · simp [candidateFits]
    · simp [candidateFits, minLocalPayload_le_indexMaxLocal]

theorem indexLocalPayloadSize_le_payload (usable : UsablePageSize)
    (payloadSize : Nat) :
    indexLocalPayloadSize usable payloadSize ≤ payloadSize := by
  have minLeMax := minLocalPayload_le_indexMaxLocal usable
  by_cases fits : payloadSize ≤ indexMaxLocal usable
  · simp [indexLocalPayloadSize, fits]
  · have minLePayload : minLocalPayload usable ≤ payloadSize := by omega
    have remainderLe := Nat.mod_le
      (payloadSize - minLocalPayload usable) (overflowPayloadCapacity usable)
    simp only [indexLocalPayloadSize, fits, ↓reduceIte]
    split <;> omega

theorem indexLocalPayloadSize_lt_payload_of_overflow
    (usable : UsablePageSize) (payloadSize : Nat)
    (overflow : indexMaxLocal usable < payloadSize) :
    indexLocalPayloadSize usable payloadSize < payloadSize := by
  have localLeMax := indexLocalPayloadSize_le_max usable payloadSize
  omega

theorem indexLocalPayloadSize_le_usable (usable : UsablePageSize)
    (payloadSize : Nat) : indexLocalPayloadSize usable payloadSize ≤ usable.val := by
  let n := usable.val - 12
  have numerator : n * 64 ≤ 255 * n := by omega
  have divided : n * 64 / 255 ≤ n := Nat.div_le_of_le_mul numerator
  have localLeMax := indexLocalPayloadSize_le_max usable payloadSize
  unfold indexMaxLocal at localLeMax
  change indexLocalPayloadSize usable payloadSize ≤ n * 64 / 255 - 23 at localLeMax
  omega

/-- Unchecked physical alternatives for the bytes stored in a table leaf
cell. `TableLeafPayload` below admits only alternatives satisfying SQLite's
local-payload rule. -/
inductive BTreePayloadData where
  | inline (bytes : List UInt8)
  | overflow (localBytes : List UInt8) (firstOverflowPage : PageNumber)
  deriving DecidableEq

def BTreePayloadData.TableLeafWellFormed (usable : UsablePageSize)
    (payloadSize : Nat) : BTreePayloadData → Prop
  | .inline bytes =>
    payloadSize ≤ tableLeafMaxLocal usable ∧ bytes.length = payloadSize
  | .overflow localBytes _ =>
    tableLeafMaxLocal usable < payloadSize ∧
      localBytes.length = tableLeafLocalPayloadSize usable payloadSize

instance (usable : UsablePageSize) (payloadSize : Nat)
    (data : BTreePayloadData) :
    Decidable (data.TableLeafWellFormed usable payloadSize) := by
  cases data <;> simp [BTreePayloadData.TableLeafWellFormed] <;> infer_instance

/-- The bytes physically stored in a table leaf cell. Its proof field ensures
a fitting payload is stored in full, while an overflowing payload stores
exactly SQLite's calculated local prefix and a nonzero overflow page. -/
structure TableLeafPayload (usable : UsablePageSize) (payloadSize : Nat) where
  data : BTreePayloadData
  wellFormed : data.TableLeafWellFormed usable payloadSize
  deriving DecidableEq

def TableLeafPayload.encode {usable : UsablePageSize} {payloadSize : Nat}
    (payload : TableLeafPayload usable payloadSize) : List UInt8 :=
  match payload.data with
  | .inline bytes => bytes
  | .overflow localBytes firstOverflowPage =>
    localBytes ++ firstOverflowPage.encode

def decodeTableLeafPayload (usable : UsablePageSize) (payloadSize : Nat)
    (input : List UInt8) :
    Option (TableLeafPayload usable payloadSize × List UInt8) :=
  if fits : payloadSize ≤ tableLeafMaxLocal usable then do
    let (payload, suffix) ← decodeSizedBytes payloadSize input
    let decoded : TableLeafPayload usable payloadSize := {
      data := .inline payload.bytes
      wellFormed := ⟨fits, payload.length_eq⟩ }
    some (decoded, suffix)
  else do
    let (localPayload, afterLocal) ←
      decodeSizedBytes (tableLeafLocalPayloadSize usable payloadSize) input
    let (firstOverflowPage, suffix) ← decodePageNumber afterLocal
    have overflows : tableLeafMaxLocal usable < payloadSize :=
      Nat.lt_of_not_ge fits
    let decoded : TableLeafPayload usable payloadSize := {
      data := .overflow localPayload.bytes firstOverflowPage
      wellFormed := ⟨overflows, localPayload.length_eq⟩ }
    some (decoded, suffix)

theorem decodeTableLeafPayload_encode_inline {usable : UsablePageSize}
    {payloadSize : Nat} (bytes : List UInt8)
    (wellFormed :
      (BTreePayloadData.inline bytes).TableLeafWellFormed usable payloadSize)
    (suffix : List UInt8) :
    let payload : TableLeafPayload usable payloadSize :=
      ⟨.inline bytes, wellFormed⟩
    decodeTableLeafPayload usable payloadSize (payload.encode ++ suffix) =
      some (payload, suffix) := by
  dsimp only
  let sized : SizedBytes payloadSize := ⟨bytes, wellFormed.2⟩
  have decoded := decodeSizedBytes_append sized suffix
  unfold TableLeafPayload.encode decodeTableLeafPayload
  rw [dif_pos wellFormed.1]
  rw [decoded]
  congr

theorem TableLeafPayload.encode_length {usable : UsablePageSize}
    {payloadSize : Nat} (payload : TableLeafPayload usable payloadSize) :
    payload.encode.length =
      match payload.data with
      | .inline _ => payloadSize
      | .overflow _ _ =>
        tableLeafLocalPayloadSize usable payloadSize + 4 := by
  rcases payload with ⟨data, wellFormed⟩
  cases data with
  | inline bytes =>
      exact wellFormed.2
  | overflow localBytes firstOverflowPage =>
      simp [TableLeafPayload.encode, wellFormed.2,
        PageNumber.encode, encodeU32Bytes]

/-- A complete table B-tree leaf cell, including the overflow pointer exactly
when the payload cannot fit locally. -/
structure TableLeafCell (usable : UsablePageSize) where
  payloadSize : U64Value
  rowid : SignedInteger .eight
  payload : TableLeafPayload usable payloadSize.val
  deriving DecidableEq

def TableLeafCell.encode {usable : UsablePageSize}
    (cell : TableLeafCell usable) : List UInt8 :=
  encodeVarint cell.payloadSize ++ encodeVarint (signedInteger64Bits cell.rowid) ++
    cell.payload.encode

def decodeTableLeafCell (usable : UsablePageSize) (input : List UInt8) :
    Option (TableLeafCell usable × List UInt8) := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (rowidBits, afterRowid) ← decodeVarint afterSize
  let (payload, suffix) ←
    decodeTableLeafPayload usable payloadSize.val afterRowid
  let rowid := signedIntegerFromUnsigned .eight rowidBits
  some (⟨payloadSize, rowid, payload⟩, suffix)

theorem TableLeafCell.encode_length {usable : UsablePageSize}
    (cell : TableLeafCell usable) :
    cell.encode.length = sqliteVarintSize cell.payloadSize.val +
      sqliteVarintSize cell.rowid.toUnsigned + cell.payload.encode.length := by
  simp [TableLeafCell.encode, encodeVarint_length, signedInteger64Bits]
  omega

def BTreePayloadData.IndexWellFormed (usable : UsablePageSize)
    (payloadSize : Nat) : BTreePayloadData → Prop
  | .inline bytes =>
    payloadSize ≤ indexMaxLocal usable ∧ bytes.length = payloadSize
  | .overflow localBytes _ =>
    indexMaxLocal usable < payloadSize ∧
      localBytes.length = indexLocalPayloadSize usable payloadSize

instance (usable : UsablePageSize) (payloadSize : Nat)
    (data : BTreePayloadData) :
    Decidable (data.IndexWellFormed usable payloadSize) := by
  cases data <;> simp [BTreePayloadData.IndexWellFormed] <;> infer_instance

/-- Physical payload shared by leaf and interior index cells, checked against
SQLite's index-page local-payload formula. -/
structure IndexPayload (usable : UsablePageSize) (payloadSize : Nat) where
  data : BTreePayloadData
  wellFormed : data.IndexWellFormed usable payloadSize
  deriving DecidableEq

def IndexPayload.encode {usable : UsablePageSize} {payloadSize : Nat}
    (payload : IndexPayload usable payloadSize) : List UInt8 :=
  match payload.data with
  | .inline bytes => bytes
  | .overflow localBytes firstOverflowPage =>
    localBytes ++ firstOverflowPage.encode

def decodeIndexPayload (usable : UsablePageSize) (payloadSize : Nat)
    (input : List UInt8) : Option (IndexPayload usable payloadSize × List UInt8) :=
  if fits : payloadSize ≤ indexMaxLocal usable then do
    let (payload, suffix) ← decodeSizedBytes payloadSize input
    let decoded : IndexPayload usable payloadSize := {
      data := .inline payload.bytes
      wellFormed := ⟨fits, payload.length_eq⟩ }
    some (decoded, suffix)
  else do
    let (localPayload, afterLocal) ←
      decodeSizedBytes (indexLocalPayloadSize usable payloadSize) input
    let (firstOverflowPage, suffix) ← decodePageNumber afterLocal
    have overflows : indexMaxLocal usable < payloadSize := Nat.lt_of_not_ge fits
    let decoded : IndexPayload usable payloadSize := {
      data := .overflow localPayload.bytes firstOverflowPage
      wellFormed := ⟨overflows, localPayload.length_eq⟩ }
    some (decoded, suffix)

theorem decodeIndexPayload_encode_inline {usable : UsablePageSize}
    {payloadSize : Nat} (bytes : List UInt8)
    (wellFormed : (BTreePayloadData.inline bytes).IndexWellFormed
      usable payloadSize) (suffix : List UInt8) :
    let payload : IndexPayload usable payloadSize := ⟨.inline bytes, wellFormed⟩
    decodeIndexPayload usable payloadSize (payload.encode ++ suffix) =
      some (payload, suffix) := by
  dsimp only
  let sized : SizedBytes payloadSize := ⟨bytes, wellFormed.2⟩
  have decoded := decodeSizedBytes_append sized suffix
  unfold IndexPayload.encode decodeIndexPayload
  rw [dif_pos wellFormed.1]
  rw [decoded]
  congr

theorem IndexPayload.encode_length {usable : UsablePageSize}
    {payloadSize : Nat} (payload : IndexPayload usable payloadSize) :
    payload.encode.length =
      match payload.data with
      | .inline _ => payloadSize
      | .overflow _ _ => indexLocalPayloadSize usable payloadSize + 4 := by
  rcases payload with ⟨data, wellFormed⟩
  cases data with
  | inline bytes => exact wellFormed.2
  | overflow localBytes firstOverflowPage =>
      simp [IndexPayload.encode, wellFormed.2,
        PageNumber.encode, encodeU32Bytes]

structure LeafIndexCell (usable : UsablePageSize) where
  payloadSize : U64Value
  payload : IndexPayload usable payloadSize.val
  deriving DecidableEq

def LeafIndexCell.encode {usable : UsablePageSize}
    (cell : LeafIndexCell usable) : List UInt8 :=
  encodeVarint cell.payloadSize ++ cell.payload.encode

def decodeLeafIndexCell (usable : UsablePageSize) (input : List UInt8) :
    Option (LeafIndexCell usable × List UInt8) := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (payload, suffix) ← decodeIndexPayload usable payloadSize.val afterSize
  some (⟨payloadSize, payload⟩, suffix)

theorem LeafIndexCell.encode_length {usable : UsablePageSize}
    (cell : LeafIndexCell usable) :
    cell.encode.length = sqliteVarintSize cell.payloadSize.val +
      cell.payload.encode.length := by
  simp [LeafIndexCell.encode, encodeVarint_length]

theorem decodeLeafIndexCell_encode_inline {usable : UsablePageSize}
    (payloadSize : U64Value) (bytes : List UInt8)
    (wellFormed : (BTreePayloadData.inline bytes).IndexWellFormed
      usable payloadSize.val) (suffix : List UInt8) :
    let payload : IndexPayload usable payloadSize.val := ⟨.inline bytes, wellFormed⟩
    let cell : LeafIndexCell usable := ⟨payloadSize, payload⟩
    decodeLeafIndexCell usable (cell.encode ++ suffix) = some (cell, suffix) := by
  dsimp only
  unfold LeafIndexCell.encode decodeLeafIndexCell
  rw [List.append_assoc, decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeIndexPayload_encode_inline]

structure InteriorIndexCell (usable : UsablePageSize) where
  leftChildPage : PageNumber
  payloadSize : U64Value
  payload : IndexPayload usable payloadSize.val
  deriving DecidableEq

def InteriorIndexCell.encode {usable : UsablePageSize}
    (cell : InteriorIndexCell usable) : List UInt8 :=
  cell.leftChildPage.encode ++ encodeVarint cell.payloadSize ++ cell.payload.encode

def decodeInteriorIndexCell (usable : UsablePageSize) (input : List UInt8) :
    Option (InteriorIndexCell usable × List UInt8) := do
  let (leftChildPage, afterChild) ← decodePageNumber input
  let (payloadSize, afterSize) ← decodeVarint afterChild
  let (payload, suffix) ← decodeIndexPayload usable payloadSize.val afterSize
  some (⟨leftChildPage, payloadSize, payload⟩, suffix)

theorem InteriorIndexCell.encode_length {usable : UsablePageSize}
    (cell : InteriorIndexCell usable) :
    cell.encode.length = 4 + sqliteVarintSize cell.payloadSize.val +
      cell.payload.encode.length := by
  simp [InteriorIndexCell.encode, PageNumber.encode, encodeU32Bytes,
    encodeVarint_length]
  omega

theorem decodeInteriorIndexCell_encode_inline {usable : UsablePageSize}
    (leftChildPage : PageNumber) (payloadSize : U64Value) (bytes : List UInt8)
    (wellFormed : (BTreePayloadData.inline bytes).IndexWellFormed
      usable payloadSize.val) (suffix : List UInt8) :
    let payload : IndexPayload usable payloadSize.val := ⟨.inline bytes, wellFormed⟩
    let cell : InteriorIndexCell usable :=
      ⟨leftChildPage, payloadSize, payload⟩
    decodeInteriorIndexCell usable (cell.encode ++ suffix) =
      some (cell, suffix) := by
  dsimp only
  unfold InteriorIndexCell.encode decodeInteriorIndexCell
  simp only [List.append_assoc]
  rw [decodePageNumber_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeIndexPayload_encode_inline]

/-- The first word of an overflow page is either zero, terminating the chain,
or a positive 32-bit database page number. -/
inductive OverflowNext where
  | endOfChain
  | page (number : PageNumber)
  deriving Repr, DecidableEq

def OverflowNext.encode : OverflowNext → List UInt8
  | .endOfChain => encodeU32Bytes ⟨0, by omega⟩
  | .page number => number.encode

def decodeOverflowNext (input : List UInt8) :
    Option (OverflowNext × List UInt8) := do
  let (value, suffix) ← decodeU32Bytes input
  if zero : value.val = 0 then
    some (.endOfChain, suffix)
  else
    have positive : 0 < value.val := Nat.pos_of_ne_zero zero
    some (.page ⟨value, positive⟩, suffix)

theorem decodeOverflowNext_encode (next : OverflowNext) (suffix : List UInt8) :
    decodeOverflowNext (next.encode ++ suffix) = some (next, suffix) := by
  cases next with
  | endOfChain =>
      unfold OverflowNext.encode decodeOverflowNext
      rw [decodeU32Bytes_encode]
      simp
  | page number =>
      unfold OverflowNext.encode decodeOverflowNext PageNumber.encode
      rw [decodeU32Bytes_encode]
      simp only [bind, Option.bind]
      rw [dif_neg (Nat.ne_of_gt number.positive)]

theorem OverflowNext.encode_length (next : OverflowNext) :
    next.encode.length = 4 := by
  cases next <;> simp [OverflowNext.encode, PageNumber.encode, encodeU32Bytes]

/-- A raw SQLite overflow page over its usable bytes. The final page's unused
payload tail is retained physically; a higher-level chain supplies the logical
payload length. -/
structure OverflowPage (usable : UsablePageSize) where
  next : OverflowNext
  payload : SizedBytes (overflowPayloadCapacity usable)
  deriving DecidableEq

def OverflowPage.encode {usable : UsablePageSize}
    (page : OverflowPage usable) : List UInt8 :=
  page.next.encode ++ page.payload.bytes

def decodeOverflowPage (usable : UsablePageSize) (input : List UInt8) :
    Option (OverflowPage usable × List UInt8) := do
  let (next, afterNext) ← decodeOverflowNext input
  let (payload, suffix) ←
    decodeSizedBytes (overflowPayloadCapacity usable) afterNext
  some (⟨next, payload⟩, suffix)

theorem decodeOverflowPage_encode {usable : UsablePageSize}
    (page : OverflowPage usable) (suffix : List UInt8) :
    decodeOverflowPage usable (page.encode ++ suffix) = some (page, suffix) := by
  unfold OverflowPage.encode decodeOverflowPage
  rw [List.append_assoc, decodeOverflowNext_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeSizedBytes_append]

theorem OverflowPage.encode_length {usable : UsablePageSize}
    (page : OverflowPage usable) :
    page.encode.length = usable.val := by
  simp [OverflowPage.encode, page.next.encode_length, page.payload.length_eq,
    overflowPayloadCapacity]
  have minimum := usable.atLeastMinimum
  omega

/-- Logical overflow-chain data. Every non-final page contributes its complete
payload capacity; the final page records how many of its physical payload bytes
belong to the logical record. -/
inductive OverflowChainData (usable : UsablePageSize) where
  | last (number : PageNumber)
      (payload : SizedBytes (overflowPayloadCapacity usable))
      (used : Nat) (used_le : used ≤ overflowPayloadCapacity usable)
  | link (number : PageNumber)
      (payload : SizedBytes (overflowPayloadCapacity usable))
      (tail : OverflowChainData usable)
  deriving DecidableEq

def OverflowChainData.firstPage {usable : UsablePageSize} :
    OverflowChainData usable → PageNumber
  | .last number _ _ _ | .link number _ _ => number

def OverflowChainData.pageNumbers {usable : UsablePageSize} :
    OverflowChainData usable → List PageNumber
  | .last number _ _ _ => [number]
  | .link number _ tail => number :: tail.pageNumbers

def OverflowChainData.pageCount {usable : UsablePageSize} :
    OverflowChainData usable → Nat
  | .last _ _ _ _ => 1
  | .link _ _ tail => tail.pageCount + 1

/-- Reconstruct the physical pages, deriving every next pointer from the
following page rather than trusting separately supplied linkage metadata. -/
def OverflowChainData.toPages {usable : UsablePageSize} :
    OverflowChainData usable → List (PageNumber × OverflowPage usable)
  | .last number payload _ _ => [(number, ⟨.endOfChain, payload⟩)]
  | .link number payload tail =>
    (number, ⟨.page tail.firstPage, payload⟩) :: tail.toPages

def OverflowChainData.logicalPayload {usable : UsablePageSize} :
    OverflowChainData usable → List UInt8
  | .last _ payload used _ => payload.bytes.take used
  | .link _ payload tail => payload.bytes ++ tail.logicalPayload

def OverflowChainData.logicalPayloadSize {usable : UsablePageSize} :
    OverflowChainData usable → Nat
  | .last _ _ used _ => used
  | .link _ _ tail => overflowPayloadCapacity usable + tail.logicalPayloadSize

/-- Adjacent physical overflow pages point to one another and the last page
uses the zero end-of-chain sentinel. -/
def OverflowPagesLinked {usable : UsablePageSize} :
    List (PageNumber × OverflowPage usable) → Prop
  | [] => False
  | [(_, page)] => page.next = .endOfChain
  | (_, page) :: (nextNumber, nextPage) :: tail =>
    page.next = .page nextNumber ∧
      OverflowPagesLinked ((nextNumber, nextPage) :: tail)

theorem OverflowChainData.pageCount_pos {usable : UsablePageSize}
    (chain : OverflowChainData usable) : 0 < chain.pageCount := by
  cases chain <;> simp [OverflowChainData.pageCount]

theorem OverflowChainData.toPages_length {usable : UsablePageSize}
    (chain : OverflowChainData usable) :
    chain.toPages.length = chain.pageCount := by
  induction chain with
  | last => rfl
  | link number payload tail induction =>
      simp [OverflowChainData.toPages, OverflowChainData.pageCount, induction]

theorem OverflowChainData.toPages_pageNumbers {usable : UsablePageSize}
    (chain : OverflowChainData usable) :
    chain.toPages.map Prod.fst = chain.pageNumbers := by
  induction chain with
  | last => rfl
  | link number payload tail induction =>
      simp [OverflowChainData.toPages, OverflowChainData.pageNumbers, induction]

theorem OverflowChainData.logicalPayload_length {usable : UsablePageSize}
    (chain : OverflowChainData usable) :
    chain.logicalPayload.length = chain.logicalPayloadSize := by
  induction chain with
  | last number payload used used_le =>
      simp [OverflowChainData.logicalPayload,
        OverflowChainData.logicalPayloadSize, payload.length_eq, used_le]
  | link number payload tail induction =>
      simp [OverflowChainData.logicalPayload,
        OverflowChainData.logicalPayloadSize, payload.length_eq, induction]

theorem OverflowChainData.toPages_linked {usable : UsablePageSize}
    (chain : OverflowChainData usable) : OverflowPagesLinked chain.toPages := by
  induction chain with
  | last => rfl
  | link number payload tail induction =>
      cases tail <;>
        simp [OverflowChainData.toPages, OverflowChainData.firstPage,
          OverflowPagesLinked] at induction ⊢ <;>
        assumption

/-- An overflow chain with no repeated page number. Together with `toPages`,
this excludes cycles and makes all linkage correct by construction. -/
structure OverflowChain (usable : UsablePageSize) where
  data : OverflowChainData usable
  acyclic : data.pageNumbers.Nodup
  deriving DecidableEq

def OverflowChain.firstPage {usable : UsablePageSize}
    (chain : OverflowChain usable) : PageNumber := chain.data.firstPage

def OverflowChain.toPages {usable : UsablePageSize}
    (chain : OverflowChain usable) : List (PageNumber × OverflowPage usable) :=
  chain.data.toPages

def OverflowChain.logicalPayload {usable : UsablePageSize}
    (chain : OverflowChain usable) : List UInt8 := chain.data.logicalPayload

theorem OverflowChain.pageNumbers_nodup {usable : UsablePageSize}
    (chain : OverflowChain usable) : chain.data.pageNumbers.Nodup :=
  chain.acyclic

theorem OverflowChain.pages_linked {usable : UsablePageSize}
    (chain : OverflowChain usable) : OverflowPagesLinked chain.toPages :=
  chain.data.toPages_linked

theorem OverflowChain.toPages_nonempty {usable : UsablePageSize}
    (chain : OverflowChain usable) : chain.toPages ≠ [] := by
  intro empty
  have lengthPositive := chain.data.pageCount_pos
  have lengthEquality := chain.data.toPages_length
  unfold OverflowChain.toPages at empty
  rw [empty] at lengthEquality
  simp at lengthEquality
  omega

theorem OverflowChain.logicalPayload_length {usable : UsablePageSize}
    (chain : OverflowChain usable) :
    chain.logicalPayload.length = chain.data.logicalPayloadSize :=
  chain.data.logicalPayload_length

/-- Connect a table leaf cell to its overflow storage. Inline cells must have
no chain. Overflowing cells must point at the chain's first page, and local plus
overflow bytes must equal the payload size announced by the cell. -/
def TableLeafCell.ChainResolved {usable : UsablePageSize}
    (cell : TableLeafCell usable) (chain : Option (OverflowChain usable)) : Prop :=
  match cell.payload.data, chain with
  | .inline _, none => True
  | .overflow localBytes firstOverflowPage, some chain =>
    chain.firstPage = firstOverflowPage ∧
      localBytes.length + chain.logicalPayload.length = cell.payloadSize.val
  | _, _ => False

instance {usable : UsablePageSize} (cell : TableLeafCell usable)
    (chain : Option (OverflowChain usable)) :
    Decidable (cell.ChainResolved chain) := by
  unfold TableLeafCell.ChainResolved
  split <;> infer_instance

structure ResolvedTableLeafCell (usable : UsablePageSize) where
  cell : TableLeafCell usable
  chain : Option (OverflowChain usable)
  resolved : cell.ChainResolved chain
  deriving DecidableEq

def ResolvedTableLeafCell.logicalPayload {usable : UsablePageSize}
    (resolvedCell : ResolvedTableLeafCell usable) : List UInt8 :=
  match resolvedCell.cell.payload.data, resolvedCell.chain with
  | .inline bytes, none => bytes
  | .overflow localBytes _, some chain => localBytes ++ chain.logicalPayload
  | _, _ => []

theorem ResolvedTableLeafCell.logicalPayload_length {usable : UsablePageSize}
    (resolvedCell : ResolvedTableLeafCell usable) :
    resolvedCell.logicalPayload.length = resolvedCell.cell.payloadSize.val := by
  rcases resolvedCell with ⟨cell, chain, resolved⟩
  rcases cell with ⟨payloadSize, rowid, payload⟩
  rcases payload with ⟨data, payloadWellFormed⟩
  cases data <;> cases chain <;>
    simp [ResolvedTableLeafCell.logicalPayload,
      TableLeafCell.ChainResolved] at resolved ⊢
  · exact payloadWellFormed.2
  · omega

/-- A physical cell byte interval placed within one database page. -/
structure PlacedCell (pageSize : Nat) where
  offset : U16Value
  bytes : List UInt8
  nonempty : bytes ≠ []
  endWithinPage : offset.val + bytes.length ≤ pageSize
  deriving DecidableEq

def PlacedCell.endOffset {pageSize : Nat} (cell : PlacedCell pageSize) : Nat :=
  cell.offset.val + cell.bytes.length

def PlacedCell.Contains {pageSize : Nat} (cell : PlacedCell pageSize)
    (byteOffset : Nat) : Prop :=
  cell.offset.val ≤ byteOffset ∧ byteOffset < cell.endOffset

instance {pageSize : Nat} (cell : PlacedCell pageSize) (byteOffset : Nat) :
    Decidable (cell.Contains byteOffset) := by
  unfold PlacedCell.Contains PlacedCell.endOffset
  infer_instance

def PlacedCell.Disjoint {pageSize : Nat}
    (left right : PlacedCell pageSize) : Prop :=
  left.endOffset ≤ right.offset.val ∨ right.endOffset ≤ left.offset.val

instance {pageSize : Nat} (left right : PlacedCell pageSize) :
    Decidable (left.Disjoint right) := by
  unfold PlacedCell.Disjoint PlacedCell.endOffset
  infer_instance

theorem PlacedCell.Disjoint.symm {pageSize : Nat}
    {left right : PlacedCell pageSize} (disjoint : left.Disjoint right) :
    right.Disjoint left := by
  unfold PlacedCell.Disjoint at disjoint ⊢
  exact disjoint.elim Or.inr Or.inl

theorem PlacedCell.Disjoint.not_both_contains {pageSize byteOffset : Nat}
    {left right : PlacedCell pageSize} (disjoint : left.Disjoint right) :
    ¬(left.Contains byteOffset ∧ right.Contains byteOffset) := by
  unfold PlacedCell.Disjoint PlacedCell.endOffset at disjoint
  unfold PlacedCell.Contains PlacedCell.endOffset
  omega

/-- A page prefix connected to concrete cell intervals. Pointer agreement
ensures every encoded pointer selects the corresponding cell; the remaining
fields exclude prefix overlap and cell-to-cell overlap. -/
structure BTreeCellLayout (pageSize : Nat) where
  pagePrefix : BTreePagePrefix pageSize
  cells : List (PlacedCell pageSize)
  pointerAgreement : cells.map (fun cell => cell.offset) = pagePrefix.pointers.values
  afterPrefix : ∀ cell ∈ cells, pagePrefix.encode.length ≤ cell.offset.val
  pairwiseDisjoint : cells.Pairwise PlacedCell.Disjoint
  deriving DecidableEq

theorem BTreeCellLayout.cellCount_eq {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) :
    layout.cells.length = layout.pagePrefix.header.header.common.cellCount.val := by
  have lengths := congrArg List.length layout.pointerAgreement
  simpa [layout.pagePrefix.pointers.length_eq] using lengths

theorem BTreeCellLayout.every_cell_within_page {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (cell : PlacedCell pageSize)
    (_member : cell ∈ layout.cells) : cell.endOffset ≤ pageSize := by
  exact cell.endWithinPage

theorem BTreeCellLayout.every_cell_after_prefix {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (cell : PlacedCell pageSize)
    (member : cell ∈ layout.cells) :
    layout.pagePrefix.encode.length ≤ cell.offset.val :=
  layout.afterPrefix cell member

private def cellByteAt? {pageSize : Nat} :
    List (PlacedCell pageSize) → Nat → Option UInt8
  | [], _ => none
  | cell :: cells, byteOffset =>
    if cell.Contains byteOffset then
      cell.bytes[byteOffset - cell.offset.val]?
    else
      cellByteAt? cells byteOffset

theorem PlacedCell.Contains.relative_lt {pageSize byteOffset : Nat}
    {cell : PlacedCell pageSize} (contains : cell.Contains byteOffset) :
    byteOffset - cell.offset.val < cell.bytes.length := by
  unfold PlacedCell.Contains PlacedCell.endOffset at contains
  omega

private theorem cellByteAt?_eq_of_mem {pageSize byteOffset : Nat}
    {cells : List (PlacedCell pageSize)} (pairwise : cells.Pairwise PlacedCell.Disjoint)
    {cell : PlacedCell pageSize} (member : cell ∈ cells)
    (contains : cell.Contains byteOffset) :
    cellByteAt? cells byteOffset =
      some (cell.bytes.get
        ⟨byteOffset - cell.offset.val, contains.relative_lt⟩) := by
  induction cells with
  | nil => simp at member
  | cons head tail induction =>
      have headRelations := (List.pairwise_cons.mp pairwise).1
      have tailPairwise := (List.pairwise_cons.mp pairwise).2
      rcases List.mem_cons.mp member with same | inTail
      · subst head
        unfold cellByteAt?
        rw [if_pos contains]
        simp [getElem?_def, contains.relative_lt]
      · have disjoint := headRelations cell inTail
        have headDoesNotContain : ¬ head.Contains byteOffset := by
          intro headContains
          exact disjoint.not_both_contains ⟨headContains, contains⟩
        unfold cellByteAt?
        rw [if_neg headDoesNotContain]
        exact induction tailPairwise inTail

def BTreeCellLayout.byteAt {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (byteOffset : Nat) : UInt8 :=
  match layout.pagePrefix.encode[byteOffset]? with
  | some byte => byte
  | none => (cellByteAt? layout.cells byteOffset).getD 0

/-- Materialize a validated layout as an exact-size storage page. Bytes not
occupied by the prefix or a cell are deterministically zero-filled. -/
def BTreeCellLayout.encodePage {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) : Storage.Page pageSize := {
  bytes := Array.ofFn (fun offset : Fin pageSize => layout.byteAt offset.val)
  sizeInvariant := by simp }

theorem BTreeCellLayout.encodePage_size {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) :
    layout.encodePage.bytes.size = pageSize :=
  layout.encodePage.sizeInvariant

theorem BTreeCellLayout.byteAt_prefix {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (byteOffset : Nat)
    (withinPrefix : byteOffset < layout.pagePrefix.encode.length) :
    layout.byteAt byteOffset =
      layout.pagePrefix.encode.get ⟨byteOffset, withinPrefix⟩ := by
  unfold BTreeCellLayout.byteAt
  simp [getElem?_def, withinPrefix]

theorem BTreeCellLayout.byteAt_cell {pageSize : Nat}
    (layout : BTreeCellLayout pageSize) (cell : PlacedCell pageSize)
    (member : cell ∈ layout.cells) (byteOffset : Nat)
    (contains : cell.Contains byteOffset) :
    layout.byteAt byteOffset =
      cell.bytes.get ⟨byteOffset - cell.offset.val, contains.relative_lt⟩ := by
  have prefixBeforeCell := layout.afterPrefix cell member
  have prefixBeforeOffset : layout.pagePrefix.encode.length ≤ byteOffset := by
    exact Nat.le_trans prefixBeforeCell contains.1
  unfold BTreeCellLayout.byteAt
  simp only [getElem?_def, Nat.not_lt_of_ge prefixBeforeOffset, ↓reduceDIte]
  rw [cellByteAt?_eq_of_mem layout.pairwiseDisjoint member contains]
  rfl

inductive BTreeCellBody (usable : UsablePageSize) where
  | interiorTable (cell : InteriorTableCell)
  | leafTable (cell : TableLeafCell usable)
  | interiorIndex (cell : InteriorIndexCell usable)
  | leafIndex (cell : LeafIndexCell usable)
  deriving DecidableEq

def BTreeCellBody.pageType {usable : UsablePageSize} :
    BTreeCellBody usable → BTreePageType
  | .interiorTable _ => .interiorTable
  | .leafTable _ => .leafTable
  | .interiorIndex _ => .interiorIndex
  | .leafIndex _ => .leafIndex

def BTreeCellBody.encode {usable : UsablePageSize} :
    BTreeCellBody usable → List UInt8
  | .interiorTable cell => cell.encode
  | .leafTable cell => cell.encode
  | .interiorIndex cell => cell.encode
  | .leafIndex cell => cell.encode

theorem BTreeCellBody.encode_length_pos {usable : UsablePageSize}
    (body : BTreeCellBody usable) : 0 < body.encode.length := by
  cases body with
  | interiorTable cell =>
      change 0 < cell.encode.length
      rw [InteriorTableCell.encode_length]
      omega
  | leafTable cell =>
      change 0 < cell.encode.length
      rw [TableLeafCell.encode_length]
      have sizePositive := sqliteVarintSize_positive cell.payloadSize.val
      omega
  | interiorIndex cell =>
      change 0 < cell.encode.length
      rw [InteriorIndexCell.encode_length]
      omega
  | leafIndex cell =>
      change 0 < cell.encode.length
      rw [LeafIndexCell.encode_length]
      have sizePositive := sqliteVarintSize_positive cell.payloadSize.val
      omega

theorem BTreeCellBody.encode_ne_nil {usable : UsablePageSize}
    (body : BTreeCellBody usable) : body.encode ≠ [] := by
  intro empty
  have positive := body.encode_length_pos
  rw [empty] at positive
  simp at positive

/-- A typed cell can only inhabit the matching kind of B-tree page. -/
structure TypedBTreeCell (usable : UsablePageSize) (pageType : BTreePageType) where
  offset : U16Value
  body : BTreeCellBody usable
  matchesPage : body.pageType = pageType
  endWithinPage : offset.val + body.encode.length ≤ usable.val
  deriving DecidableEq

def TypedBTreeCell.toPlacedCell {usable : UsablePageSize}
    {pageType : BTreePageType} (cell : TypedBTreeCell usable pageType) :
    PlacedCell usable.val := {
  offset := cell.offset
  bytes := cell.body.encode
  nonempty := cell.body.encode_ne_nil
  endWithinPage := cell.endWithinPage }

/-- Typed cells paired with the generic layout carrying pointer agreement and
interval disjointness. -/
structure TypedBTreePageLayout (usable : UsablePageSize) where
  generic : BTreeCellLayout usable.val
  cells : List (TypedBTreeCell usable generic.pagePrefix.header.header.pageType)
  placementsAgree : generic.cells = cells.map TypedBTreeCell.toPlacedCell
  deriving DecidableEq

def TypedBTreePageLayout.encodePage {usable : UsablePageSize}
    (layout : TypedBTreePageLayout usable) : Storage.Page usable.val :=
  layout.generic.encodePage

theorem TypedBTreePageLayout.cellCount_eq {usable : UsablePageSize}
    (layout : TypedBTreePageLayout usable) :
    layout.cells.length =
      layout.generic.pagePrefix.header.header.common.cellCount.val := by
  rw [← layout.generic.cellCount_eq]
  rw [layout.placementsAgree]
  simp

theorem TypedBTreePageLayout.all_cells_match {usable : UsablePageSize}
    (layout : TypedBTreePageLayout usable)
    (cell : TypedBTreeCell usable layout.generic.pagePrefix.header.header.pageType)
    (_member : cell ∈ layout.cells) :
    cell.body.pageType = layout.generic.pagePrefix.header.header.pageType :=
  cell.matchesPage

def PageNumber.WithinDatabase (pageCount : Nat) (number : PageNumber) : Prop :=
  number.value.val ≤ pageCount

instance (pageCount : Nat) (number : PageNumber) :
    Decidable (number.WithinDatabase pageCount) := by
  unfold PageNumber.WithinDatabase
  infer_instance

def BTreePageHeader.ReferencesWithin (pageCount : Nat) : BTreePageHeader → Prop
  | .interiorIndex _ rightmostPage | .interiorTable _ rightmostPage =>
    rightmostPage.val ≤ pageCount
  | .leafIndex _ | .leafTable _ => True

instance (pageCount : Nat) (header : BTreePageHeader) :
    Decidable (header.ReferencesWithin pageCount) := by
  cases header <;> simp [BTreePageHeader.ReferencesWithin] <;> infer_instance

def BTreePayloadData.ReferencesWithin (pageCount : Nat) : BTreePayloadData → Prop
  | .inline _ => True
  | .overflow _ firstOverflowPage => firstOverflowPage.WithinDatabase pageCount

instance (pageCount : Nat) (payload : BTreePayloadData) :
    Decidable (payload.ReferencesWithin pageCount) := by
  cases payload <;> simp [BTreePayloadData.ReferencesWithin] <;> infer_instance

def BTreeCellBody.ReferencesWithin {usable : UsablePageSize}
    (pageCount : Nat) : BTreeCellBody usable → Prop
  | .interiorTable cell =>
    cell.leftChildPage.WithinDatabase pageCount
  | .leafTable cell => cell.payload.data.ReferencesWithin pageCount
  | .interiorIndex cell =>
    cell.leftChildPage.WithinDatabase pageCount ∧
      cell.payload.data.ReferencesWithin pageCount
  | .leafIndex cell => cell.payload.data.ReferencesWithin pageCount

instance {usable : UsablePageSize} (pageCount : Nat) (body : BTreeCellBody usable) :
    Decidable (body.ReferencesWithin pageCount) := by
  cases body <;> simp [BTreeCellBody.ReferencesWithin] <;> infer_instance

def TypedBTreePageLayout.ReferencesWithin {usable : UsablePageSize}
    (layout : TypedBTreePageLayout usable) (pageCount : Nat) : Prop :=
  layout.generic.pagePrefix.header.header.ReferencesWithin pageCount ∧
    ∀ cell ∈ layout.cells, cell.body.ReferencesWithin pageCount

instance {usable : UsablePageSize} (layout : TypedBTreePageLayout usable)
    (pageCount : Nat) : Decidable (layout.ReferencesWithin pageCount) := by
  unfold TypedBTreePageLayout.ReferencesWithin
  infer_instance

theorem OverflowChainData.firstPage_mem_pageNumbers {usable : UsablePageSize}
    (chain : OverflowChainData usable) : chain.firstPage ∈ chain.pageNumbers := by
  cases chain <;> simp [OverflowChainData.firstPage, OverflowChainData.pageNumbers]

def OverflowChain.ReferencesWithin {usable : UsablePageSize}
    (chain : OverflowChain usable) (pageCount : Nat) : Prop :=
  ∀ number ∈ chain.data.pageNumbers, number.WithinDatabase pageCount

instance {usable : UsablePageSize} (chain : OverflowChain usable)
    (pageCount : Nat) : Decidable (chain.ReferencesWithin pageCount) := by
  unfold OverflowChain.ReferencesWithin
  infer_instance

structure BoundedOverflowChain (usable : UsablePageSize) (pageCount : Nat) where
  chain : OverflowChain usable
  referencesWithin : chain.ReferencesWithin pageCount
  deriving DecidableEq

def BoundedOverflowChain.firstPage {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount) : BoundedPageNumber pageCount := {
  number := chain.chain.firstPage
  withinDatabase := chain.referencesWithin _
    chain.chain.data.firstPage_mem_pageNumbers }

structure BoundedTypedBTreePageLayout (usable : UsablePageSize) (pageCount : Nat) where
  layout : TypedBTreePageLayout usable
  referencesWithin : layout.ReferencesWithin pageCount
  deriving DecidableEq

theorem BoundedTypedBTreePageLayout.header_references_within
    {usable : UsablePageSize} {pageCount : Nat}
    (layout : BoundedTypedBTreePageLayout usable pageCount) :
    layout.layout.generic.pagePrefix.header.header.ReferencesWithin pageCount :=
  layout.referencesWithin.1

theorem BoundedTypedBTreePageLayout.cell_references_within
    {usable : UsablePageSize} {pageCount : Nat}
    (layout : BoundedTypedBTreePageLayout usable pageCount)
    (cell : TypedBTreeCell usable
      layout.layout.generic.pagePrefix.header.header.pageType)
    (member : cell ∈ layout.layout.cells) :
    cell.body.ReferencesWithin pageCount :=
  layout.referencesWithin.2 cell member

def OverflowPage.toStoragePage {usable : UsablePageSize}
    (page : OverflowPage usable) : Storage.Page usable.val := {
  bytes := page.encode.toArray
  sizeInvariant := by simp [page.encode_length] }

theorem OverflowPage.toStoragePage_bytes {usable : UsablePageSize}
    (page : OverflowPage usable) : page.toStoragePage.bytes.toList = page.encode := by
  simp [OverflowPage.toStoragePage]

structure NumberedTypedBTreePage (usable : UsablePageSize) (pageCount : Nat) where
  pageNumber : BoundedPageNumber pageCount
  notFirstPage : pageNumber.number.value.val ≠ 1
  layout : BoundedTypedBTreePageLayout usable pageCount
  deriving DecidableEq

def NumberedTypedBTreePage.toPageWrite {usable : UsablePageSize} {pageCount : Nat}
    (page : NumberedTypedBTreePage usable pageCount) :
    Storage.PageWrite usable.val pageCount := {
  pageId := page.pageNumber.toPageId
  page := page.layout.layout.encodePage }

theorem NumberedTypedBTreePage.toPageWrite_pageId
    {usable : UsablePageSize} {pageCount : Nat}
    (page : NumberedTypedBTreePage usable pageCount) :
    page.toPageWrite.pageId = page.pageNumber.toPageId := rfl

theorem NumberedTypedBTreePage.write_read_same
    {usable : UsablePageSize} {pageCount : Nat}
    (disk : Storage.Disk usable.val pageCount)
    (page : NumberedTypedBTreePage usable pageCount) :
    (disk.write page.toPageWrite.pageId page.toPageWrite.page).read
      page.toPageWrite.pageId = page.toPageWrite.page := by
  exact Storage.Disk.read_write_same _ _ _

theorem BoundedOverflowChain.number_within_of_mem_toPages
    {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount)
    (numberedPage : PageNumber × OverflowPage usable)
    (member : numberedPage ∈ chain.chain.toPages) :
    numberedPage.1.WithinDatabase pageCount := by
  have mapped : numberedPage.1 ∈ chain.chain.toPages.map Prod.fst :=
    List.mem_map.mpr ⟨numberedPage, member, rfl⟩
  unfold OverflowChain.toPages at mapped
  rw [chain.chain.data.toPages_pageNumbers] at mapped
  exact chain.referencesWithin numberedPage.1 mapped

def BoundedOverflowChain.toPageWrites {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount) :
    List (Storage.PageWrite usable.val pageCount) :=
  chain.chain.toPages.attach.map fun attached =>
    let numberedPage := attached.val
    let boundedNumber : BoundedPageNumber pageCount := {
      number := numberedPage.1
      withinDatabase := by
        simpa [PageNumber.WithinDatabase] using
          chain.number_within_of_mem_toPages numberedPage attached.property }
    { pageId := boundedNumber.toPageId
      page := numberedPage.2.toStoragePage }

theorem BoundedOverflowChain.toPageWrites_length
    {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount) :
    chain.toPageWrites.length = chain.chain.data.pageCount := by
  simp [BoundedOverflowChain.toPageWrites,
    OverflowChain.toPages, chain.chain.data.toPages_length]

theorem BoundedOverflowChain.toPageWrites_nonempty
    {usable : UsablePageSize} {pageCount : Nat}
    (chain : BoundedOverflowChain usable pageCount) : chain.toPageWrites ≠ [] := by
  intro empty
  have countPositive := chain.chain.data.pageCount_pos
  have lengthEquality := chain.toPageWrites_length
  rw [empty] at lengthEquality
  simp at lengthEquality
  omega

def collectVerifiedPageWrites {usable : UsablePageSize} {pageCount : Nat}
    (btreePages : List (NumberedTypedBTreePage usable pageCount))
    (overflowChains : List (BoundedOverflowChain usable pageCount)) :
    List (Storage.PageWrite usable.val pageCount) :=
  btreePages.map NumberedTypedBTreePage.toPageWrite ++
    overflowChains.flatMap BoundedOverflowChain.toPageWrites

/-- A set of writes produced only from verified typed B-tree pages and verified
overflow chains. Distinct pager ids prevent later writes from silently
overwriting an earlier page in the same batch. -/
structure VerifiedPageSet (usable : UsablePageSize) (pageCount : Nat) where
  btreePages : List (NumberedTypedBTreePage usable pageCount)
  overflowChains : List (BoundedOverflowChain usable pageCount)
  pageIdsNodup :
    (collectVerifiedPageWrites btreePages overflowChains).map
      (fun write => write.pageId) |>.Nodup
  deriving DecidableEq

def VerifiedPageSet.writes {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedPageSet usable pageCount) :
    List (Storage.PageWrite usable.val pageCount) :=
  collectVerifiedPageWrites pages.btreePages pages.overflowChains

theorem VerifiedPageSet.write_page_ids_nodup
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedPageSet usable pageCount) :
    (pages.writes.map (fun write => write.pageId)).Nodup :=
  pages.pageIdsNodup

/-- The rollback-journal old-or-new theorem instantiated with writes emitted by
the verified physical page layer. -/
theorem VerifiedPageSet.rollbackCommit_crash_atomic
    {usable : UsablePageSize} {pageCount : Nat}
    (pages : VerifiedPageSet usable pageCount)
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

/-- Decode SQLite's special page-size field: the value one denotes 65536. -/
def HeaderPrefix.pageSize (header : HeaderPrefix) : Nat :=
  if header.pageSizeField.val = 1 then 65536 else header.pageSizeField.val

def ValidSQLitePageSize (pageSize : Nat) : Prop :=
  pageSize ∈ [512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]

instance (pageSize : Nat) : Decidable (ValidSQLitePageSize pageSize) := by
  unfold ValidSQLitePageSize
  infer_instance

/-- Semantic constraints needed to connect the 100-byte database header to a
fixed-size pager configuration. -/
def DatabaseHeader.WellFormedFor (usable : UsablePageSize) (pageCount : Nat)
    (header : DatabaseHeader) : Prop :=
  ValidSQLitePageSize header.headerPrefix.pageSize ∧
  header.headerPrefix.pageSize =
    usable.val + header.headerPrefix.reservedSpace.toNat ∧
  header.databaseSizePages.val = pageCount ∧
  0 < pageCount ∧
  (header.headerPrefix.writeVersion = 1 ∨ header.headerPrefix.writeVersion = 2) ∧
  (header.headerPrefix.readVersion = 1 ∨ header.headerPrefix.readVersion = 2) ∧
  1 ≤ header.schemaFormat.val ∧ header.schemaFormat.val ≤ 4 ∧
  1 ≤ header.textEncoding.val ∧ header.textEncoding.val ≤ 3 ∧
  header.headerPrefix.reservedSpace = 0

instance (usable : UsablePageSize) (pageCount : Nat) (header : DatabaseHeader) :
    Decidable (header.WellFormedFor usable pageCount) := by
  unfold DatabaseHeader.WellFormedFor
  infer_instance

structure ValidDatabaseHeader (usable : UsablePageSize) (pageCount : Nat) where
  header : DatabaseHeader
  wellFormed : header.WellFormedFor usable pageCount
  deriving DecidableEq

def decodeValidDatabaseHeader (usable : UsablePageSize) (pageCount : Nat)
    (input : List UInt8) :
    Option (ValidDatabaseHeader usable pageCount × List UInt8) := do
  let (header, suffix) ← decodeDatabaseHeader input
  if valid : header.WellFormedFor usable pageCount then
    some (⟨header, valid⟩, suffix)
  else
    none

theorem decodeValidDatabaseHeader_encode {usable : UsablePageSize}
    {pageCount : Nat} (header : ValidDatabaseHeader usable pageCount)
    (suffix : List UInt8) :
    decodeValidDatabaseHeader usable pageCount
      (encodeDatabaseHeader header.header ++ suffix) = some (header, suffix) := by
  unfold decodeValidDatabaseHeader
  rw [decodeDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos header.wellFormed]

structure DatabaseFirstPagePrefix (usable : UsablePageSize) (pageCount : Nat) where
  databaseHeader : ValidDatabaseHeader usable pageCount
  btreePrefix : BTreePagePrefix usable.val
  deriving DecidableEq

def DatabaseFirstPagePrefix.encode {usable : UsablePageSize} {pageCount : Nat}
    (pagePrefix : DatabaseFirstPagePrefix usable pageCount) : List UInt8 :=
  encodeDatabaseHeader pagePrefix.databaseHeader.header ++ pagePrefix.btreePrefix.encode

def decodeDatabaseFirstPagePrefix (usable : UsablePageSize) (pageCount : Nat)
    (input : List UInt8) :
    Option (DatabaseFirstPagePrefix usable pageCount × List UInt8) := do
  let (databaseHeader, afterHeader) ←
    decodeValidDatabaseHeader usable pageCount input
  let (btreePrefix, suffix) ← decodeBTreePagePrefix usable.val afterHeader
  some (⟨databaseHeader, btreePrefix⟩, suffix)

theorem decodeDatabaseFirstPagePrefix_encode {usable : UsablePageSize}
    {pageCount : Nat} (pagePrefix : DatabaseFirstPagePrefix usable pageCount)
    (suffix : List UInt8) :
    decodeDatabaseFirstPagePrefix usable pageCount (pagePrefix.encode ++ suffix) =
      some (pagePrefix, suffix) := by
  unfold DatabaseFirstPagePrefix.encode decodeDatabaseFirstPagePrefix
  rw [List.append_assoc, decodeValidDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeBTreePagePrefix_encode]

theorem DatabaseFirstPagePrefix.encode_length {usable : UsablePageSize}
    {pageCount : Nat} (pagePrefix : DatabaseFirstPagePrefix usable pageCount) :
    pagePrefix.encode.length = 100 + pagePrefix.btreePrefix.encode.length := by
  simp [DatabaseFirstPagePrefix.encode, encodeDatabaseHeader_length]

/-- SQLite page one: the database header occupies bytes 0–99 and the B-tree
page prefix begins at byte 100. -/
structure DatabaseFirstPage (usable : UsablePageSize) (pageCount : Nat) where
  databaseHeader : DatabaseHeader
  headerWellFormed : databaseHeader.WellFormedFor usable pageCount
  layout : BoundedTypedBTreePageLayout usable pageCount
  cellsAfterFirstPrefix : ∀ cell ∈ layout.layout.generic.cells,
    100 + layout.layout.generic.pagePrefix.encode.length ≤ cell.offset.val
  deriving DecidableEq

def DatabaseFirstPage.byteAt {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) (byteOffset : Nat) : UInt8 :=
  match (encodeDatabaseHeader page.databaseHeader)[byteOffset]? with
  | some byte => byte
  | none =>
    match page.layout.layout.generic.pagePrefix.encode[byteOffset - 100]? with
    | some byte => byte
    | none => (cellByteAt? page.layout.layout.generic.cells byteOffset).getD 0

def DatabaseFirstPage.encodePage {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) : Storage.Page usable.val := {
  bytes := Array.ofFn (fun offset : Fin usable.val => page.byteAt offset.val)
  sizeInvariant := by simp }

theorem DatabaseFirstPage.encodePage_size
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) :
    page.encodePage.bytes.size = usable.val :=
  page.encodePage.sizeInvariant

theorem DatabaseFirstPage.byteAt_header
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) (byteOffset : Nat)
    (withinHeader : byteOffset < 100) :
    page.byteAt byteOffset = (encodeDatabaseHeader page.databaseHeader).get
      ⟨byteOffset, by simpa [encodeDatabaseHeader_length] using withinHeader⟩ := by
  unfold DatabaseFirstPage.byteAt
  simp [getElem?_def, encodeDatabaseHeader_length, withinHeader]

theorem DatabaseFirstPage.encodePage_take_header
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) :
    page.encodePage.bytes.toList.take 100 =
      encodeDatabaseHeader page.databaseHeader := by
  apply List.ext_getElem
  · simp [encodeDatabaseHeader_length, page.encodePage.sizeInvariant]
    have := usable.atLeastMinimum
    omega
  · intro byteOffset leftBound rightBound
    have withinHeader : byteOffset < 100 := by
      simpa [encodeDatabaseHeader_length] using rightBound
    simpa [DatabaseFirstPage.encodePage] using
      page.byteAt_header byteOffset withinHeader

theorem DatabaseFirstPage.byteAt_btree_prefix
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) (prefixOffset : Nat)
    (withinPrefix : prefixOffset < page.layout.layout.generic.pagePrefix.encode.length) :
    page.byteAt (100 + prefixOffset) =
      page.layout.layout.generic.pagePrefix.encode.get ⟨prefixOffset, withinPrefix⟩ := by
  have afterHeader : ¬100 + prefixOffset < 100 := by omega
  have relativeOffset : 100 + prefixOffset - 100 = prefixOffset := by omega
  unfold DatabaseFirstPage.byteAt
  simp [getElem?_def, encodeDatabaseHeader_length, afterHeader,
    relativeOffset, withinPrefix]

def DatabaseFirstPage.toPageWrite
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) :
    Storage.PageWrite usable.val pageCount := {
  pageId := ⟨0, page.headerWellFormed.2.2.2.1⟩
  page := page.encodePage }

theorem DatabaseFirstPage.toPageWrite_pageId
    {usable : UsablePageSize} {pageCount : Nat}
    (page : DatabaseFirstPage usable pageCount) : page.toPageWrite.pageId.val = 0 :=
  rfl

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
