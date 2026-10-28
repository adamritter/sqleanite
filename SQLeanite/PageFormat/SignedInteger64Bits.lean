import SQLeanite.PageFormat.PageNumber
import SQLeanite.Record

namespace SQLeanite
namespace FileFormat

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

end FileFormat

end SQLeanite
