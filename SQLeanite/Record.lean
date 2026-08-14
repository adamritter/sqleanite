import SQLeanite.FileFormat

namespace SQLeanite
namespace FileFormat

/-- A byte payload whose length is part of its type. -/
structure SizedBytes (size : Nat) where
  bytes : List UInt8
  length_eq : bytes.length = size
  deriving DecidableEq

/-- Read exactly `size` bytes, retaining the unconsumed suffix. -/
def decodeSizedBytes : (size : Nat) → List UInt8 → Option (SizedBytes size × List UInt8)
  | 0, input => some (⟨[], rfl⟩, input)
  | size + 1, byte :: input => do
    let (tail, suffix) ← decodeSizedBytes size input
    some (⟨byte :: tail.bytes, by simp [tail.length_eq]⟩, suffix)
  | _ + 1, [] => none

theorem decodeSizedBytes_append {size : Nat} (payload : SizedBytes size)
    (suffix : List UInt8) :
    decodeSizedBytes size (payload.bytes ++ suffix) = some (payload, suffix) := by
  rcases payload with ⟨bytes, lengthEquality⟩
  induction bytes generalizing size with
  | nil =>
      simp only [List.length_nil] at lengthEquality
      subst size
      rfl
  | cons byte bytes induction =>
      cases size with
      | zero => simp at lengthEquality
      | succ size =>
          simp only [List.length_cons, Nat.succ.injEq] at lengthEquality
          simp only [List.cons_append, decodeSizedBytes]
          rw [induction (size := size) lengthEquality]
          rfl

theorem decodeSizedBytes_sound {size : Nat} {input suffix : List UInt8}
    {payload : SizedBytes size}
    (decoded : decodeSizedBytes size input = some (payload, suffix)) :
    input = payload.bytes ++ suffix := by
  induction size generalizing input suffix with
  | zero =>
      simp only [decodeSizedBytes] at decoded
      have pairEquality := Option.some.inj decoded
      injection pairEquality with payloadEquality suffixEquality
      subst payload
      subst suffix
      rfl
  | succ size induction =>
      cases input with
      | nil => simp [decodeSizedBytes] at decoded
      | cons byte input =>
          simp only [decodeSizedBytes] at decoded
          cases tailResult : decodeSizedBytes size input with
          | none => simp [tailResult] at decoded
          | some result =>
              rcases result with ⟨tail, remaining⟩
              rw [tailResult] at decoded
              simp only [Option.bind_eq_bind, Option.bind] at decoded
              have pairEquality := Option.some.inj decoded
              injection pairEquality with payloadEquality suffixEquality
              subst payload
              subst suffix
              rw [induction tailResult]
              rfl

theorem decodeSizedBytes_short {size : Nat} (input : List UInt8)
    (short : input.length < size) : decodeSizedBytes size input = none := by
  induction size generalizing input with
  | zero => omega
  | succ size induction =>
      cases input with
      | nil => rfl
      | cons byte input =>
          simp only [List.length_cons] at short
          simp only [decodeSizedBytes]
          rw [induction input (by omega)]
          rfl

def IntegerWidth.serialType : IntegerWidth → SerialType
  | .one => .integer8
  | .two => .integer16
  | .three => .integer24
  | .four => .integer32
  | .six => .integer48
  | .eight => .integer64

/-- One physical SQLite record field. Dynamic text/blob fields carry a sized
payload matching their proof-carrying serial-type metadata. Floats are stored
as raw IEEE-754 bits so this layer does not trust a numeric conversion. -/
inductive RecordField where
  | null
  | integer (width : IntegerWidth) (value : SignedInteger width)
  | floatBits (bits : U64Value)
  | constantZero
  | constantOne
  | blob (metadata : BlobSerialType)
      (payload : SizedBytes (serialTypePayloadSize (.blob metadata)))
  | text (metadata : TextSerialType)
      (payload : SizedBytes (serialTypePayloadSize (.text metadata)))
  deriving DecidableEq

def RecordField.serialType : RecordField → SerialType
  | .null => .null
  | .integer width _ => width.serialType
  | .floatBits _ => .float64
  | .constantZero => .constantZero
  | .constantOne => .constantOne
  | .blob metadata _ => .blob metadata
  | .text metadata _ => .text metadata

def RecordField.encodePayload : RecordField → List UInt8
  | .null | .constantZero | .constantOne => []
  | .integer _ value => encodeSignedInteger value
  | .floatBits bits => encodeUnsignedFixed 8 bits.val
  | .blob _ payload | .text _ payload => payload.bytes

def decodeRecordFieldPayload : SerialType → List UInt8 →
    Option (RecordField × List UInt8)
  | .null, input => some (.null, input)
  | .integer8, input => do
    let (value, suffix) ← decodeSignedInteger .one input
    some (.integer .one value, suffix)
  | .integer16, input => do
    let (value, suffix) ← decodeSignedInteger .two input
    some (.integer .two value, suffix)
  | .integer24, input => do
    let (value, suffix) ← decodeSignedInteger .three input
    some (.integer .three value, suffix)
  | .integer32, input => do
    let (value, suffix) ← decodeSignedInteger .four input
    some (.integer .four value, suffix)
  | .integer48, input => do
    let (value, suffix) ← decodeSignedInteger .six input
    some (.integer .six value, suffix)
  | .integer64, input => do
    let (value, suffix) ← decodeSignedInteger .eight input
    some (.integer .eight value, suffix)
  | .float64, input => do
    let (bits, suffix) ← decodeUnsignedFixed 8 input
    if bound : bits < 18446744073709551616 then
      some (.floatBits ⟨bits, bound⟩, suffix)
    else none
  | .constantZero, input => some (.constantZero, input)
  | .constantOne, input => some (.constantOne, input)
  | .blob metadata, input => do
    let (payload, suffix) ← decodeSizedBytes (serialTypePayloadSize (.blob metadata)) input
    some (.blob metadata payload, suffix)
  | .text metadata, input => do
    let (payload, suffix) ← decodeSizedBytes (serialTypePayloadSize (.text metadata)) input
    some (.text metadata payload, suffix)

theorem decodeRecordFieldPayload_encode (field : RecordField) (suffix : List UInt8) :
    decodeRecordFieldPayload field.serialType (field.encodePayload ++ suffix) =
      some (field, suffix) := by
  cases field with
  | null | constantZero | constantOne => rfl
  | integer width value =>
      cases width <;> simp only [RecordField.serialType, IntegerWidth.serialType,
        RecordField.encodePayload, decodeRecordFieldPayload, Option.bind_eq_bind,
        Option.bind, decodeSignedInteger_encode]
  | floatBits bits =>
      have bitsBound : bits.val < 256 ^ 8 := by
        change bits.val < 18446744073709551616
        exact bits.isLt
      simp only [RecordField.serialType, RecordField.encodePayload,
        decodeRecordFieldPayload]
      rw [decodeUnsignedFixed_encode suffix bitsBound]
      simp only [Option.bind_eq_bind, Option.bind, dif_pos bits.isLt]
  | blob metadata payload =>
      simp only [RecordField.serialType, RecordField.encodePayload,
        decodeRecordFieldPayload]
      rw [decodeSizedBytes_append]
      rfl
  | text metadata payload =>
      simp only [RecordField.serialType, RecordField.encodePayload,
        decodeRecordFieldPayload]
      rw [decodeSizedBytes_append]
      rfl

/-- Serial-type varints for a sequence of physical record fields. -/
def encodeRecordSerialTypes (fields : List RecordField) : List UInt8 :=
  fields.flatMap fun field => encodeVarint (encodeSerialType field.serialType)

theorem encodeRecordSerialTypes_length_le (fields : List RecordField) :
    (encodeRecordSerialTypes fields).length ≤ 9 * fields.length := by
  induction fields with
  | nil => exact Nat.le_refl 0
  | cons field fields induction =>
      change (encodeVarint (encodeSerialType field.serialType) ++
        encodeRecordSerialTypes fields).length ≤ 9 * (field :: fields).length
      rw [List.length_append, encodeVarint_length]
      simp only [List.length_cons]
      have fieldBound := sqliteVarintSize_le_nine
        (encodeSerialType field.serialType).val
      omega

/-- SQLite includes the size varint itself in the record-header size. Each
threshold is the largest serial-type byte count for which adding a `k`-byte
size varint still fits in the `k`-byte varint range. -/
def recordHeaderSize (serialTypeBytes : Nat) : Nat :=
  if serialTypeBytes ≤ 126 then serialTypeBytes + 1
  else if serialTypeBytes ≤ 16381 then serialTypeBytes + 2
  else if serialTypeBytes ≤ 2097148 then serialTypeBytes + 3
  else if serialTypeBytes ≤ 268435451 then serialTypeBytes + 4
  else if serialTypeBytes ≤ 34359738362 then serialTypeBytes + 5
  else if serialTypeBytes ≤ 4398046511097 then serialTypeBytes + 6
  else if serialTypeBytes ≤ 562949953421304 then serialTypeBytes + 7
  else if serialTypeBytes ≤ 72057594037927927 then serialTypeBytes + 8
  else serialTypeBytes + 9

theorem recordHeaderSize_le (serialTypeBytes : Nat) :
    recordHeaderSize serialTypeBytes ≤ serialTypeBytes + 9 := by
  unfold recordHeaderSize
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

private theorem varintSize_eq_one {value : Nat} (upper : value ≤ 127) :
    sqliteVarintSize value = 1 := by
  simp [sqliteVarintSize, upper]

private theorem varintSize_eq_two {value : Nat} (lower : 127 < value)
    (upper : value ≤ 16383) : sqliteVarintSize value = 2 := by
  simp [sqliteVarintSize, show ¬value ≤ 127 by omega, upper]

private theorem varintSize_eq_three {value : Nat} (lower : 16383 < value)
    (upper : value ≤ 2097151) : sqliteVarintSize value = 3 := by
  simp [sqliteVarintSize, show ¬value ≤ 127 by omega,
    show ¬value ≤ 16383 by omega, upper]

private theorem varintSize_eq_four {value : Nat} (lower : 2097151 < value)
    (upper : value ≤ 268435455) : sqliteVarintSize value = 4 := by
  simp [sqliteVarintSize, show ¬value ≤ 127 by omega,
    show ¬value ≤ 16383 by omega, show ¬value ≤ 2097151 by omega, upper]

private theorem varintSize_eq_five {value : Nat} (lower : 268435455 < value)
    (upper : value ≤ 34359738367) : sqliteVarintSize value = 5 := by
  simp [sqliteVarintSize, show ¬value ≤ 127 by omega,
    show ¬value ≤ 16383 by omega, show ¬value ≤ 2097151 by omega,
    show ¬value ≤ 268435455 by omega, upper]

private theorem varintSize_eq_six {value : Nat} (lower : 34359738367 < value)
    (upper : value ≤ 4398046511103) : sqliteVarintSize value = 6 := by
  simp [sqliteVarintSize, show ¬value ≤ 127 by omega,
    show ¬value ≤ 16383 by omega, show ¬value ≤ 2097151 by omega,
    show ¬value ≤ 268435455 by omega, show ¬value ≤ 34359738367 by omega, upper]

private theorem varintSize_eq_seven {value : Nat} (lower : 4398046511103 < value)
    (upper : value ≤ 562949953421311) : sqliteVarintSize value = 7 := by
  simp [sqliteVarintSize, show ¬value ≤ 127 by omega,
    show ¬value ≤ 16383 by omega, show ¬value ≤ 2097151 by omega,
    show ¬value ≤ 268435455 by omega, show ¬value ≤ 34359738367 by omega,
    show ¬value ≤ 4398046511103 by omega, upper]

private theorem varintSize_eq_eight {value : Nat} (lower : 562949953421311 < value)
    (upper : value ≤ 72057594037927935) : sqliteVarintSize value = 8 := by
  simp [sqliteVarintSize, show ¬value ≤ 127 by omega,
    show ¬value ≤ 16383 by omega, show ¬value ≤ 2097151 by omega,
    show ¬value ≤ 268435455 by omega, show ¬value ≤ 34359738367 by omega,
    show ¬value ≤ 4398046511103 by omega, show ¬value ≤ 562949953421311 by omega,
    upper]

private theorem varintSize_eq_nine {value : Nat} (lower : 72057594037927935 < value) :
    sqliteVarintSize value = 9 := by
  simp [sqliteVarintSize, show ¬value ≤ 127 by omega,
    show ¬value ≤ 16383 by omega, show ¬value ≤ 2097151 by omega,
    show ¬value ≤ 268435455 by omega, show ¬value ≤ 34359738367 by omega,
    show ¬value ≤ 4398046511103 by omega, show ¬value ≤ 562949953421311 by omega,
    show ¬value ≤ 72057594037927935 by omega]

theorem recordHeaderSize_fixed (serialTypeBytes : Nat) :
    serialTypeBytes + sqliteVarintSize (recordHeaderSize serialTypeBytes) =
      recordHeaderSize serialTypeBytes := by
  unfold recordHeaderSize
  split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals first
    | have sizeEquality := varintSize_eq_one (value := serialTypeBytes + 1) (by omega)
      omega
    | have sizeEquality := varintSize_eq_two (value := serialTypeBytes + 2)
          (by omega) (by omega)
      omega
    | have sizeEquality := varintSize_eq_three (value := serialTypeBytes + 3)
          (by omega) (by omega)
      omega
    | have sizeEquality := varintSize_eq_four (value := serialTypeBytes + 4)
          (by omega) (by omega)
      omega
    | have sizeEquality := varintSize_eq_five (value := serialTypeBytes + 5)
          (by omega) (by omega)
      omega
    | have sizeEquality := varintSize_eq_six (value := serialTypeBytes + 6)
          (by omega) (by omega)
      omega
    | have sizeEquality := varintSize_eq_seven (value := serialTypeBytes + 7)
          (by omega) (by omega)
      omega
    | have sizeEquality := varintSize_eq_eight (value := serialTypeBytes + 8)
          (by omega) (by omega)
      omega
    | have sizeEquality := varintSize_eq_nine (value := serialTypeBytes + 9) (by omega)
      omega

/-- A physical record whose computed header size fits in SQLite's unsigned
64-bit varint domain. -/
structure PhysicalRecord where
  fields : List RecordField
  headerSizeBound :
    recordHeaderSize (encodeRecordSerialTypes fields).length < 18446744073709551616
  deriving DecidableEq

def PhysicalRecord.headerSize (record : PhysicalRecord) : U64Value :=
  ⟨recordHeaderSize (encodeRecordSerialTypes record.fields).length,
    record.headerSizeBound⟩

def PhysicalRecord.encodeHeader (record : PhysicalRecord) : List UInt8 :=
  encodeVarint record.headerSize ++ encodeRecordSerialTypes record.fields

def PhysicalRecord.encodePayload (record : PhysicalRecord) : List UInt8 :=
  record.fields.flatMap RecordField.encodePayload

def PhysicalRecord.encode (record : PhysicalRecord) : List UInt8 :=
  record.encodeHeader ++ record.encodePayload

theorem PhysicalRecord.encodeHeader_length (record : PhysicalRecord) :
    record.encodeHeader.length = record.headerSize.val := by
  simp only [PhysicalRecord.encodeHeader, List.length_append, encodeVarint_length,
    PhysicalRecord.headerSize]
  have fixed := recordHeaderSize_fixed (encodeRecordSerialTypes record.fields).length
  omega

theorem PhysicalRecord.encode_length (record : PhysicalRecord) :
    record.encode.length = record.headerSize.val + record.encodePayload.length := by
  simp [PhysicalRecord.encode, PhysicalRecord.encodeHeader_length]

private def decodeRecordSerialTypesFuel : Nat → List UInt8 → Option (List SerialType)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, input => do
    let (code, suffix) ← decodeVarint input
    let serialType ← decodeSerialType code
    let serialTypes ← decodeRecordSerialTypesFuel fuel suffix
    some (serialType :: serialTypes)

def decodeRecordSerialTypes (input : List UInt8) : Option (List SerialType) :=
  decodeRecordSerialTypesFuel input.length input

private theorem encodeVarint_ne_nil (value : U64Value) : encodeVarint value ≠ [] := by
  intro empty
  have lengthEquality := encodeVarint_length value
  rw [empty] at lengthEquality
  simp only [List.length_nil] at lengthEquality
  have positive := sqliteVarintSize_positive value.val
  omega

private theorem decodeRecordSerialTypesFuel_succ (fuel : Nat) (input : List UInt8)
    (nonempty : input ≠ []) :
    decodeRecordSerialTypesFuel (fuel + 1) input = (do
      let (code, suffix) ← decodeVarint input
      let serialType ← decodeSerialType code
      let serialTypes ← decodeRecordSerialTypesFuel fuel suffix
      some (serialType :: serialTypes)) := by
  cases input with
  | nil => contradiction
  | cons byte input => rfl

private theorem encodeRecordSerialTypes_length_ge (fields : List RecordField) :
    fields.length ≤ (encodeRecordSerialTypes fields).length := by
  induction fields with
  | nil => exact Nat.le_refl 0
  | cons field fields induction =>
      change (field :: fields).length ≤
        (encodeVarint (encodeSerialType field.serialType) ++
          encodeRecordSerialTypes fields).length
      simp only [List.length_cons, List.length_append]
      have positive := sqliteVarintSize_positive (encodeSerialType field.serialType).val
      rw [encodeVarint_length]
      omega

private theorem decodeRecordSerialTypesFuel_encode (fields : List RecordField)
    (fuel : Nat) (enough : fields.length ≤ fuel) :
    decodeRecordSerialTypesFuel fuel (encodeRecordSerialTypes fields) =
      some (fields.map RecordField.serialType) := by
  induction fields generalizing fuel with
  | nil =>
      cases fuel <;> rfl
  | cons field fields induction =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simp only [encodeRecordSerialTypes, List.flatMap_cons, List.map_cons]
          rw [decodeRecordSerialTypesFuel_succ]
          rw [decodeVarint_encode]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [decodeSerialType_encode]
          simp only [Option.bind_eq_bind, Option.bind]
          change
            (decodeRecordSerialTypesFuel fuel (encodeRecordSerialTypes fields)).bind
                (fun serialTypes => some (field.serialType :: serialTypes)) =
              some (field.serialType :: fields.map RecordField.serialType)
          rw [induction fuel (by simpa using enough)]
          rfl
          exact List.append_ne_nil_of_left_ne_nil (encodeVarint_ne_nil _) _

theorem decodeRecordSerialTypes_encode (fields : List RecordField) :
    decodeRecordSerialTypes (encodeRecordSerialTypes fields) =
      some (fields.map RecordField.serialType) := by
  unfold decodeRecordSerialTypes
  exact decodeRecordSerialTypesFuel_encode fields _
    (encodeRecordSerialTypes_length_ge fields)

def encodeRecordPayloads (fields : List RecordField) : List UInt8 :=
  fields.flatMap RecordField.encodePayload

def decodeRecordPayloads : List SerialType → List UInt8 →
    Option (List RecordField × List UInt8)
  | [], input => some ([], input)
  | serialType :: serialTypes, input => do
    let (field, afterField) ← decodeRecordFieldPayload serialType input
    let (fields, suffix) ← decodeRecordPayloads serialTypes afterField
    some (field :: fields, suffix)

theorem decodeRecordPayloads_encode (fields : List RecordField) (suffix : List UInt8) :
    decodeRecordPayloads (fields.map RecordField.serialType)
        (encodeRecordPayloads fields ++ suffix) =
      some (fields, suffix) := by
  induction fields with
  | nil => rfl
  | cons field fields induction =>
      simp only [List.map_cons, encodeRecordPayloads, List.flatMap_cons,
        List.append_assoc, decodeRecordPayloads]
      rw [decodeRecordFieldPayload_encode]
      simp only [Option.bind_eq_bind, Option.bind]
      change
        (decodeRecordPayloads (fields.map RecordField.serialType)
            (encodeRecordPayloads fields ++ suffix)).bind
            (fun decoded => some (field :: decoded.1, decoded.2)) =
          some (field :: fields, suffix)
      rw [induction]
      rfl

theorem PhysicalRecord.ext {left right : PhysicalRecord}
    (fieldsEquality : left.fields = right.fields) : left = right := by
  cases left
  cases right
  cases fieldsEquality
  rfl

/-- Decode a complete physical record. Besides parsing, this validates that
the serial-type header is canonical and that its announced size is the unique
header-size fixed point for those serial bytes. -/
def decodePhysicalRecord (input : List UInt8) : Option (PhysicalRecord × List UInt8) := do
  let (headerSize, afterSize) ← decodeVarint input
  let encodedSizeWidth := (encodeVarint headerSize).length
  if widthFits : encodedSizeWidth ≤ headerSize.val then
    let remainingHeaderBytes := headerSize.val - encodedSizeWidth
    let (headerBytes, payloadInput) ← decodeSizedBytes remainingHeaderBytes afterSize
    let serialTypes ← decodeRecordSerialTypes headerBytes.bytes
    let (fields, suffix) ← decodeRecordPayloads serialTypes payloadInput
    if canonical : encodeRecordSerialTypes fields = headerBytes.bytes then
      if sizeMatches :
          recordHeaderSize (encodeRecordSerialTypes fields).length = headerSize.val then
        let record : PhysicalRecord := {
          fields
          headerSizeBound := by
            rw [sizeMatches]
            exact headerSize.isLt }
        some (record, suffix)
      else none
    else none
  else none

theorem decodePhysicalRecord_encode (record : PhysicalRecord) (suffix : List UInt8) :
    decodePhysicalRecord (record.encode ++ suffix) = some (record, suffix) := by
  let serialBytes := encodeRecordSerialTypes record.fields
  let payloadBytes := encodeRecordPayloads record.fields
  have encodedLayout :
      record.encode ++ suffix =
        encodeVarint record.headerSize ++ (serialBytes ++ (payloadBytes ++ suffix)) := by
    simp [PhysicalRecord.encode, PhysicalRecord.encodeHeader,
      PhysicalRecord.encodePayload, encodeRecordPayloads, serialBytes, payloadBytes,
      List.append_assoc]
  have fixed := recordHeaderSize_fixed serialBytes.length
  have sizeWidth :
      (encodeVarint record.headerSize).length = sqliteVarintSize record.headerSize.val :=
    encodeVarint_length _
  have widthFits : (encodeVarint record.headerSize).length ≤ record.headerSize.val := by
    change (encodeVarint record.headerSize).length ≤
      recordHeaderSize (encodeRecordSerialTypes record.fields).length
    rw [sizeWidth]
    change sqliteVarintSize (recordHeaderSize serialBytes.length) ≤
      recordHeaderSize serialBytes.length
    omega
  have remainingHeader :
      record.headerSize.val - (encodeVarint record.headerSize).length = serialBytes.length := by
    change recordHeaderSize serialBytes.length - (encodeVarint record.headerSize).length =
      serialBytes.length
    rw [sizeWidth]
    change recordHeaderSize serialBytes.length -
      sqliteVarintSize (recordHeaderSize serialBytes.length) = serialBytes.length
    omega
  rw [encodedLayout]
  unfold decodePhysicalRecord
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos widthFits]
  rw [remainingHeader]
  rw [decodeSizedBytes_append (⟨serialBytes, rfl⟩ : SizedBytes serialBytes.length)
    (payloadBytes ++ suffix)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show serialBytes = encodeRecordSerialTypes record.fields by rfl,
    decodeRecordSerialTypes_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show payloadBytes = encodeRecordPayloads record.fields by rfl,
    decodeRecordPayloads_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  have sizeMatches :
      recordHeaderSize (encodeRecordSerialTypes record.fields).length =
        record.headerSize.val := rfl
  simp only [dif_pos sizeMatches]
  apply congrArg some
  apply Prod.ext
  · exact PhysicalRecord.ext rfl
  · rfl

end FileFormat
end SQLeanite
