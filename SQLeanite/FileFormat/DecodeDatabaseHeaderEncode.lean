import SQLeanite.FileFormat.U16Value

namespace SQLeanite
namespace FileFormat

theorem decodeDatabaseHeader_encode (header : DatabaseHeader) (suffix : List UInt8) :
    decodeDatabaseHeader (encodeDatabaseHeader header ++ suffix) = some (header, suffix) := by
  have beforeLength : header.beforeReserved.length = 11 := by
    simp [DatabaseHeader.beforeReserved]
  have afterLength : header.afterReserved.length = 2 := by
    simp [DatabaseHeader.afterReserved]
  have encodedLayout :
      encodeDatabaseHeader header ++ suffix =
        encodeHeaderPrefix header.headerPrefix ++
          (encodeU32Values header.beforeReserved ++
            (List.replicate 20 0 ++
              (encodeU32Values header.afterReserved ++ suffix))) := by
    simp [encodeDatabaseHeader, List.append_assoc]
  have fieldsRoundtrip :
      decodeU32Values 11
          (encodeU32Values header.beforeReserved ++
            (List.replicate 20 0 ++
              (encodeU32Values header.afterReserved ++ suffix))) =
        some (header.beforeReserved,
          List.replicate 20 0 ++
            (encodeU32Values header.afterReserved ++ suffix)) := by
    rw [← beforeLength]
    exact decodeU32Values_encode _ _
  have versionsRoundtrip :
      decodeU32Values 2 (encodeU32Values header.afterReserved ++ suffix) =
        some (header.afterReserved, suffix) := by
    rw [← afterLength]
    exact decodeU32Values_encode _ _
  rw [encodedLayout]
  unfold decodeDatabaseHeader
  rw [decodeHeaderPrefix_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [fieldsRoundtrip]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [stripPrefix_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [versionsRoundtrip]
  simp only [Option.bind_eq_bind, Option.bind]
  simp [DatabaseHeader.beforeReserved, DatabaseHeader.afterReserved]

/-- Successful header decoding is lossless: the returned structure and suffix
reconstruct the exact input bytes.  This is the inverse direction needed to
transport a validated header across page-local writes without decoding the
whole post-image. -/
theorem decodeDatabaseHeader_sound {input suffix : List UInt8}
    {header : DatabaseHeader}
    (decoded : decodeDatabaseHeader input = some (header, suffix)) :
    input = encodeDatabaseHeader header ++ suffix := by
  unfold decodeDatabaseHeader at decoded
  rcases Option.bind_eq_some_iff.mp decoded with
    ⟨prefixAndRest, prefixResult, decoded⟩
  rcases prefixAndRest with ⟨headerPrefix, afterPrefix⟩
  rcases Option.bind_eq_some_iff.mp decoded with
    ⟨fieldsAndRest, fieldsResult, decoded⟩
  rcases fieldsAndRest with ⟨fields, afterFields⟩
  rcases Option.bind_eq_some_iff.mp decoded with
    ⟨afterReserved, reservedResult, decoded⟩
  rcases Option.bind_eq_some_iff.mp decoded with
    ⟨versionsAndSuffix, versionsResult, decoded⟩
  rcases versionsAndSuffix with ⟨versions, decodedSuffix⟩
  rcases fields with _ | ⟨databaseSizePages, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨firstFreelistTrunk, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨freelistPageCount, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨schemaCookie, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨schemaFormat, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨defaultPageCacheSize, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨largestRootBTreePage, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨textEncoding, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨userVersion, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨incrementalVacuum, fields⟩
  · simp at decoded
  rcases fields with _ | ⟨applicationId, fields⟩
  · simp at decoded
  cases fields with
  | cons extra fields => simp at decoded
  | nil =>
    rcases versions with _ | ⟨versionValidFor, versions⟩
    · simp at decoded
    rcases versions with _ | ⟨sqliteVersion, versions⟩
    · simp at decoded
    cases versions with
    | cons extra versions => simp at decoded
    | nil =>
      have pairEquality := Option.some.inj decoded
      injection pairEquality with headerEq suffixEq
      subst header
      subst suffix
      rw [decodeHeaderPrefix_sound prefixResult,
        decodeU32Values_sound fieldsResult,
        stripPrefix_sound reservedResult,
        decodeU32Values_sound versionsResult]
      simp [encodeDatabaseHeader, DatabaseHeader.beforeReserved,
        DatabaseHeader.afterReserved, List.append_assoc]

/-- SQLite varints represent exactly the unsigned 64-bit range. The ninth byte
uses all eight bits; each earlier byte contributes seven payload bits and uses
its high bit as the continuation marker. -/
abbrev U64Value := Fin 18446744073709551616

/-- Canonical byte length of an unsigned SQLite varint. -/
def sqliteVarintSize (value : Nat) : Nat :=
  if value ≤ 127 then 1
  else if value ≤ 16383 then 2
  else if value ≤ 2097151 then 3
  else if value ≤ 268435455 then 4
  else if value ≤ 34359738367 then 5
  else if value ≤ 4398046511103 then 6
  else if value ≤ 562949953421311 then 7
  else if value ≤ 72057594037927935 then 8
  else 9

theorem sqliteVarintSize_positive (value : Nat) : 0 < sqliteVarintSize value := by
  unfold sqliteVarintSize
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem sqliteVarintSize_le_nine (value : Nat) : sqliteVarintSize value ≤ 9 := by
  unfold sqliteVarintSize
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

private def varintDigit (value divisor : Nat) : Nat :=
  value / divisor % 128

private def varintContinuation (value divisor : Nat) : UInt8 :=
  UInt8.ofNat (128 + varintDigit value divisor)

private def varintTerminal7 (value : Nat) : UInt8 :=
  UInt8.ofNat (value % 128)

private def varintTerminal8 (value : Nat) : UInt8 :=
  UInt8.ofNat (value % 256)

private theorem varintDigit_lt (value divisor : Nat) : varintDigit value divisor < 128 := by
  exact Nat.mod_lt _ (by omega)

private theorem varintContinuation_toNat (value divisor : Nat) :
    (varintContinuation value divisor).toNat = 128 + varintDigit value divisor := by
  have bound := varintDigit_lt value divisor
  have sumBound : 128 + varintDigit value divisor < 256 := by omega
  simp only [varintContinuation, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt sumBound

private theorem varintTerminal7_toNat (value : Nat) :
    (varintTerminal7 value).toNat = value % 128 := by
  have bound : value % 128 < 128 := Nat.mod_lt _ (by omega)
  have byteBound : value % 128 < 256 := by omega
  simp only [varintTerminal7, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt byteBound

private theorem varintTerminal8_toNat (value : Nat) :
    (varintTerminal8 value).toNat = value % 256 := by
  simp [varintTerminal8, UInt8.toNat_ofNat']

private theorem varintContinuation_not_terminal (value divisor : Nat) :
    ¬(varintContinuation value divisor).toNat < 128 := by
  rw [varintContinuation_toNat]
  omega

private theorem varintTerminal7_is_terminal (value : Nat) :
    (varintTerminal7 value).toNat < 128 := by
  rw [varintTerminal7_toNat]
  exact Nat.mod_lt _ (by omega)

/-- Joining a higher base-128 block to its next digit grows the represented
modulus by one radix position. This lets the roundtrip proof normalize a
varint a digit at a time instead of invoking arithmetic automation on the
fully expanded nine-byte expression. -/
private theorem varintCombineDigits (value divisor block : Nat) :
    (value / (divisor * 128) % block) * 128 + value / divisor % 128 =
      value / divisor % (128 * block) := by
  rw [← Nat.div_div_eq_div_mul]
  rw [Nat.mod_mul]
  omega

/-- Encode one unsigned 64-bit value using SQLite's canonical varint layout. -/
def encodeVarint (value : U64Value) : List UInt8 :=
  let number := value.val
  if number ≤ 127 then
    [varintTerminal7 number]
  else if number ≤ 16383 then
    [varintContinuation number 128, varintTerminal7 number]
  else if number ≤ 2097151 then
    [varintContinuation number 16384, varintContinuation number 128,
      varintTerminal7 number]
  else if number ≤ 268435455 then
    [varintContinuation number 2097152, varintContinuation number 16384,
      varintContinuation number 128, varintTerminal7 number]
  else if number ≤ 34359738367 then
    [varintContinuation number 268435456, varintContinuation number 2097152,
      varintContinuation number 16384, varintContinuation number 128,
      varintTerminal7 number]
  else if number ≤ 4398046511103 then
    [varintContinuation number 34359738368, varintContinuation number 268435456,
      varintContinuation number 2097152, varintContinuation number 16384,
      varintContinuation number 128, varintTerminal7 number]
  else if number ≤ 562949953421311 then
    [varintContinuation number 4398046511104, varintContinuation number 34359738368,
      varintContinuation number 268435456, varintContinuation number 2097152,
      varintContinuation number 16384, varintContinuation number 128,
      varintTerminal7 number]
  else if number ≤ 72057594037927935 then
    [varintContinuation number 562949953421312,
      varintContinuation number 4398046511104,
      varintContinuation number 34359738368, varintContinuation number 268435456,
      varintContinuation number 2097152, varintContinuation number 16384,
      varintContinuation number 128, varintTerminal7 number]
  else
    [varintContinuation number 144115188075855872,
      varintContinuation number 1125899906842624,
      varintContinuation number 8796093022208,
      varintContinuation number 68719476736,
      varintContinuation number 536870912,
      varintContinuation number 4194304,
      varintContinuation number 32768,
      varintContinuation number 256,
      varintTerminal8 number]

private def decodeVarintNat : Nat → Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _, _ => none
  | 1, accumulated, byte :: suffix => some (accumulated * 256 + byte.toNat, suffix)
  | remaining + 2, accumulated, byte :: suffix =>
      if byte.toNat < 128 then some (accumulated * 128 + byte.toNat, suffix)
      else decodeVarintNat (remaining + 1)
        (accumulated * 128 + (byte.toNat - 128)) suffix
  | _, _, [] => none

/-- Decode one SQLite varint and retain the unconsumed input suffix. -/
def decodeVarint (bytes : List UInt8) : Option (U64Value × List UInt8) :=
  match decodeVarintNat 9 0 bytes with
  | none => none
  | some (value, suffix) =>
    if bound : value < 18446744073709551616 then some (⟨value, bound⟩, suffix)
    else none

theorem encodeVarint_length (value : U64Value) :
    (encodeVarint value).length = sqliteVarintSize value.val := by
  unfold encodeVarint sqliteVarintSize
  dsimp only
  split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals rfl

set_option maxHeartbeats 800000 in
theorem decodeVarint_encode (value : U64Value) (suffix : List UInt8) :
    decodeVarint (encodeVarint value ++ suffix) = some (value, suffix) := by
  unfold encodeVarint
  dsimp only
  split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals simp only [List.cons_append, List.nil_append, decodeVarint,
    decodeVarintNat, varintContinuation_not_terminal, varintTerminal7_is_terminal,
    ↓reduceIte]
  all_goals simp only [varintContinuation_toNat, varintTerminal7_toNat,
    varintTerminal8_toNat, varintDigit, Nat.zero_mul, Nat.zero_add,
    Nat.add_sub_cancel_left, varintCombineDigits]
  all_goals split
  all_goals try simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  all_goals try apply Fin.ext
  all_goals try simp only [Fin.val_mk]
  all_goals omega

/-- A blob serial type carries the raw on-disk code together with the format
conditions that make the code denote a blob. -/
structure BlobSerialType where
  code : U64Value
  atLeastTwelve : 12 ≤ code.val
  evenCode : code.val % 2 = 0
  deriving DecidableEq

/-- A text serial type carries the raw on-disk code together with the format
conditions that make the code denote text. -/
structure TextSerialType where
  code : U64Value
  atLeastThirteen : 13 ≤ code.val
  oddCode : code.val % 2 = 1
  deriving DecidableEq

/-- Semantic interpretation of SQLite record serial-type numbers. Codes 10
and 11 have no constructor because the file format reserves them. -/
inductive SerialType where
  | null
  | integer8
  | integer16
  | integer24
  | integer32
  | integer48
  | integer64
  | float64
  | constantZero
  | constantOne
  | blob (metadata : BlobSerialType)
  | text (metadata : TextSerialType)
  deriving DecidableEq

def encodeSerialType : SerialType → U64Value
  | .null => ⟨0, by omega⟩
  | .integer8 => ⟨1, by omega⟩
  | .integer16 => ⟨2, by omega⟩
  | .integer24 => ⟨3, by omega⟩
  | .integer32 => ⟨4, by omega⟩
  | .integer48 => ⟨5, by omega⟩
  | .integer64 => ⟨6, by omega⟩
  | .float64 => ⟨7, by omega⟩
  | .constantZero => ⟨8, by omega⟩
  | .constantOne => ⟨9, by omega⟩
  | .blob metadata => metadata.code
  | .text metadata => metadata.code

def decodeSerialType (code : U64Value) : Option SerialType :=
  if small : code.val < 12 then
    match code.val with
    | 0 => some .null
    | 1 => some .integer8
    | 2 => some .integer16
    | 3 => some .integer24
    | 4 => some .integer32
    | 5 => some .integer48
    | 6 => some .integer64
    | 7 => some .float64
    | 8 => some .constantZero
    | 9 => some .constantOne
    | _ => none
  else if even : code.val % 2 = 0 then
    some (.blob {
      code
      atLeastTwelve := by omega
      evenCode := even })
  else
    some (.text {
      code
      atLeastThirteen := by
        have remainderBound : code.val % 2 < 2 := Nat.mod_lt _ (by omega)
        omega
      oddCode := by
        have remainderBound : code.val % 2 < 2 := Nat.mod_lt _ (by omega)
        omega })

/-- Number of payload bytes selected by a legal serial type. -/
def serialTypePayloadSize : SerialType → Nat
  | .null | .constantZero | .constantOne => 0
  | .integer8 => 1
  | .integer16 => 2
  | .integer24 => 3
  | .integer32 => 4
  | .integer48 => 6
  | .integer64 | .float64 => 8
  | .blob metadata => (metadata.code.val - 12) / 2
  | .text metadata => (metadata.code.val - 13) / 2

/-- SQLite's canonical serial type for an integer value. Values outside the
signed 64-bit range still select the eight-byte class here; rejecting such a
logical value is a separate value-domain obligation. -/
def integerSerialType (value : Int) : SerialType :=
  if value = 0 then .constantZero
  else if value = 1 then .constantOne
  else if -128 ≤ value ∧ value ≤ 127 then .integer8
  else if -32768 ≤ value ∧ value ≤ 32767 then .integer16
  else if -8388608 ≤ value ∧ value ≤ 8388607 then .integer24
  else if -2147483648 ≤ value ∧ value ≤ 2147483647 then .integer32
  else if -140737488355328 ≤ value ∧ value ≤ 140737488355327 then .integer48
  else .integer64

theorem integerSerialType_payload_le_eight (value : Int) :
    serialTypePayloadSize (integerSerialType value) ≤ 8 := by
  unfold integerSerialType
  split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals simp [serialTypePayloadSize]

theorem decodeSerialType_encode (serialType : SerialType) :
    decodeSerialType (encodeSerialType serialType) = some serialType := by
  cases serialType with
  | null | integer8 | integer16 | integer24 | integer32 | integer48 |
      integer64 | float64 | constantZero | constantOne =>
      rfl
  | blob metadata =>
      have notSmall : ¬metadata.code.val < 12 := Nat.not_lt_of_ge metadata.atLeastTwelve
      simp [encodeSerialType, decodeSerialType, notSmall, metadata.evenCode]
  | text metadata =>
      have notSmall : ¬metadata.code.val < 12 :=
        Nat.not_lt_of_ge (Nat.le_trans (by omega) metadata.atLeastThirteen)
      have notEven : metadata.code.val % 2 ≠ 0 := by
        rw [metadata.oddCode]
        omega
      simp [encodeSerialType, decodeSerialType, notSmall, notEven]

theorem decodeSerialType_encode_payload (serialType : SerialType) :
    (decodeSerialType (encodeSerialType serialType)).map serialTypePayloadSize =
      some (serialTypePayloadSize serialType) := by
  rw [decodeSerialType_encode]
  rfl

/-- Fixed-width big-endian representation used by SQLite integer payloads and
many page fields. High zero bytes are retained so the output has exactly the
requested width. -/
def encodeUnsignedFixed : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value =>
    encodeUnsignedFixed width (value / 256) ++ [UInt8.ofNat (value % 256)]

/-- Decode exactly `width` big-endian bytes, retaining all following bytes. -/
def decodeUnsignedFixed : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, input => some (0, input)
  | width + 1, input => do
    let (decodedPrefix, afterPrefix) ← decodeUnsignedFixed width input
    match afterPrefix with
    | byte :: suffix => some (decodedPrefix * 256 + byte.toNat, suffix)
    | [] => none

theorem unsignedFixedByte_toNat (value : Nat) :
    (UInt8.ofNat (value % 256)).toNat = value % 256 := by
  simp [UInt8.toNat_ofNat']

theorem encodeUnsignedFixed_length (width value : Nat) :
    (encodeUnsignedFixed width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width induction =>
      simp [encodeUnsignedFixed, induction]

theorem encodeU16Bytes_eq_encodeUnsignedFixed (value : U16Value) :
    encodeU16Bytes value = encodeUnsignedFixed 2 value.val := by
  have quotientBound : value.val / 256 < 256 := by omega
  simp [encodeU16Bytes, encodeU16, encodeUnsignedFixed,
    Nat.mod_eq_of_lt quotientBound]

end FileFormat

end SQLeanite
