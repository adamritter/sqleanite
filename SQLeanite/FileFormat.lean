import Std

namespace SQLeanite
namespace FileFormat

/-- Values stored in SQLite's two-byte big-endian header fields. -/
abbrev U16Value := Fin 65536

def encodeU16 (value : U16Value) : UInt8 × UInt8 :=
  (UInt8.ofNat (value.val / 256), UInt8.ofNat (value.val % 256))

def decodeU16 (high low : UInt8) : Nat :=
  high.toNat * 256 + low.toNat

theorem decodeU16_lt (high low : UInt8) : decodeU16 high low < 65536 := by
  have highBound : high.toNat < 256 := high.toBitVec.isLt
  have lowBound : low.toNat < 256 := low.toBitVec.isLt
  unfold decodeU16
  omega

theorem decodeU16_encode (value : U16Value) :
    decodeU16 (encodeU16 value).1 (encodeU16 value).2 = value.val := by
  have quotientBound : value.val / 256 < 256 := by omega
  have remainderBound : value.val % 256 < 256 := Nat.mod_lt _ (by omega)
  simp only [encodeU16, decodeU16, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt quotientBound, Nat.mod_eq_of_lt remainderBound]
  omega

theorem encodeU16_decode (high low : UInt8) :
    encodeU16 ⟨decodeU16 high low, decodeU16_lt high low⟩ = (high, low) := by
  apply Prod.ext
  · apply UInt8.toNat.inj
    simp only [encodeU16, decodeU16, UInt8.toNat_ofNat']
    have highBound : high.toNat < 256 := high.toBitVec.isLt
    have lowBound : low.toNat < 256 := low.toBitVec.isLt
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · apply UInt8.toNat.inj
    simp only [encodeU16, decodeU16, UInt8.toNat_ofNat']
    have highBound : high.toNat < 256 := high.toBitVec.isLt
    have lowBound : low.toNat < 256 := low.toBitVec.isLt
    omega

def encodeU16Bytes (value : U16Value) : List UInt8 :=
  [encodeU16 value |>.1, encodeU16 value |>.2]

/-- Parse one big-endian 16-bit field, retaining all following bytes. -/
def decodeU16Bytes : List UInt8 → Option (U16Value × List UInt8)
  | high :: low :: suffix =>
    some (⟨decodeU16 high low, decodeU16_lt high low⟩, suffix)
  | _ => none

theorem decodeU16Bytes_encode (value : U16Value) (suffix : List UInt8) :
    decodeU16Bytes (encodeU16Bytes value ++ suffix) = some (value, suffix) := by
  have valueRoundtrip := decodeU16_encode value
  have decodedValue :
      (⟨decodeU16 (encodeU16 value).1 (encodeU16 value).2,
        decodeU16_lt (encodeU16 value).1 (encodeU16 value).2⟩ : U16Value) = value :=
    Fin.ext valueRoundtrip
  simp [encodeU16Bytes, decodeU16Bytes, decodedValue]

theorem decodeU16Bytes_sound {input suffix : List UInt8} {value : U16Value}
    (decoded : decodeU16Bytes input = some (value, suffix)) :
    input = encodeU16Bytes value ++ suffix := by
  cases input with
  | nil => simp [decodeU16Bytes] at decoded
  | cons high rest =>
      cases rest with
      | nil => simp [decodeU16Bytes] at decoded
      | cons low inputSuffix =>
          simp only [decodeU16Bytes] at decoded
          have pairEquality := Option.some.inj decoded
          injection pairEquality with valueEquality suffixEquality
          subst value
          subst suffix
          simp [encodeU16Bytes, encodeU16_decode]

theorem decodeU16Bytes_short (bytes : List UInt8) (short : bytes.length < 2) :
    decodeU16Bytes bytes = none := by
  cases bytes with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second suffix =>
          simp only [List.length_cons] at short
          omega

/-- Values stored in SQLite's four-byte big-endian header fields. -/
abbrev U32Value := Fin 4294967296

structure U32Bytes where
  first : UInt8
  second : UInt8
  third : UInt8
  fourth : UInt8
  deriving Repr, DecidableEq

def encodeU32 (value : U32Value) : U32Bytes :=
  { first := UInt8.ofNat (value.val / 16777216)
    second := UInt8.ofNat ((value.val / 65536) % 256)
    third := UInt8.ofNat ((value.val / 256) % 256)
    fourth := UInt8.ofNat (value.val % 256) }

def decodeU32 (bytes : U32Bytes) : Nat :=
  bytes.first.toNat * 16777216 + bytes.second.toNat * 65536 +
    bytes.third.toNat * 256 + bytes.fourth.toNat

theorem decodeU32_lt (bytes : U32Bytes) : decodeU32 bytes < 4294967296 := by
  have firstBound : bytes.first.toNat < 256 := bytes.first.toBitVec.isLt
  have secondBound : bytes.second.toNat < 256 := bytes.second.toBitVec.isLt
  have thirdBound : bytes.third.toNat < 256 := bytes.third.toBitVec.isLt
  have fourthBound : bytes.fourth.toNat < 256 := bytes.fourth.toBitVec.isLt
  unfold decodeU32
  omega

theorem decodeU32_encode (value : U32Value) : decodeU32 (encodeU32 value) = value.val := by
  have firstBound : value.val / 16777216 < 256 := by omega
  have secondBound : (value.val / 65536) % 256 < 256 := Nat.mod_lt _ (by omega)
  have thirdBound : (value.val / 256) % 256 < 256 := Nat.mod_lt _ (by omega)
  have fourthBound : value.val % 256 < 256 := Nat.mod_lt _ (by omega)
  simp only [encodeU32, decodeU32, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt firstBound, Nat.mod_eq_of_lt secondBound,
    Nat.mod_eq_of_lt thirdBound, Nat.mod_eq_of_lt fourthBound]
  omega

def encodeU32Bytes (value : U32Value) : List UInt8 :=
  let bytes := encodeU32 value
  [bytes.first, bytes.second, bytes.third, bytes.fourth]

def decodeU32Bytes : List UInt8 → Option (U32Value × List UInt8)
  | first :: second :: third :: fourth :: suffix =>
    let bytes : U32Bytes := { first, second, third, fourth }
    some (⟨decodeU32 bytes, decodeU32_lt bytes⟩, suffix)
  | _ => none

theorem decodeU32Bytes_encode (value : U32Value) (suffix : List UInt8) :
    decodeU32Bytes (encodeU32Bytes value ++ suffix) = some (value, suffix) := by
  have valueRoundtrip := decodeU32_encode value
  have decodedValue :
      (⟨decodeU32 (encodeU32 value), decodeU32_lt (encodeU32 value)⟩ : U32Value) = value :=
    Fin.ext valueRoundtrip
  simp [encodeU32Bytes, decodeU32Bytes, decodedValue]

theorem decodeU32Bytes_short (bytes : List UInt8) (short : bytes.length < 4) :
    decodeU32Bytes bytes = none := by
  cases bytes with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              cases rest with
              | nil => rfl
              | cons fourth suffix =>
                  simp only [List.length_cons] at short
                  omega

/-- The required first 16 bytes of every SQLite 3 database file. -/
def sqliteHeaderMagic : List UInt8 :=
  [83, 81, 76, 105, 116, 101, 32, 102, 111, 114, 109, 97, 116, 32, 51, 0]

private def stripPrefix? (expected input : List UInt8) : Option (List UInt8) :=
  if input.take expected.length == expected then some (input.drop expected.length) else none

private theorem stripPrefix_append (expected suffix : List UInt8) :
    stripPrefix? expected (expected ++ suffix) = some suffix := by
  simp [stripPrefix?]

/-- Bytes 0 through 27 of an SQLite database header. The three payload
fraction bytes are fixed by the format and therefore are validated rather than
stored in the decoded structure. -/
structure HeaderPrefix where
  pageSizeField : U16Value
  writeVersion : UInt8
  readVersion : UInt8
  reservedSpace : UInt8
  changeCounter : U32Value
  deriving Repr, DecidableEq

def encodeHeaderPrefix (header : HeaderPrefix) : List UInt8 :=
  sqliteHeaderMagic ++ encodeU16Bytes header.pageSizeField ++
    [header.writeVersion, header.readVersion, header.reservedSpace, 64, 32, 32] ++
    encodeU32Bytes header.changeCounter

def decodeHeaderPrefix (bytes : List UInt8) : Option (HeaderPrefix × List UInt8) := do
  let afterMagic ← stripPrefix? sqliteHeaderMagic bytes
  let (pageSizeField, afterPageSize) ← decodeU16Bytes afterMagic
  match afterPageSize with
  | writeVersion :: readVersion :: reservedSpace :: 64 :: 32 :: 32 :: afterFractions =>
    let (changeCounter, suffix) ← decodeU32Bytes afterFractions
    pure ({ pageSizeField, writeVersion, readVersion, reservedSpace, changeCounter }, suffix)
  | _ => none

theorem encodeHeaderPrefix_length (header : HeaderPrefix) :
    (encodeHeaderPrefix header).length = 28 := by
  simp [encodeHeaderPrefix, sqliteHeaderMagic, encodeU16Bytes, encodeU32Bytes]

theorem decodeHeaderPrefix_encode (header : HeaderPrefix) (suffix : List UInt8) :
    decodeHeaderPrefix (encodeHeaderPrefix header ++ suffix) = some (header, suffix) := by
  simp [encodeHeaderPrefix, decodeHeaderPrefix, List.append_assoc,
    stripPrefix_append, decodeU16Bytes_encode, decodeU32Bytes_encode]

def encodeU32Values (values : List U32Value) : List UInt8 :=
  values.flatMap encodeU32Bytes

def decodeU32Values : Nat → List UInt8 → Option (List U32Value × List UInt8)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
    let (value, suffix) ← decodeU32Bytes bytes
    let (values, rest) ← decodeU32Values count suffix
    pure (value :: values, rest)

theorem decodeU32Values_encode (values : List U32Value) (suffix : List UInt8) :
    decodeU32Values values.length (encodeU32Values values ++ suffix) =
      some (values, suffix) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [encodeU32Values, List.flatMap_cons, List.length_cons, List.append_assoc,
        decodeU32Values]
      rw [decodeU32Bytes_encode]
      change
        (decodeU32Values values.length (encodeU32Values values ++ suffix)).bind
            (fun decoded => some (value :: decoded.1, decoded.2)) =
          some (value :: values, suffix)
      rw [induction]
      rfl

/-- The complete 100-byte SQLite database header. Signed interpretation of the
default-cache field is deferred; the file codec preserves its raw bits. -/
structure DatabaseHeader where
  headerPrefix : HeaderPrefix
  databaseSizePages : U32Value
  firstFreelistTrunk : U32Value
  freelistPageCount : U32Value
  schemaCookie : U32Value
  schemaFormat : U32Value
  defaultPageCacheSize : U32Value
  largestRootBTreePage : U32Value
  textEncoding : U32Value
  userVersion : U32Value
  incrementalVacuum : U32Value
  applicationId : U32Value
  versionValidFor : U32Value
  sqliteVersion : U32Value
  deriving Repr, DecidableEq

private def DatabaseHeader.beforeReserved (header : DatabaseHeader) : List U32Value :=
  [header.databaseSizePages, header.firstFreelistTrunk, header.freelistPageCount,
    header.schemaCookie, header.schemaFormat, header.defaultPageCacheSize,
    header.largestRootBTreePage, header.textEncoding, header.userVersion,
    header.incrementalVacuum, header.applicationId]

private def DatabaseHeader.afterReserved (header : DatabaseHeader) : List U32Value :=
  [header.versionValidFor, header.sqliteVersion]

def encodeDatabaseHeader (header : DatabaseHeader) : List UInt8 :=
  encodeHeaderPrefix header.headerPrefix ++ encodeU32Values header.beforeReserved ++
    List.replicate 20 0 ++ encodeU32Values header.afterReserved

def decodeDatabaseHeader (bytes : List UInt8) : Option (DatabaseHeader × List UInt8) := do
  let (headerPrefix, afterPrefix) ← decodeHeaderPrefix bytes
  let (fields, afterFields) ← decodeU32Values 11 afterPrefix
  let afterReserved ← stripPrefix? (List.replicate 20 0) afterFields
  let (versions, suffix) ← decodeU32Values 2 afterReserved
  match fields, versions with
  | [databaseSizePages, firstFreelistTrunk, freelistPageCount, schemaCookie,
      schemaFormat, defaultPageCacheSize, largestRootBTreePage, textEncoding,
      userVersion, incrementalVacuum, applicationId],
      [versionValidFor, sqliteVersion] =>
    let header : DatabaseHeader := {
      headerPrefix := headerPrefix
      databaseSizePages := databaseSizePages
      firstFreelistTrunk := firstFreelistTrunk
      freelistPageCount := freelistPageCount
      schemaCookie := schemaCookie
      schemaFormat := schemaFormat
      defaultPageCacheSize := defaultPageCacheSize
      largestRootBTreePage := largestRootBTreePage
      textEncoding := textEncoding
      userVersion := userVersion
      incrementalVacuum := incrementalVacuum
      applicationId := applicationId
      versionValidFor := versionValidFor
      sqliteVersion := sqliteVersion
    }
    pure (header, suffix)
  | _, _ => none

theorem encodeDatabaseHeader_length (header : DatabaseHeader) :
    (encodeDatabaseHeader header).length = 100 := by
  simp [encodeDatabaseHeader, DatabaseHeader.beforeReserved,
    DatabaseHeader.afterReserved, encodeHeaderPrefix_length, encodeU32Values,
    encodeU32Bytes]

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

private theorem unsignedFixedByte_toNat (value : Nat) :
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

theorem decodeUnsignedFixed_encode {width value : Nat} (suffix : List UInt8)
    (bound : value < 256 ^ width) :
    decodeUnsignedFixed width (encodeUnsignedFixed width value ++ suffix) =
      some (value, suffix) := by
  induction width generalizing value suffix with
  | zero =>
      simp only [Nat.pow_zero] at bound
      have valueZero : value = 0 := by omega
      subst value
      rfl
  | succ width induction =>
      have quotientBound : value / 256 < 256 ^ width := by
        rw [Nat.pow_succ] at bound
        omega
      simp only [encodeUnsignedFixed, List.append_assoc, List.cons_append,
        List.nil_append, decodeUnsignedFixed]
      rw [induction (suffix := UInt8.ofNat (value % 256) :: suffix) quotientBound]
      simp only [Option.bind_eq_bind, Option.bind, unsignedFixedByte_toNat]
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      simpa [Nat.mul_comm] using Nat.div_add_mod value 256

theorem decodeUnsignedFixed_consumes {width : Nat} {input suffix : List UInt8}
    {value : Nat} (decoded : decodeUnsignedFixed width input = some (value, suffix)) :
    input.length = width + suffix.length := by
  induction width generalizing input value suffix with
  | zero =>
      simp only [decodeUnsignedFixed] at decoded
      have pairEquality : (0, input) = (value, suffix) := Option.some.inj decoded
      injection pairEquality with valueEquality suffixEquality
      subst value
      subst input
      simp
  | succ width induction =>
      simp only [decodeUnsignedFixed] at decoded
      cases prefixResult : decodeUnsignedFixed width input with
      | none =>
          rw [prefixResult] at decoded
          simp at decoded
      | some result =>
          rcases result with ⟨decodedPrefix, afterPrefix⟩
          rw [prefixResult] at decoded
          simp only [Option.bind_eq_bind, Option.bind] at decoded
          cases afterPrefix with
          | nil => simp at decoded
          | cons byte rest =>
              have pairEquality : (decodedPrefix * 256 + byte.toNat, rest) =
                  (value, suffix) := Option.some.inj decoded
              injection pairEquality with valueEquality suffixEquality
              subst value
              subst suffix
              have prefixConsumed := induction prefixResult
              simp only [List.length_cons] at prefixConsumed
              omega

theorem decodeUnsignedFixed_short {width : Nat} (input : List UInt8)
    (short : input.length < width) :
    decodeUnsignedFixed width input = none := by
  cases decoded : decodeUnsignedFixed width input with
  | none => rfl
  | some result =>
      rcases result with ⟨value, suffix⟩
      have consumed := decodeUnsignedFixed_consumes decoded
      omega

/-- The only signed integer widths used by SQLite record serial types. -/
inductive IntegerWidth where
  | one | two | three | four | six | eight
  deriving Repr, DecidableEq

namespace IntegerWidth

def bytes : IntegerWidth → Nat
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .six => 6
  | .eight => 8

def modulus : IntegerWidth → Nat
  | .one => 256
  | .two => 65536
  | .three => 16777216
  | .four => 4294967296
  | .six => 281474976710656
  | .eight => 18446744073709551616

def midpoint : IntegerWidth → Nat
  | .one => 128
  | .two => 32768
  | .three => 8388608
  | .four => 2147483648
  | .six => 140737488355328
  | .eight => 9223372036854775808

theorem modulus_eq_pow (width : IntegerWidth) :
    width.modulus = 256 ^ width.bytes := by
  cases width <;> decide

theorem modulus_eq_twice_midpoint (width : IntegerWidth) :
    width.modulus = 2 * width.midpoint := by
  cases width <;> decide

theorem modulus_positive (width : IntegerWidth) : 0 < width.modulus := by
  cases width <;> decide

theorem midpoint_positive (width : IntegerWidth) : 0 < width.midpoint := by
  cases width <;> decide

end IntegerWidth

/-- A signed integer known to fit exactly in one SQLite integer width. -/
structure SignedInteger (width : IntegerWidth) where
  value : Int
  lowerBound : -(Int.ofNat width.midpoint) ≤ value
  upperBound : value < Int.ofNat width.midpoint
  deriving DecidableEq

theorem SignedInteger.ext {width : IntegerWidth} {left right : SignedInteger width}
    (valueEquality : left.value = right.value) : left = right := by
  cases left
  cases right
  cases valueEquality
  rfl

def SignedInteger.toUnsigned {width : IntegerWidth}
    (value : SignedInteger width) : Nat :=
  if value.value < 0 then
    (value.value + Int.ofNat width.modulus).toNat
  else value.value.toNat

theorem SignedInteger.toUnsigned_lt {width : IntegerWidth}
    (value : SignedInteger width) : value.toUnsigned < width.modulus := by
  have lowerBound := value.lowerBound
  have upperBound := value.upperBound
  simp only [Int.ofNat_eq_coe] at lowerBound upperBound
  unfold SignedInteger.toUnsigned
  simp only [Int.ofNat_eq_coe]
  split <;> rename_i sign
  · rw [Int.toNat_lt' width.modulus_positive]
    omega
  · rw [Int.toNat_lt' width.modulus_positive]
    have modulusIdentity := width.modulus_eq_twice_midpoint
    omega

def signedIntFromUnsigned (width : IntegerWidth) (value : Fin width.modulus) : Int :=
  if value.val < width.midpoint then Int.ofNat value.val
  else Int.ofNat value.val - Int.ofNat width.modulus

def signedIntegerFromUnsigned (width : IntegerWidth)
    (unsigned : Fin width.modulus) : SignedInteger width :=
  if below : unsigned.val < width.midpoint then {
    value := Int.ofNat unsigned.val
    lowerBound := by
      simp only [Int.ofNat_eq_coe]
      omega
    upperBound := by
      simp only [Int.ofNat_eq_coe]
      omega
  } else {
    value := Int.ofNat unsigned.val - Int.ofNat width.modulus
    lowerBound := by
      have modulusIdentity := width.modulus_eq_twice_midpoint
      simp only [Int.ofNat_eq_coe]
      omega
    upperBound := by
      have unsignedBound := unsigned.isLt
      have midpointPositive := width.midpoint_positive
      simp only [Int.ofNat_eq_coe]
      omega
  }

theorem signedIntegerFromUnsigned_value (width : IntegerWidth)
    (unsigned : Fin width.modulus) :
    (signedIntegerFromUnsigned width unsigned).value =
      signedIntFromUnsigned width unsigned := by
  unfold signedIntegerFromUnsigned signedIntFromUnsigned
  split <;> rfl

theorem signedIntegerFromUnsigned_toUnsigned {width : IntegerWidth}
    (value : SignedInteger width) :
    signedIntegerFromUnsigned width ⟨value.toUnsigned, value.toUnsigned_lt⟩ = value := by
  apply SignedInteger.ext
  rw [signedIntegerFromUnsigned_value]
  unfold signedIntFromUnsigned SignedInteger.toUnsigned
  simp only [Int.ofNat_eq_coe]
  have lowerBound := value.lowerBound
  have upperBound := value.upperBound
  simp only [Int.ofNat_eq_coe] at lowerBound upperBound
  split <;> rename_i sign
  · have modulusIdentity := width.modulus_eq_twice_midpoint
    have sumNonnegative : 0 ≤ value.value + (width.modulus : Int) := by omega
    have unsignedNotBelow :
        ¬(value.value + (width.modulus : Int)).toNat < width.midpoint := by
      rw [Int.toNat_lt' width.midpoint_positive]
      omega
    simp only [unsignedNotBelow, ↓reduceIte]
    have recovered := Int.toNat_of_nonneg sumNonnegative
    omega
  · have valueNonnegative : 0 ≤ value.value := by omega
    have unsignedBelow : value.value.toNat < width.midpoint := by
      rw [Int.toNat_lt' width.midpoint_positive]
      exact upperBound
    simp only [unsignedBelow, ↓reduceIte]
    exact Int.toNat_of_nonneg valueNonnegative

/-- Encoding after signed interpretation recovers the original fixed-width
bit pattern.  This is the converse direction needed by page-routing codecs. -/
theorem SignedInteger.toUnsigned_fromUnsigned (width : IntegerWidth)
    (unsigned : Fin width.modulus) :
    (signedIntegerFromUnsigned width unsigned).toUnsigned = unsigned.val := by
  unfold SignedInteger.toUnsigned
  rw [signedIntegerFromUnsigned_value]
  unfold signedIntFromUnsigned
  split <;> rename_i below
  · rw [if_neg (by simp only [Int.ofNat_eq_coe]; omega)]
    simp
  · have unsignedBound := unsigned.isLt
    have modulusPositive := width.modulus_positive
    rw [if_pos (by simp only [Int.ofNat_eq_coe]; omega)]
    simp only [Int.ofNat_eq_coe]
    have sumIdentity :
        (unsigned.val : Int) - (width.modulus : Int) +
          (width.modulus : Int) = unsigned.val := by omega
    rw [sumIdentity]
    simp

/-- Encode a bounded signed SQLite integer as fixed-width two's-complement
big-endian bytes. -/
def encodeSignedInteger {width : IntegerWidth}
    (value : SignedInteger width) : List UInt8 :=
  encodeUnsignedFixed width.bytes value.toUnsigned

/-- Decode one fixed-width two's-complement SQLite integer. -/
def decodeSignedInteger (width : IntegerWidth) (input : List UInt8) :
    Option (SignedInteger width × List UInt8) := do
  let (unsigned, suffix) ← decodeUnsignedFixed width.bytes input
  if bound : unsigned < width.modulus then
    some (signedIntegerFromUnsigned width ⟨unsigned, bound⟩, suffix)
  else none

theorem encodeSignedInteger_length {width : IntegerWidth}
    (value : SignedInteger width) :
    (encodeSignedInteger value).length = width.bytes := by
  exact encodeUnsignedFixed_length _ _

theorem decodeSignedInteger_encode {width : IntegerWidth}
    (value : SignedInteger width) (suffix : List UInt8) :
    decodeSignedInteger width (encodeSignedInteger value ++ suffix) =
      some (value, suffix) := by
  have unsignedBound := value.toUnsigned_lt
  have encodedBound : value.toUnsigned < 256 ^ width.bytes := by
    rw [← width.modulus_eq_pow]
    exact unsignedBound
  unfold decodeSignedInteger encodeSignedInteger
  rw [decodeUnsignedFixed_encode suffix encodedBound]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos unsignedBound]
  rw [signedIntegerFromUnsigned_toUnsigned]

theorem decodeSignedInteger_short (width : IntegerWidth) (input : List UInt8)
    (short : input.length < width.bytes) :
    decodeSignedInteger width input = none := by
  unfold decodeSignedInteger
  rw [decodeUnsignedFixed_short input short]
  rfl

end FileFormat
end SQLeanite
