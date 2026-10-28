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

theorem encodeU32_decode (bytes : U32Bytes) :
    encodeU32 ⟨decodeU32 bytes, decodeU32_lt bytes⟩ = bytes := by
  rcases bytes with ⟨first, second, third, fourth⟩
  change U32Bytes.mk _ _ _ _ = U32Bytes.mk first second third fourth
  simp only [U32Bytes.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat.inj <;>
    simp only [encodeU32, decodeU32, UInt8.toNat_ofNat']
  all_goals
    have firstBound : first.toNat < 256 := first.toBitVec.isLt
    have secondBound : second.toNat < 256 := second.toBitVec.isLt
    have thirdBound : third.toNat < 256 := third.toBitVec.isLt
    have fourthBound : fourth.toNat < 256 := fourth.toBitVec.isLt
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

theorem decodeU32Bytes_sound {input suffix : List UInt8} {value : U32Value}
    (decoded : decodeU32Bytes input = some (value, suffix)) :
    input = encodeU32Bytes value ++ suffix := by
  cases input with
  | nil => simp [decodeU32Bytes] at decoded
  | cons first rest =>
    cases rest with
    | nil => simp [decodeU32Bytes] at decoded
    | cons second rest =>
      cases rest with
      | nil => simp [decodeU32Bytes] at decoded
      | cons third rest =>
        cases rest with
        | nil => simp [decodeU32Bytes] at decoded
        | cons fourth inputSuffix =>
          simp only [decodeU32Bytes] at decoded
          have pairEquality := Option.some.inj decoded
          injection pairEquality with valueEquality suffixEquality
          subst value
          subst suffix
          have encoded := encodeU32_decode
            ({ first, second, third, fourth } : U32Bytes)
          simp [encodeU32Bytes, encoded]

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

def stripPrefix? (expected input : List UInt8) : Option (List UInt8) :=
  if input.take expected.length == expected then some (input.drop expected.length) else none

theorem stripPrefix_append (expected suffix : List UInt8) :
    stripPrefix? expected (expected ++ suffix) = some suffix := by
  simp [stripPrefix?]

theorem stripPrefix_sound {expected input suffix : List UInt8}
    (decoded : stripPrefix? expected input = some suffix) :
    input = expected ++ suffix := by
  unfold stripPrefix? at decoded
  split at decoded
  next matched =>
    injection decoded with suffixEq
    subst suffix
    have prefixEq : input.take expected.length = expected := by
      simpa using matched
    calc
      input = input.take expected.length ++ input.drop expected.length :=
        (List.take_append_drop expected.length input).symm
      _ = expected ++ input.drop expected.length := by rw [prefixEq]
  next => simp at decoded

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

theorem decodeHeaderPrefix_sound {input suffix : List UInt8}
    {header : HeaderPrefix}
    (decoded : decodeHeaderPrefix input = some (header, suffix)) :
    input = encodeHeaderPrefix header ++ suffix := by
  unfold decodeHeaderPrefix at decoded
  rcases Option.bind_eq_some_iff.mp decoded with
    ⟨afterMagic, magicResult, decoded⟩
  rcases Option.bind_eq_some_iff.mp decoded with
    ⟨pageSizeAndRest, pageSizeResult, decoded⟩
  rcases pageSizeAndRest with ⟨pageSizeField, afterPageSize⟩
  cases afterPageSize with
  | nil => simp at decoded
  | cons writeVersion rest =>
    cases rest with
    | nil => simp at decoded
    | cons readVersion rest =>
      cases rest with
      | nil => simp at decoded
      | cons reservedSpace rest =>
        cases rest with
        | nil => simp at decoded
        | cons fraction64 rest =>
          cases rest with
          | nil => simp at decoded
          | cons fraction32a rest =>
            cases rest with
            | nil => simp at decoded
            | cons fraction32b afterFractions =>
              by_cases firstFraction : fraction64 = 64
              · subst fraction64
                by_cases secondFraction : fraction32a = 32
                · subst fraction32a
                  by_cases thirdFraction : fraction32b = 32
                  · subst fraction32b
                    simp only at decoded
                    rcases Option.bind_eq_some_iff.mp decoded with
                      ⟨counterAndSuffix, counterResult, decoded⟩
                    rcases counterAndSuffix with
                      ⟨changeCounter, decodedSuffix⟩
                    have pairEquality := Option.some.inj decoded
                    injection pairEquality with headerEq suffixEq
                    subst header
                    subst suffix
                    rw [stripPrefix_sound magicResult,
                      decodeU16Bytes_sound pageSizeResult,
                      decodeU32Bytes_sound counterResult]
                    rfl
                  · simp [thirdFraction] at decoded
                · simp [secondFraction] at decoded
              · simp [firstFraction] at decoded

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

theorem decodeU32Values_sound :
    ∀ {count : Nat} {input suffix : List UInt8} {values : List U32Value},
      decodeU32Values count input = some (values, suffix) →
      input = encodeU32Values values ++ suffix
  | 0, input, suffix, values, decoded => by
      simp only [decodeU32Values, Option.some.injEq] at decoded
      injection decoded with valuesEq suffixEq
      subst values
      subst suffix
      rfl
  | count + 1, input, suffix, values, decoded => by
      simp only [decodeU32Values] at decoded
      rcases Option.bind_eq_some_iff.mp decoded with
        ⟨headAndRest, headResult, decoded⟩
      rcases headAndRest with ⟨head, rest⟩
      rcases Option.bind_eq_some_iff.mp decoded with
        ⟨tailAndSuffix, tailResult, decoded⟩
      rcases tailAndSuffix with ⟨tail, decodedSuffix⟩
      have pairEquality := Option.some.inj decoded
      injection pairEquality with valuesEq suffixEq
      subst values
      subst suffix
      simp only at tailResult ⊢
      rw [decodeU32Bytes_sound headResult,
        decodeU32Values_sound tailResult]
      simp [encodeU32Values, List.append_assoc]

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

def DatabaseHeader.beforeReserved (header : DatabaseHeader) : List U32Value :=
  [header.databaseSizePages, header.firstFreelistTrunk, header.freelistPageCount,
    header.schemaCookie, header.schemaFormat, header.defaultPageCacheSize,
    header.largestRootBTreePage, header.textEncoding, header.userVersion,
    header.incrementalVacuum, header.applicationId]

def DatabaseHeader.afterReserved (header : DatabaseHeader) : List U32Value :=
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

end FileFormat

end SQLeanite
