import SQLeanite.PhysicalMultiPageCodec

namespace SQLeanite
namespace PhysicalWAL

open FileFormat

def walMagic : Nat := 0x377f0683
def walVersion : Nat := 3007000
def modulus : Nat := 2 ^ 32
def frameSize : Nat := 24 + PhysicalCodec.pageSize

def walMagicValue : U32Value := ⟨walMagic, by decide⟩
def walVersionValue : U32Value := ⟨walVersion, by decide⟩
def walPageSizeValue : U32Value := ⟨PhysicalCodec.pageSize, by decide⟩

structure Checksum where
  first : U32Value
  second : U32Value
  deriving DecidableEq, Repr

def Checksum.zero : Checksum :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

def Checksum.step (checksum : Checksum) (firstWord secondWord : Nat) : Checksum :=
  let nextFirst := (checksum.first.val + firstWord + checksum.second.val) % modulus
  let nextSecond := (checksum.second.val + secondWord + nextFirst) % modulus
  { first := ⟨nextFirst, Nat.mod_lt _ (by simp [modulus])⟩
    second := ⟨nextSecond, Nat.mod_lt _ (by simp [modulus])⟩ }

def word (a b c d : UInt8) : Nat :=
  a.toNat * 256 ^ 3 + b.toNat * 256 ^ 2 + c.toNat * 256 + d.toNat

theorem word_encodeU32 (value : U32Value) :
    let bytes := encodeU32 value
    word bytes.first bytes.second bytes.third bytes.fourth = value.val := by
  simpa [word, decodeU32] using decodeU32_encode value

/-- SQLite's WAL checksum recurrence over big-endian pairs of 32-bit words.
The selected magic `0x377f0683` declares this byte order. -/
def checksumBytes : Checksum → List UInt8 → Checksum
  | checksum, a :: b :: c :: d :: e :: f :: g :: h :: bytes =>
      checksumBytes
        (checksum.step (word a b c d) (word e f g h)) bytes
  | checksum, _ => checksum

theorem checksumBytes_encodePair (seed : Checksum) (first second : U32Value)
    (suffix : List UInt8) :
    checksumBytes seed
        (encodeU32Bytes first ++ (encodeU32Bytes second ++ suffix)) =
      checksumBytes (seed.step first.val second.val) suffix := by
  unfold encodeU32Bytes
  simp only [List.append_assoc, List.cons_append, List.nil_append, checksumBytes]
  rw [word_encodeU32, word_encodeU32]

def encodeWords : List U32Value → List UInt8
  | [] => []
  | value :: values => encodeU32Bytes value ++ encodeWords values

def decodeWords : Nat → List UInt8 → Option (List U32Value × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (value, afterValue) ← decodeU32Bytes input
      let (values, suffix) ← decodeWords count afterValue
      some (value :: values, suffix)

theorem decodeWords_encode (values : List U32Value) (suffix : List UInt8) :
    decodeWords values.length (encodeWords values ++ suffix) =
      some (values, suffix) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.length_cons, encodeWords, List.append_assoc, decodeWords]
      rw [decodeU32Bytes_encode]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [induction]

theorem encodeWords_length (values : List U32Value) :
    (encodeWords values).length = 4 * values.length := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [encodeWords, List.length_append, List.length_cons]
      rw [show (encodeU32Bytes value).length = 4 by
        simp [encodeU32Bytes, encodeUnsignedFixed_length]]
      omega

structure Header where
  checkpointSequence : U32Value
  saltFirst : U32Value
  saltSecond : U32Value
  deriving DecidableEq, Repr

def Header.prefix (header : Header) : List UInt8 :=
  encodeU32Bytes walMagicValue ++
    encodeU32Bytes walVersionValue ++
    encodeU32Bytes walPageSizeValue ++
    encodeU32Bytes header.checkpointSequence ++
    encodeU32Bytes header.saltFirst ++
    encodeU32Bytes header.saltSecond

theorem Header.prefix_length (header : Header) : header.prefix.length = 24 := by
  simp [Header.prefix, encodeU32Bytes, encodeUnsignedFixed_length]

@[irreducible] def Header.checksum (header : Header) : Checksum :=
  (((Checksum.zero.step walMagic walVersion).step
      PhysicalCodec.pageSize header.checkpointSequence.val).step
    header.saltFirst.val header.saltSecond.val)

theorem Header.checksum_spec (header : Header) :
    header.checksum =
      (((Checksum.zero.step walMagic walVersion).step
          PhysicalCodec.pageSize header.checkpointSequence.val).step
        header.saltFirst.val header.saltSecond.val) := by
  unfold Header.checksum
  rfl

theorem Header.checksum_bytes (header : Header) :
    checksumBytes .zero header.prefix = header.checksum := by
  unfold Header.prefix
  simp only [List.append_assoc]
  rw [checksumBytes_encodePair, checksumBytes_encodePair]
  have last := checksumBytes_encodePair
    ((Checksum.zero.step walMagicValue.val walVersionValue.val).step
      walPageSizeValue.val header.checkpointSequence.val)
    header.saltFirst header.saltSecond []
  simp only [List.append_nil, checksumBytes] at last
  rw [last]
  exact header.checksum_spec.symm

def Header.wordsWithChecksum (header : Header) (checksum : Checksum) :
    List U32Value :=
  [walMagicValue, walVersionValue, walPageSizeValue,
    header.checkpointSequence, header.saltFirst, header.saltSecond,
    checksum.first, checksum.second]

def Header.words (header : Header) : List U32Value :=
  header.wordsWithChecksum header.checksum

def Header.encode (header : Header) : List UInt8 :=
  encodeWords header.words

theorem Header.encode_length (header : Header) : header.encode.length = 32 := by
  rw [Header.encode, encodeWords_length]
  simp [Header.words, Header.wordsWithChecksum]

def decodeHeader (input : List UInt8) : Option (Header × Checksum × List UInt8) := do
  let (words, suffix) ← decodeWords 8 input
  match words with
  | [magic, version, pageSize, checkpointSequence, saltFirst, saltSecond,
      checksumFirst, checksumSecond] =>
      let header : Header := ⟨checkpointSequence, saltFirst, saltSecond⟩
      let expected := header.checksum
      if _magic : magic.val = walMagic then
        if _version : version.val = walVersion then
          if _pageSize : pageSize.val = PhysicalCodec.pageSize then
            if _checksum : checksumFirst = expected.first ∧
                checksumSecond = expected.second then
              some (header, expected, suffix)
            else none
          else none
        else none
      else none
  | _ => none

theorem decodeHeader_wordsWithChecksum (header : Header) (checksum : Checksum)
    (valid : checksum = header.checksum) (suffix : List UInt8) :
    decodeHeader (encodeWords (header.wordsWithChecksum checksum) ++ suffix) =
      some (header, header.checksum, suffix) := by
  unfold decodeHeader
  have count : (header.wordsWithChecksum checksum).length = 8 := by
    simp [Header.wordsWithChecksum]
  rw [← count, decodeWords_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  unfold Header.wordsWithChecksum
  dsimp only
  have magicEq : walMagicValue.val = walMagic := rfl
  have versionEq : walVersionValue.val = walVersion := rfl
  have pageSizeEq : walPageSizeValue.val = PhysicalCodec.pageSize := rfl
  rw [dif_pos magicEq, dif_pos versionEq, dif_pos pageSizeEq]
  have checksumEq : checksum.first = header.checksum.first ∧
      checksum.second = header.checksum.second := by
    constructor <;> rw [valid]
  rw [dif_pos checksumEq]

theorem decodeHeader_encode (header : Header) (suffix : List UInt8) :
    decodeHeader (header.encode ++ suffix) =
      some (header, header.checksum, suffix) := by
  unfold Header.encode Header.words
  exact decodeHeader_wordsWithChecksum header header.checksum rfl suffix

structure Frame where
  pageNumber : PageNumber
  databaseSize : U32Value
  page : Storage.Page PhysicalCodec.pageSize

def Frame.checksumInput (frame : Frame) : List UInt8 :=
  frame.pageNumber.encode ++ encodeU32Bytes frame.databaseSize ++
    frame.page.bytes.toList

def Frame.checksum (seed : Checksum) (frame : Frame) : Checksum :=
  checksumBytes seed frame.checksumInput

def Frame.encode (header : Header) (seed : Checksum) (frame : Frame) : List UInt8 :=
  let checksum := frame.checksum seed
  frame.pageNumber.encode ++ encodeU32Bytes frame.databaseSize ++
    encodeU32Bytes header.saltFirst ++ encodeU32Bytes header.saltSecond ++
    encodeU32Bytes checksum.first ++ encodeU32Bytes checksum.second ++
    frame.page.bytes.toList

theorem Frame.encode_length (header : Header) (seed : Checksum) (frame : Frame) :
    (frame.encode header seed).length = frameSize := by
  simp [Frame.encode, frameSize, PageNumber.encode, encodeU32Bytes,
    frame.page.sizeInvariant]
  omega

def decodeFrame (header : Header) (seed : Checksum) (input : List UInt8) :
    Option (Frame × Checksum × List UInt8) := do
  let (pageNumber, afterPageNumber) ← decodePageNumber input
  let (databaseSize, afterDatabaseSize) ← decodeU32Bytes afterPageNumber
  let (saltFirst, afterSaltFirst) ← decodeU32Bytes afterDatabaseSize
  let (saltSecond, afterSaltSecond) ← decodeU32Bytes afterSaltFirst
  let (checksumFirst, afterChecksumFirst) ← decodeU32Bytes afterSaltSecond
  let (checksumSecond, afterChecksumSecond) ← decodeU32Bytes afterChecksumFirst
  let (page, suffix) ←
    DiskFormat.decodeStoragePage PhysicalCodec.pageSize afterChecksumSecond
  let frame : Frame := ⟨pageNumber, databaseSize, page⟩
  let expected := frame.checksum seed
  if _salt : saltFirst = header.saltFirst ∧ saltSecond = header.saltSecond then
    if _checksum : checksumFirst = expected.first ∧
        checksumSecond = expected.second then
      some (frame, expected, suffix)
    else none
  else none

theorem decodeFrame_encode (header : Header) (seed : Checksum) (frame : Frame)
    (suffix : List UInt8) :
    decodeFrame header seed (frame.encode header seed ++ suffix) =
      some (frame, frame.checksum seed, suffix) := by
  unfold Frame.encode decodeFrame
  simp only [List.append_assoc]
  rw [decodePageNumber_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeU32Bytes_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeU32Bytes_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeU32Bytes_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeU32Bytes_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeU32Bytes_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [DiskFormat.decodeStoragePage_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  simp only [true_and, dif_pos True.intro]

def encodeFrames (header : Header) : Checksum → List Frame → List UInt8
  | _, [] => []
  | seed, frame :: frames =>
      frame.encode header seed ++ encodeFrames header (frame.checksum seed) frames

def decodeFrames (header : Header) : Nat → Checksum → List UInt8 →
    Option (List Frame × Checksum × List UInt8)
  | 0, seed, input => some ([], seed, input)
  | count + 1, seed, input => do
      let (frame, nextChecksum, afterFrame) ← decodeFrame header seed input
      let (frames, finalChecksum, suffix) ←
        decodeFrames header count nextChecksum afterFrame
      some (frame :: frames, finalChecksum, suffix)

def finalChecksum (header : Header) : Checksum → List Frame → Checksum
  | seed, [] => seed
  | seed, frame :: frames =>
      finalChecksum header (frame.checksum seed) frames

theorem decodeFrames_encode (header : Header) (frames : List Frame)
    (seed : Checksum) (suffix : List UInt8) :
    decodeFrames header frames.length seed
      (encodeFrames header seed frames ++ suffix) =
      some (frames, finalChecksum header seed frames, suffix) := by
  induction frames generalizing seed with
  | nil => rfl
  | cons frame frames induction =>
      simp only [List.length_cons, encodeFrames, List.append_assoc, decodeFrames]
      rw [decodeFrame_encode]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [induction]
      rfl

structure WAL where
  header : Header
  frames : List Frame

def WAL.encode (wal : WAL) : List UInt8 :=
  wal.header.encode ++
    encodeFrames wal.header wal.header.checksum wal.frames

def decodeWithFrameCount (frameCount : Nat) (input : List UInt8) :
    Option (WAL × List UInt8) := do
  let (header, headerChecksum, afterHeader) ← decodeHeader input
  let (frames, _finalChecksum, suffix) ←
    decodeFrames header frameCount headerChecksum afterHeader
  some (⟨header, frames⟩, suffix)

theorem decodeWithFrameCount_encode (wal : WAL) (suffix : List UInt8) :
    decodeWithFrameCount wal.frames.length (wal.encode ++ suffix) =
      some (wal, suffix) := by
  unfold WAL.encode decodeWithFrameCount
  rw [List.append_assoc, decodeHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeFrames_encode]

theorem encodeFrames_length (header : Header) (frames : List Frame)
    (seed : Checksum) :
    (encodeFrames header seed frames).length = frameSize * frames.length := by
  induction frames generalizing seed with
  | nil => rfl
  | cons frame frames induction =>
      rw [encodeFrames, List.length_append, frame.encode_length, induction]
      simp [Nat.mul_succ, Nat.add_comm]

def decode (input : List UInt8) : Option WAL := do
  if _header : 32 ≤ input.length then
    let remaining := input.length - 32
    if _aligned : remaining % frameSize = 0 then
      let frameCount := remaining / frameSize
      let (wal, suffix) ← decodeWithFrameCount frameCount input
      if _consumed : suffix = [] then some wal else none
    else none
  else none

theorem WAL.encode_length (wal : WAL) :
    wal.encode.length = 32 + frameSize * wal.frames.length := by
  unfold WAL.encode
  rw [List.length_append, wal.header.encode_length]
  rw [encodeFrames_length]

theorem decode_encode (wal : WAL) : decode wal.encode = some wal := by
  unfold decode
  have length := wal.encode_length
  have header : 32 ≤ wal.encode.length := by omega
  rw [dif_pos header]
  have remaining : wal.encode.length - 32 = frameSize * wal.frames.length := by
    omega
  rw [show wal.encode.length - 32 = frameSize * wal.frames.length from remaining]
  have frameSizePositive : 0 < frameSize := by decide
  have aligned : (frameSize * wal.frames.length) % frameSize = 0 := by
    exact Nat.mul_mod_right _ _
  rw [dif_pos aligned]
  rw [Nat.mul_div_right _ frameSizePositive]
  dsimp only
  rw [show decodeWithFrameCount wal.frames.length wal.encode = some (wal, []) by
    simpa using decodeWithFrameCount_encode wal []]
  simp

end PhysicalWAL
end SQLeanite
