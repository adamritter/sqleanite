import SQLeanite.PhysicalMultiPageCodec

namespace SQLeanite
namespace PhysicalJournalCodec

open FileFormat

def magic : List UInt8 := [76, 83, 81, 76, 74, 82, 78, 76]

theorem magic_length : magic.length = 8 := rfl

structure Encodable where
  journal : GrowableStorage.Journal PhysicalCodec.pageSize
  originalPageCountFits : journal.originalPageCount < 2 ^ 32
  undoCountFits : journal.undo.length < 2 ^ 32
  pageIdsFit : ∀ record ∈ journal.undo, record.pageId < 2 ^ 32

def encodeUndoRecord
    (record : GrowableStorage.UndoRecord PhysicalCodec.pageSize) : List UInt8 :=
  encodeUnsignedFixed 4 record.pageId ++ record.before.bytes.toList

def encodeUndo (records : List (GrowableStorage.UndoRecord PhysicalCodec.pageSize)) :
    List UInt8 :=
  records.flatMap encodeUndoRecord

def encode (journal : Encodable) : List UInt8 :=
  magic ++ encodeUnsignedFixed 4 journal.journal.originalPageCount ++
    encodeUnsignedFixed 4 journal.journal.undo.length ++
      encodeUndo journal.journal.undo

def decodeUndo : Nat → List UInt8 →
    Option (List (GrowableStorage.UndoRecord PhysicalCodec.pageSize) × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (pageId, afterPageId) ← decodeUnsignedFixed 4 input
      let (page, afterPage) ←
        DiskFormat.decodeStoragePage PhysicalCodec.pageSize afterPageId
      let (records, suffix) ← decodeUndo count afterPage
      some (⟨pageId, page⟩ :: records, suffix)

theorem decodeUndo_encode
    (records : List (GrowableStorage.UndoRecord PhysicalCodec.pageSize))
    (pageIdsFit : ∀ record ∈ records, record.pageId < 2 ^ 32)
    (suffix : List UInt8) :
    decodeUndo records.length (encodeUndo records ++ suffix) =
      some (records, suffix) := by
  induction records with
  | nil => rfl
  | cons record records induction =>
      simp only [encodeUndo, List.flatMap_cons, encodeUndoRecord,
        List.append_assoc, List.length_cons, decodeUndo]
      have pageIdBound : record.pageId < 256 ^ 4 := by
        simpa using pageIdsFit record (by simp)
      rw [decodeUnsignedFixed_encode _ pageIdBound]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [DiskFormat.decodeStoragePage_encode]
      simp only [Option.bind_eq_bind, Option.bind]
      change (decodeUndo records.length (encodeUndo records ++ suffix)).bind
        (fun result => some (⟨record.pageId, record.before⟩ :: result.1,
          result.2)) = some (record :: records, suffix)
      rw [induction (fun candidate member =>
        pageIdsFit candidate (by simp [member]))]
      rfl

def decode (input : List UInt8) :
    Option (GrowableStorage.Journal PhysicalCodec.pageSize × List UInt8) := do
  let (decodedMagic, afterMagic) ← decodeSizedBytes magic.length input
  if _magicMatches : decodedMagic.bytes = magic then
    let (originalPageCount, afterOriginalCount) ←
      decodeUnsignedFixed 4 afterMagic
    let (undoCount, afterUndoCount) ←
      decodeUnsignedFixed 4 afterOriginalCount
    let (undo, suffix) ← decodeUndo undoCount afterUndoCount
    some (⟨originalPageCount, undo⟩, suffix)
  else none

theorem decode_encode (journal : Encodable) (suffix : List UInt8) :
    decode (encode journal ++ suffix) = some (journal.journal, suffix) := by
  let magicBytes : SizedBytes magic.length := ⟨magic, rfl⟩
  have originalBound : journal.journal.originalPageCount < 256 ^ 4 := by
    simpa using journal.originalPageCountFits
  have undoCountBound : journal.journal.undo.length < 256 ^ 4 := by
    simpa using journal.undoCountFits
  unfold encode decode
  change (do
    let (decodedMagic, afterMagic) ←
      decodeSizedBytes magic.length (magicBytes.bytes ++
        (encodeUnsignedFixed 4 journal.journal.originalPageCount ++
          (encodeUnsignedFixed 4 journal.journal.undo.length ++
            (encodeUndo journal.journal.undo ++ suffix))))
    if _magicMatches : decodedMagic.bytes = magic then
      let (originalPageCount, afterOriginalCount) ←
        decodeUnsignedFixed 4 afterMagic
      let (undoCount, afterUndoCount) ←
        decodeUnsignedFixed 4 afterOriginalCount
      let (undo, remaining) ← decodeUndo undoCount afterUndoCount
      some (⟨originalPageCount, undo⟩, remaining)
    else none) = some (journal.journal, suffix)
  rw [decodeSizedBytes_append]
  simp only [Option.bind_eq_bind, Option.bind, dif_pos rfl]
  rw [decodeUnsignedFixed_encode _ originalBound]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeUnsignedFixed_encode _ undoCountBound]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeUndo_encode journal.journal.undo journal.pageIdsFit suffix]
  cases journal
  rfl

def ofJournal? (journal : GrowableStorage.Journal PhysicalCodec.pageSize) :
    Option Encodable :=
  if originalFits : journal.originalPageCount < 2 ^ 32 then
    if countFits : journal.undo.length < 2 ^ 32 then
      if pageIdsFit : ∀ record ∈ journal.undo, record.pageId < 2 ^ 32 then
        some ⟨journal, originalFits, countFits, pageIdsFit⟩
      else none
    else none
  else none

theorem ofJournal?_roundtrip {journal : GrowableStorage.Journal PhysicalCodec.pageSize}
    {encoded : Encodable} (accepted : ofJournal? journal = some encoded) :
    decode (encode encoded) = some (journal, []) := by
  have decoded := decode_encode encoded []
  simp only [List.append_nil] at decoded
  unfold ofJournal? at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  injection accepted with equal
  subst encoded
  exact decoded

theorem ofJournal?_journal {journal :
    GrowableStorage.Journal PhysicalCodec.pageSize} {encoded : Encodable}
    (accepted : ofJournal? journal = some encoded) :
    encoded.journal = journal := by
  unfold ofJournal? at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  injection accepted with equal
  subst encoded
  rfl

/-! ## Checksummed live journal envelope

The legacy `encode`/`decode` pair remains available for format-level proofs.
The file adapters use this envelope, whose checksum covers every encoded byte.
No collision-resistance axiom is assumed or claimed. -/

def checksumModulus : Nat := 2 ^ 32

def checksumStep (accumulator : Nat) (byte : UInt8) : Nat :=
  (accumulator * 16777619 + byte.toNat + 1) % checksumModulus

def checksumBytes (input : List UInt8) : Nat :=
  (input.foldl checksumStep 2166136261) % checksumModulus

theorem checksumBytes_lt (input : List UInt8) :
    checksumBytes input < checksumModulus := by
  unfold checksumBytes
  exact Nat.mod_lt _ (by decide)

def checksumValue (input : List UInt8) : U32Value :=
  ⟨checksumBytes input, by simpa [checksumModulus] using checksumBytes_lt input⟩

def encodeChecked (journal : Encodable) : List UInt8 :=
  let payload := encode journal
  encodeU32Bytes (checksumValue payload) ++ payload

def decodeChecked (input : List UInt8) :
    Option (GrowableStorage.Journal PhysicalCodec.pageSize) := do
  let (storedChecksum, payload) ← decodeU32Bytes input
  let (journal, suffix) ← decode payload
  if _consumed : suffix = [] then
    if _checksumMatches : storedChecksum.val = checksumBytes payload then
      some journal
    else none
  else none

theorem decodeChecked_encode (journal : Encodable) :
    decodeChecked (encodeChecked journal) = some journal.journal := by
  unfold encodeChecked decodeChecked
  rw [decodeU32Bytes_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show encode journal = encode journal ++ [] by simp,
    decode_encode journal []]
  simp [checksumValue]

/-- The exact checked bytes emitted by the live adapter decode to a journal
containing precisely the old pre-images required by its page delta. -/
theorem decodeChecked_makeJournal_exact
    (old : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (encoded : Encodable)
    (accepted : ofJournal? (GrowableStorage.makeJournal old writes) =
      some encoded) :
    decodeChecked (encodeChecked encoded) =
        some (GrowableStorage.makeJournal old writes) ∧
      encoded.journal.ExactPreimages old writes := by
  have journalEqual := ofJournal?_journal accepted
  constructor
  · rw [decodeChecked_encode, journalEqual]
  · rw [journalEqual]
    exact GrowableStorage.makeJournal_exactPreimages old writes

/-- Acceptance proves that the stored checksum equals the checksum recomputed
over the entire remaining byte stream. This is deliberately weaker than a
false theorem claiming that unequal byte streams cannot collide. -/
theorem decodeChecked_accepts_only_matching (storedChecksum : U32Value)
    (payload : List UInt8)
    (journal : GrowableStorage.Journal PhysicalCodec.pageSize)
    (accepted : decodeChecked (encodeU32Bytes storedChecksum ++ payload) =
      some journal) :
    storedChecksum.val = checksumBytes payload := by
  by_cases checksumEq : storedChecksum.val = checksumBytes payload
  · exact checksumEq
  have rejected :
      decodeChecked (encodeU32Bytes storedChecksum ++ payload) = none := by
    unfold decodeChecked
    rw [decodeU32Bytes_encode]
    simp only [Option.bind_eq_bind, Option.bind]
    cases decoded : decode payload with
    | none => simp [decoded]
    | some result =>
        rcases result with ⟨decodedJournal, suffix⟩
        simp only [decoded]
        by_cases consumed : suffix = []
        · simp [consumed, checksumEq]
        · simp [consumed]
  rw [rejected] at accepted
  contradiction

end PhysicalJournalCodec
end SQLeanite
