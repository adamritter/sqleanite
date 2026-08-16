import SQLeanite.PhysicalMultiPageCodec

namespace SQLeanite
namespace PhysicalJournalCodec

open FileFormat

def magic : List UInt8 := [76, 83, 81, 76, 74, 82, 78, 76]

theorem magic_length : magic.length = 8 := rfl

/-- Durable marker stored in the persistent rollback-journal inode when no
transaction is active.  It is deliberately not a prefix of a checked active
journal. The leading zero also makes the retained file non-hot to C SQLite's
rollback-journal detector, so an inactive SQLeanite journal does not interfere
with ordinary SQLite readers. -/
def inactiveMarker : List UInt8 := [0, 83, 81, 76, 73, 78, 65, 67, 84, 73, 86, 69]

def activeMarker : List UInt8 := [76, 83, 81, 76, 65, 67, 84, 73, 86, 69, 74, 49]

theorem activeMarker_length : activeMarker.length = 12 := rfl

def inactiveBytes : ByteArray := ByteArray.mk inactiveMarker.toArray

/-- One-time inode capacity for ordinary point mutations.  Keeping this space
allocated avoids a metadata-growing write on the first transaction while the
length-delimited active envelope continues to support larger journals. -/
def initialPersistentCapacity : Nat := 65536

def initialInactiveBytes : ByteArray := ByteArray.mk
  ((inactiveMarker ++ List.replicate
    (initialPersistentCapacity - inactiveMarker.length) 0).toArray)

theorem inactiveBytes_toList : inactiveBytes.data.toList = inactiveMarker := by
  simp [inactiveBytes]

theorem initialInactiveBytes_prefix :
    initialInactiveBytes.data.toList.take inactiveMarker.length =
      inactiveMarker := by
  change (inactiveMarker ++ List.replicate
    (initialPersistentCapacity - inactiveMarker.length) 0).take
      inactiveMarker.length = inactiveMarker
  rw [List.take_append_of_le_length (Nat.le_refl _)]
  simp

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

/-! The live writer should not have to turn every 4 KiB page into a linked
list and then immediately copy that list back into an array.  The array codec
below is definitionally the same wire format as `encodeChecked`; the theorems
make that optimization part of the checked format boundary rather than a
second, unverified encoder. -/

def encodeUndoArray :
    List (GrowableStorage.UndoRecord PhysicalCodec.pageSize) → Array UInt8
  | [] => #[]
  | record :: records =>
      ((encodeUnsignedFixed 4 record.pageId).toArray.append
        record.before.bytes).append (encodeUndoArray records)

theorem encodeUndoArray_toList
    (records : List (GrowableStorage.UndoRecord PhysicalCodec.pageSize)) :
    (encodeUndoArray records).toList = encodeUndo records := by
  induction records with
  | nil => rfl
  | cons record records induction =>
      simp [encodeUndoArray, encodeUndo, encodeUndoRecord, induction]

def encodeArray (journal : Encodable) : Array UInt8 :=
  ((((magic.toArray.append
    (encodeUnsignedFixed 4 journal.journal.originalPageCount).toArray).append
      (encodeUnsignedFixed 4 journal.journal.undo.length).toArray).append
        (encodeUndoArray journal.journal.undo)))

theorem encodeArray_toList (journal : Encodable) :
    (encodeArray journal).toList = encode journal := by
  simp [encodeArray, encode, encodeUndoArray_toList]

def checksumArray (input : Array UInt8) : Nat :=
  (input.foldl checksumStep 2166136261) % checksumModulus

theorem checksumArray_eq_checksumBytes (input : Array UInt8) :
    checksumArray input = checksumBytes input.toList := by
  simp [checksumArray, checksumBytes]

theorem checksumArray_lt (input : Array UInt8) :
    checksumArray input < checksumModulus := by
  unfold checksumArray
  exact Nat.mod_lt _ (by decide)

def checksumArrayValue (input : Array UInt8) : U32Value :=
  ⟨checksumArray input,
    by simpa [checksumModulus] using checksumArray_lt input⟩

def encodeCheckedBytes (journal : Encodable) : ByteArray :=
  let payload := encodeArray journal
  ⟨(encodeU32Bytes (checksumArrayValue payload)).toArray.append payload⟩

theorem encodeCheckedBytes_toList (journal : Encodable) :
    (encodeCheckedBytes journal).data.toList = encodeChecked journal := by
  simp [encodeCheckedBytes, encodeChecked, checksumArrayValue,
    checksumValue, checksumArray_eq_checksumBytes, encodeArray_toList]

/-- Evidence that the checked journal length fits the persistent envelope's
eight-byte length field.  This is checked once before any journal syscall. -/
structure PersistentEncodable where
  checked : Encodable
  lengthFits : (encodeChecked checked).length < 256 ^ 8

def ofEncodable? (journal : Encodable) : Option PersistentEncodable :=
  if fits : (encodeChecked journal).length < 256 ^ 8 then
    some ⟨journal, fits⟩
  else none

def encodePersistentActive (journal : PersistentEncodable) : List UInt8 :=
  activeMarker ++ encodeUnsignedFixed 8 (encodeChecked journal.checked).length ++
    encodeChecked journal.checked

def encodePersistentActiveBytes (journal : PersistentEncodable) : ByteArray :=
  let checked := encodeCheckedBytes journal.checked
  ByteArray.mk (((activeMarker.toArray.append
    (encodeUnsignedFixed 8 (encodeChecked journal.checked).length).toArray).append
      checked.data))

theorem encodePersistentActiveBytes_toList (journal : PersistentEncodable) :
    (encodePersistentActiveBytes journal).data.toList =
      encodePersistentActive journal := by
  simp [encodePersistentActiveBytes, encodePersistentActive,
    encodeCheckedBytes_toList]

def decodeChecked (input : List UInt8) :
    Option (GrowableStorage.Journal PhysicalCodec.pageSize) := do
  let (storedChecksum, payload) ← decodeU32Bytes input
  let (journal, suffix) ← decode payload
  if _consumed : suffix = [] then
    if _checksumMatches : storedChecksum.val = checksumBytes payload then
      some journal
    else none
  else none

/-- Decode a length-delimited active record from the beginning of a persistent
journal inode.  Bytes beyond the record are deliberately ignored, allowing the
inode to retain its high-water size across transactions. -/
def decodePersistentActive (input : List UInt8) :
    Option (GrowableStorage.Journal PhysicalCodec.pageSize) := do
  let (decodedMarker, afterMarker) ←
    decodeSizedBytes activeMarker.length input
  if _active : decodedMarker.bytes = activeMarker then
    let (length, afterLength) ← decodeUnsignedFixed 8 afterMarker
    let (payload, _) ← decodeSizedBytes length afterLength
    decodeChecked payload.bytes
  else none

/-- Decode the stable persistent-journal file.  `some none` is the durable
inactive state; `some (some journal)` is an active rollback record; `none`
rejects torn or otherwise malformed contents.  The final fallback accepts an
active journal left by the former rename/delete protocol during migration. -/
def decodePersistent (input : List UInt8) :
    Option (Option (GrowableStorage.Journal PhysicalCodec.pageSize)) :=
  if _inactive : input.take inactiveMarker.length = inactiveMarker then some none
  else match decodePersistentActive input with
    | some journal => some (some journal)
    | none => (decodeChecked input).map some

theorem decodePersistent_inactive :
    decodePersistent inactiveMarker = some none := by
  simp [decodePersistent]

theorem decodePersistent_initialInactive :
    decodePersistent initialInactiveBytes.data.toList = some none := by
  simp [decodePersistent, initialInactiveBytes_prefix]

theorem decodeChecked_encode (journal : Encodable) :
    decodeChecked (encodeChecked journal) = some journal.journal := by
  unfold encodeChecked decodeChecked
  rw [decodeU32Bytes_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show encode journal = encode journal ++ [] by simp,
    decode_encode journal []]
  simp [checksumValue]

theorem decodeChecked_encodeBytes (journal : Encodable) :
    decodeChecked (encodeCheckedBytes journal).data.toList =
      some journal.journal := by
  rw [encodeCheckedBytes_toList, decodeChecked_encode]

theorem decodePersistentActive_encode (journal : PersistentEncodable)
    (suffix : List UInt8) :
    decodePersistentActive (encodePersistentActive journal ++ suffix) =
      some journal.checked.journal := by
  let markerBytes : SizedBytes activeMarker.length := ⟨activeMarker, rfl⟩
  let checkedBytes : SizedBytes (encodeChecked journal.checked).length :=
    ⟨encodeChecked journal.checked, rfl⟩
  unfold encodePersistentActive decodePersistentActive
  change (do
    let (decodedMarker, afterMarker) ← decodeSizedBytes activeMarker.length
      (markerBytes.bytes ++
        (encodeUnsignedFixed 8 (encodeChecked journal.checked).length ++
          (checkedBytes.bytes ++ suffix)))
    if _active : decodedMarker.bytes = activeMarker then
      let (length, afterLength) ← decodeUnsignedFixed 8 afterMarker
      let (payload, _) ← decodeSizedBytes length afterLength
      decodeChecked payload.bytes
    else none) = some journal.checked.journal
  rw [decodeSizedBytes_append]
  simp only [Option.bind_eq_bind, Option.bind]
  simp [markerBytes]
  rw [decodeUnsignedFixed_encode _ journal.lengthFits]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeSizedBytes_append]
  simp [checkedBytes, decodeChecked_encode]

theorem decodePersistent_encode (journal : PersistentEncodable)
    (suffix : List UInt8) :
    decodePersistent (encodePersistentActive journal ++ suffix) =
      some (some journal.checked.journal) := by
  have notInactive :
      (encodePersistentActive journal ++ suffix).take inactiveMarker.length ≠
        inactiveMarker := by
    simp [encodePersistentActive, inactiveMarker, activeMarker]
  simp [decodePersistent, notInactive,
    decodePersistentActive_encode journal suffix]

theorem decodePersistent_encodeBytes (journal : PersistentEncodable) :
    decodePersistent (encodePersistentActiveBytes journal).data.toList =
      some (some journal.checked.journal) := by
  rw [encodePersistentActiveBytes_toList]
  simpa using decodePersistent_encode journal []

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
