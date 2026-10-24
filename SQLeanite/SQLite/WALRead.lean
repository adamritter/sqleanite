import SQLeanite.PhysicalWAL

/-! SQLite WAL recovery over the valid committed prefix. The canonical writer
keeps its separate round-trip proofs; this reader also admits SQLite's other
checksum byte order, variable page sizes, partial-page transactions, and torn
or stale tails. OS locking and concurrent wal-index coordination are outside
this pure byte decoder. -/
namespace SQLeanite.SQLite.WALRead

open FileFormat PhysicalWAL

def checksumLittle : Checksum → List UInt8 → Checksum
  | seed, a :: b :: c :: d :: e :: f :: g :: h :: rest =>
      checksumLittle (seed.step (word d c b a) (word h g f e)) rest
  | seed, _ => seed

def checksum (bigEndian : Bool) (seed : Checksum) (input : List UInt8) : Checksum :=
  if bigEndian then PhysicalWAL.checksumBytes seed input else checksumLittle seed input

structure Header where
  pageSize : Nat
  bigEndian : Bool
  saltFirst : U32Value
  saltSecond : U32Value
  seed : Checksum

/-- Invalid or incomplete headers describe an empty log. A valid checksum with
an unsupported format version is an error, matching SQLite's recovery order. -/
def decodeHeader (input : List UInt8) : Except String (Option (Header × List UInt8)) := do
  if input.length ≤ 32 then return none
  let some (words, rest) := decodeWords 8 input | return none
  match words with
  | [magic, version, pageSize, _, saltFirst, saltSecond, first, second] =>
      unless (magic.val == 0x377f0682 || magic.val == 0x377f0683) &&
          decide (ValidSQLitePageSize pageSize.val) do return none
      let bigEndian := magic.val == 0x377f0683
      let seed := checksum bigEndian .zero (input.take 24)
      unless seed.first == first && seed.second == second do return none
      unless version.val == walVersion do throw "unsupported SQLite WAL format version"
      return some (⟨pageSize.val, bigEndian, saltFirst, saltSecond, seed⟩, rest)
  | _ => return none

structure Frame where
  pageNumber : Nat
  databaseSize : Nat
  page : List UInt8

/-- A frame is accepted only with matching salts, a positive page number, a
complete payload, and the checksum chained from every preceding valid frame. -/
def decodeFrame (header : Header) (seed : Checksum) (input : List UInt8) :
    Option (Frame × Checksum × List UInt8) := do
  let (words, data) ← decodeWords 6 input
  match words with
  | [pageNumber, databaseSize, saltFirst, saltSecond, first, second] =>
      if pageNumber.val == 0 || saltFirst != header.saltFirst ||
          saltSecond != header.saltSecond || data.length < header.pageSize then none
      else
        let page := data.take header.pageSize
        let next := checksum header.bigEndian seed (input.take 8 ++ page)
        if next.first == first && next.second == second then
          some (⟨pageNumber.val, databaseSize.val, page⟩, next, data.drop header.pageSize)
        else none
  | _ => none

/-- Stop at the first bad frame. Later bytes cannot repair a broken checksum
chain, and a final incomplete frame is never part of a committed prefix. -/
def decodeFrames (header : Header) :
    Nat → Checksum → List UInt8 → List Frame
  | 0, _, _ => []
  | fuel + 1, seed, input =>
      match decodeFrame header seed input with
      | none => []
      | some (frame, next, rest) => frame :: decodeFrames header fuel next rest

structure Snapshot where
  pageSize : Nat
  pageCount : Nat
  /-- Newest first, so repeated page writes use the most recent committed one. -/
  frames : List Frame

structure Replay where
  pending : List Frame := []
  committed : Option Snapshot := none

def Replay.push (pageSize : Nat) (state : Replay) (frame : Frame) : Replay :=
  let pending := frame :: state.pending
  { pending
    committed := if frame.databaseSize == 0 then state.committed
      else some ⟨pageSize, frame.databaseSize, pending⟩ }

def Replay.run (pageSize : Nat) : Replay → List Frame → Replay
  | state, [] => state
  | state, frame :: frames => Replay.run pageSize (state.push pageSize frame) frames

def recover (input : List UInt8) : Except String (Option Snapshot) := do
  let some (header, rest) ← decodeHeader input | return none
  let frames := decodeFrames header (rest.length / (24 + header.pageSize)) header.seed rest
  return (Replay.run header.pageSize {} frames).committed

/-- Untouched pages come from the main database. Only a committed snapshot's
page count controls visibility; a shrinking commit hides older higher pages. -/
def Snapshot.readPage (snapshot : Snapshot) (base : Nat → Option (List UInt8))
    (pageNumber : Nat) : Option (List UInt8) :=
  if pageNumber == 0 || snapshot.pageCount < pageNumber then none
  else match snapshot.frames.find? (fun frame => frame.pageNumber == pageNumber) with
    | some frame => some frame.page
    | none => base pageNumber

theorem decodeFrames_invalid (header : Header) (fuel : Nat) (seed : Checksum)
    (input : List UInt8) (invalid : decodeFrame header seed input = none) :
    decodeFrames header (fuel + 1) seed input = [] := by
  simp [decodeFrames, invalid]

/-- Any number of checksum-valid but uncommitted trailing frames leaves the
last committed snapshot unchanged. This is the replay used by `recover`. -/
theorem Replay.run_uncommitted (pageSize : Nat) (state : Replay) (frames : List Frame)
    (uncommitted : ∀ frame ∈ frames, frame.databaseSize = 0) :
    (Replay.run pageSize state frames).committed = state.committed := by
  induction frames generalizing state with
  | nil => rfl
  | cons frame frames ih =>
    simp only [Replay.run]
    rw [ih (state.push pageSize frame) (by
      intro f member; exact uncommitted f (by simp [member]))]
    simp [Replay.push, uncommitted frame (by simp)]

theorem Snapshot.readPage_base (snapshot : Snapshot) (base : Nat → Option (List UInt8))
    (pageNumber : Nat) (positive : pageNumber ≠ 0) (within : pageNumber ≤ snapshot.pageCount)
    (untouched : snapshot.frames.find? (fun frame => frame.pageNumber == pageNumber) = none) :
    snapshot.readPage base pageNumber = base pageNumber := by
  simp [Snapshot.readPage, positive, Nat.not_lt_of_ge within, untouched]

theorem Snapshot.readPage_newest (pageSize pageCount : Nat) (frame : Frame)
    (frames : List Frame) (base : Nat → Option (List UInt8))
    (positive : frame.pageNumber ≠ 0) (within : frame.pageNumber ≤ pageCount) :
    (Snapshot.mk pageSize pageCount (frame :: frames)).readPage base frame.pageNumber =
      some frame.page := by
  simp [Snapshot.readPage, positive, Nat.not_lt_of_ge within]

end SQLeanite.SQLite.WALRead
