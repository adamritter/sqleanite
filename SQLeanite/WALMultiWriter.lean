import SQLeanite.WALConcurrency

namespace SQLeanite.WALConcurrency.Multi

/-!
# Multiple sequential writers with concurrent readers

Unlike the first one-writer theorem, this model accepts arbitrarily many writer
transactions provided their intervals are chronologically ordered and do not
overlap.  Readers may overlap any number of writers and retain the WAL version
visible at their begin tick.
-/

def WritersOrdered : List WriterTxn → Prop
  | [] => True
  | [_] => True
  | first :: second :: writers =>
      first.lifetime.endTick ≤ second.lifetime.beginTick ∧
        WritersOrdered (second :: writers)

structure Schedule where
  initial : WAL
  writers : List WriterTxn
  readers : List ReaderTxn

def Accepts (schedule : Schedule) : Prop :=
  WritersOrdered schedule.writers ∧
  (∀ writer ∈ schedule.writers, writer.lifetime.Valid) ∧
  (∀ reader ∈ schedule.readers, reader.lifetime.Valid) ∧
  (schedule.writers.map WriterTxn.id ++ schedule.readers.map ReaderTxn.id).Nodup

def beforeTick (writer : WriterTxn) (tick : Nat) : Bool :=
  decide (tick < writer.lifetime.endTick)

def commitAll : WAL → List WriterTxn → WAL
  | wal, [] => wal
  | wal, writer :: writers => commitAll (wal.commit writer.next) writers

/-- The version visible at a begin tick.  Writer order is commit order; once a
writer has not yet committed, later writers cannot have committed in an
accepted schedule. -/
def visibleAt : WAL → List WriterTxn → Nat → Core.Database
  | wal, [], _ => wal.visible
  | wal, writer :: writers, tick =>
      if beforeTick writer tick then wal.visible
      else visibleAt (wal.commit writer.next) writers tick

def result (schedule : Schedule) : Outcome := {
  final := (commitAll schedule.initial schedule.writers).visible
  observed := fun id database =>
    ∃ reader ∈ schedule.readers, reader.id = id ∧
      database = visibleAt schedule.initial schedule.writers
        reader.lifetime.beginTick
}

structure Phase where
  readers : List ReaderTxn
  writer : WriterTxn

structure SerialExecution where
  initial : WAL
  phases : List Phase
  trailingReaders : List ReaderTxn

def SerialExecution.writers (serial : SerialExecution) : List WriterTxn :=
  serial.phases.map Phase.writer

def SerialExecution.allReaders (serial : SerialExecution) : List ReaderTxn :=
  serial.phases.flatMap Phase.readers ++ serial.trailingReaders

def SerialExecution.WellFormed (serial : SerialExecution) : Prop :=
  WritersOrdered serial.writers ∧
  (∀ writer ∈ serial.writers, writer.lifetime.Valid) ∧
  (∀ reader ∈ serial.allReaders, reader.lifetime.Valid)

def commitPhases : WAL → List Phase → WAL
  | wal, [] => wal
  | wal, phase :: phases => commitPhases (wal.commit phase.writer.next) phases

def serialObserved : WAL → List Phase → List ReaderTxn → TxnId → Core.Database → Prop
  | wal, [], trailing, id, database =>
      ∃ reader ∈ trailing, reader.id = id ∧ database = wal.visible
  | wal, phase :: phases, trailing, id, database =>
      (∃ reader ∈ phase.readers,
        reader.id = id ∧ database = wal.visible) ∨
      serialObserved (wal.commit phase.writer.next) phases trailing id database

def serialResult (serial : SerialExecution) : Outcome := {
  final := (commitPhases serial.initial serial.phases).visible
  observed := serialObserved serial.initial serial.phases serial.trailingReaders
}

def build : List WriterTxn → List ReaderTxn → List Phase × List ReaderTxn
  | [], readers => ([], readers)
  | writer :: writers, readers =>
      let before := readers.filter (fun reader => beforeTick writer reader.lifetime.beginTick)
      let remaining := readers.filter (fun reader => !beforeTick writer reader.lifetime.beginTick)
      let tail := build writers remaining
      ({ readers := before, writer := writer } :: tail.1, tail.2)

def serialize (schedule : Schedule) : SerialExecution :=
  let built := build schedule.writers schedule.readers
  { initial := schedule.initial, phases := built.1, trailingReaders := built.2 }

theorem build_writers (writers : List WriterTxn) (readers : List ReaderTxn) :
    (build writers readers).1.map Phase.writer = writers := by
  induction writers generalizing readers with
  | nil => rfl
  | cons writer writers induction =>
      simp [build, induction]

theorem build_readers_perm (writers : List WriterTxn) (readers : List ReaderTxn) :
    ((build writers readers).1.flatMap Phase.readers ++ (build writers readers).2).Perm
      readers := by
  induction writers generalizing readers with
  | nil => rfl
  | cons writer writers induction =>
      simp only [build, List.flatMap_cons]
      let predicate := fun reader : ReaderTxn => beforeTick writer reader.lifetime.beginTick
      have tail := induction (readers.filter fun reader => !predicate reader)
      have partition := List.filter_append_perm predicate readers
      simpa [predicate, List.append_assoc] using
        (List.Perm.append_left (readers.filter predicate) tail).trans partition

theorem commitPhases_build (wal : WAL) (writers : List WriterTxn)
    (readers : List ReaderTxn) :
    commitPhases wal (build writers readers).1 = commitAll wal writers := by
  induction writers generalizing wal readers with
  | nil => rfl
  | cons writer writers induction =>
      simp [build, commitPhases, commitAll, induction]

theorem serialObserved_build (wal : WAL) (writers : List WriterTxn)
    (readers : List ReaderTxn) (id : TxnId) (database : Core.Database) :
    serialObserved wal (build writers readers).1 (build writers readers).2 id database ↔
      ∃ reader ∈ readers, reader.id = id ∧
        database = visibleAt wal writers reader.lifetime.beginTick := by
  induction writers generalizing wal readers with
  | nil => simp [build, serialObserved, visibleAt]
  | cons writer writers induction =>
      simp only [build, serialObserved, visibleAt]
      constructor
      · rintro (⟨reader, filtered, idEq, databaseEq⟩ | later)
        · have parts := List.mem_filter.mp filtered
          exact ⟨reader, parts.1, idEq, by simpa [parts.2] using databaseEq⟩
        · have laterRaw := (induction (wal := wal.commit writer.next)
            (readers := readers.filter fun reader =>
              !beforeTick writer reader.lifetime.beginTick)).mp later
          rcases laterRaw with ⟨reader, filtered, idEq, databaseEq⟩
          have parts := List.mem_filter.mp filtered
          have notBefore : beforeTick writer reader.lifetime.beginTick = false := by
            simpa using parts.2
          exact ⟨reader, parts.1, idEq, by simpa [notBefore] using databaseEq⟩
      · rintro ⟨reader, membership, idEq, databaseEq⟩
        cases selected : beforeTick writer reader.lifetime.beginTick with
        | false =>
            apply Or.inr
            apply (induction (wal := wal.commit writer.next)
              (readers := readers.filter fun reader =>
                !beforeTick writer reader.lifetime.beginTick)).mpr
            refine ⟨reader, List.mem_filter.mpr ⟨membership, ?_⟩, idEq, ?_⟩
            · simp [selected]
            · simpa [selected] using databaseEq
        | true =>
            exact Or.inl ⟨reader, List.mem_filter.mpr ⟨membership, selected⟩, idEq,
              by simpa [selected] using databaseEq⟩

theorem serialize_wellFormed (schedule : Schedule) (accepted : Accepts schedule) :
    (serialize schedule).WellFormed := by
  rcases accepted with ⟨ordered, writersValid, readersValid, _⟩
  constructor
  · simpa [serialize, SerialExecution.writers, build_writers] using ordered
  constructor
  · intro writer membership
    rw [show (serialize schedule).writers = schedule.writers by
      simp [serialize, SerialExecution.writers, build_writers]] at membership
    exact writersValid writer membership
  · intro reader membership
    have permutation : (serialize schedule).allReaders.Perm schedule.readers := by
      simpa [serialize, SerialExecution.allReaders] using
        build_readers_perm schedule.writers schedule.readers
    exact readersValid reader (permutation.subset membership)

/-- Arbitrarily many non-overlapping writers and arbitrarily interleaved
readers are observationally equivalent to the constructed serial epoch order. -/
theorem accepted_schedules_are_serializable (schedule : Schedule)
    (accepted : Accepts schedule) :
    ∃ serial, serial.WellFormed ∧ result schedule = serialResult serial := by
  refine ⟨serialize schedule, serialize_wellFormed schedule accepted, ?_⟩
  apply Outcome.ext
  · exact congrArg WAL.visible
      (commitPhases_build schedule.initial schedule.writers schedule.readers).symm
  · funext id database
    apply propext
    simpa [result, serialResult, serialize] using
      (serialObserved_build schedule.initial schedule.writers schedule.readers id database).symm

def interleavedTwoWriterExample : Schedule := {
  initial := { main := Core.Database.empty }
  writers := [
    { id := 1
      lifetime := { beginTick := 2, endTick := 4 }
      next := Core.Database.empty },
    { id := 2
      lifetime := { beginTick := 6, endTick := 8 }
      next := Core.Database.empty }]
  readers := [
    { id := 3, lifetime := { beginTick := 1, endTick := 7 } },
    { id := 4, lifetime := { beginTick := 5, endTick := 9 } }]
}

theorem two_nonoverlapping_writers_are_accepted :
    Accepts interleavedTwoWriterExample := by
  simp [Accepts, WritersOrdered, interleavedTwoWriterExample, Interval.Valid]

def overlappingWritersExample : Schedule := {
  initial := { main := Core.Database.empty }
  writers := [
    { id := 1
      lifetime := { beginTick := 1, endTick := 5 }
      next := Core.Database.empty },
    { id := 2
      lifetime := { beginTick := 3, endTick := 7 }
      next := Core.Database.empty }]
  readers := []
}

theorem overlapping_writers_are_rejected : ¬Accepts overlappingWritersExample := by
  simp [Accepts, WritersOrdered, overlappingWritersExample, Interval.Valid]

end SQLeanite.WALConcurrency.Multi
