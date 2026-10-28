import SQLeanite.Core.TableReplaceValues

namespace SQLeanite

/-!
# A pure one-writer WAL/MVCC concurrency model

This module models the Tier 2 protocol without pretending that Lean's runtime
threads have formal semantics.  A committed WAL frame publishes an immutable
`Core.Database`; readers that started before publication retain the preceding
value, while later readers see the new one.  Raw schedules can contain any
number of writers, but `Accepts` permits zero or one writer transaction.  This
is the first one-writer theorem, not yet a model of multiple sequential writer
transactions or physical WAL bytes.
-/

namespace WALConcurrency

/-- A logical WAL has a checkpointed main image, newest-first durable frames,
and at most one frame awaiting the durability barrier. -/
structure WAL where
  main : Core.Database
  durableFrames : List Core.Database := []
  pendingFrame : Option Core.Database := none

/-- Readers use only durable frames.  A pending frame is never visible. -/
def WAL.visible (wal : WAL) : Core.Database :=
  wal.durableFrames.head?.getD wal.main

/-- Stage a writer's new immutable database without publishing it. -/
def WAL.appendPending (wal : WAL) (next : Core.Database) : WAL :=
  { wal with pendingFrame := some next }

/-- The WAL sync is the publication point. -/
def WAL.sync (wal : WAL) : WAL :=
  match wal.pendingFrame with
  | none => wal
  | some next =>
      { wal with durableFrames := next :: wal.durableFrames, pendingFrame := none }

/-- One logical commit stages a frame and crosses the WAL durability barrier. -/
def WAL.commit (wal : WAL) (next : Core.Database) : WAL :=
  (wal.appendPending next).sync

/-- Fold the visible WAL version into the main image.  This logical checkpoint
does not model the physical page-copy and sync protocol. -/
def WAL.checkpoint (wal : WAL) : WAL :=
  { main := wal.visible }

theorem WAL.pending_is_invisible (wal : WAL) (next : Core.Database) :
    (wal.appendPending next).visible = wal.visible := by
  simp [WAL.appendPending, WAL.visible]

theorem WAL.commit_publishes (wal : WAL) (next : Core.Database) :
    (wal.commit next).visible = next := by
  simp [WAL.commit, WAL.sync, WAL.appendPending, WAL.visible]

theorem WAL.checkpoint_preserves_visible (wal : WAL) :
    wal.checkpoint.visible = wal.visible := by
  simp [WAL.checkpoint, WAL.visible]

/-- A snapshot is the immutable database value retained at reader begin. -/
structure Snapshot where
  database : Core.Database

def WAL.beginRead (wal : WAL) : Snapshot := ⟨wal.visible⟩

theorem WAL.reader_retains_precommit_snapshot (wal : WAL) (next : Core.Database) :
    (wal.beginRead).database = wal.visible ∧
      (wal.commit next).visible = next := by
  exact ⟨rfl, WAL.commit_publishes wal next⟩

/-- Logical events at the writer-lock/WAL boundary. -/
inductive WriterEvent where
  | lock
  | append (next : Core.Database)
  | sync
  | unlock

structure WriterProtocolState where
  wal : WAL
  lockHeld : Bool

/-- Unlock is permitted only after the pending WAL frame has crossed the sync
barrier.  Append and sync likewise require ownership of the writer lock. -/
def WriterProtocolState.step (state : WriterProtocolState)
    (event : WriterEvent) : Option WriterProtocolState :=
  match event with
  | .lock =>
      if state.lockHeld then none else some { state with lockHeld := true }
  | .append next =>
      if state.lockHeld then some { state with wal := state.wal.appendPending next }
      else none
  | .sync =>
      if state.lockHeld then some { state with wal := state.wal.sync }
      else none
  | .unlock =>
      if state.lockHeld && state.wal.pendingFrame.isNone then
        some { state with lockHeld := false }
      else none

def WriterProtocolState.Safe (state : WriterProtocolState) : Prop :=
  state.lockHeld = false → state.wal.pendingFrame = none

theorem WriterProtocolState.step_preserves_safe {state next : WriterProtocolState}
    {event : WriterEvent} (stepped : state.step event = some next) : next.Safe := by
  cases event with
  | lock =>
      simp only [WriterProtocolState.step] at stepped
      split at stepped
      · simp at stepped
      · simp only [Option.some.injEq] at stepped
        subst next
        intro unlocked
        simp_all [WriterProtocolState.Safe]
  | append database =>
      simp only [WriterProtocolState.step] at stepped
      split at stepped
      · simp only [Option.some.injEq] at stepped
        subst next
        intro unlocked
        simp_all [WriterProtocolState.Safe]
      · simp at stepped
  | sync =>
      simp only [WriterProtocolState.step] at stepped
      split at stepped
      · simp only [Option.some.injEq] at stepped
        subst next
        intro unlocked
        simp_all [WriterProtocolState.Safe]
      · simp at stepped
  | unlock =>
      simp only [WriterProtocolState.step] at stepped
      split at stepped
      · simp only [Option.some.injEq] at stepped
        subst next
        simp_all [WriterProtocolState.Safe]
      · simp at stepped

def runWriterProtocol : WriterProtocolState → List WriterEvent → Option WriterProtocolState
  | state, [] => some state
  | state, event :: events => do
      runWriterProtocol (← state.step event) events

theorem runWriterProtocol_preserves_safe {state final : WriterProtocolState}
    {events : List WriterEvent} (safe : state.Safe)
    (ran : runWriterProtocol state events = some final) : final.Safe := by
  induction events generalizing state with
  | nil =>
      simp only [runWriterProtocol, Option.some.injEq] at ran
      simpa [ran] using safe
  | cons event events induction =>
      simp only [runWriterProtocol] at ran
      cases stepped : state.step event with
      | none => simp [stepped] at ran
      | some next =>
          simp only [stepped, Option.bind_some] at ran
          exact induction (state.step_preserves_safe stepped) ran

def writerProtocol (next : Core.Database) : List WriterEvent :=
  [.lock, .append next, .sync, .unlock]

/-- The intended writer protocol completes with the lock released only after
the new database is durable and visible. -/
theorem writerProtocol_completes (wal : WAL) (next : Core.Database) :
    runWriterProtocol { wal := wal, lockHeld := false } (writerProtocol next) =
      some { wal := wal.commit next, lockHeld := false } := by
  simp [writerProtocol, runWriterProtocol, WriterProtocolState.step,
    WAL.commit, WAL.appendPending, WAL.sync]

abbrev TxnId := Nat

structure Interval where
  beginTick : Nat
  endTick : Nat

def Interval.Valid (interval : Interval) : Prop :=
  interval.beginTick < interval.endTick

def Interval.Overlaps (left right : Interval) : Prop :=
  left.beginTick < right.endTick ∧ right.beginTick < left.endTick

structure ReaderTxn where
  id : TxnId
  lifetime : Interval

structure WriterTxn where
  id : TxnId
  lifetime : Interval
  next : Core.Database

/-- Raw schedules deliberately admit multiple writers, so the single-writer
restriction and the lost-update rejection theorem are substantive. -/
structure Schedule where
  initial : WAL
  writers : List WriterTxn
  readers : List ReaderTxn

/-- Accepted Tier 2 histories have zero or one writer, valid transaction
intervals, and globally unique transaction ids. -/
def Accepts (schedule : Schedule) : Prop :=
  (schedule.writers = [] ∨ ∃ writer, schedule.writers = [writer]) ∧
  (∀ writer ∈ schedule.writers, writer.lifetime.Valid) ∧
  (∀ reader ∈ schedule.readers, reader.lifetime.Valid) ∧
  (schedule.writers.map WriterTxn.id ++ schedule.readers.map ReaderTxn.id).Nodup

/-- A raw timed schedule is serial only if no reader interval overlaps a
writer interval.  (Read/read overlap is observationally harmless.) -/
def Schedule.Serial (schedule : Schedule) : Prop :=
  ∀ writer ∈ schedule.writers, ∀ reader ∈ schedule.readers,
    ¬writer.lifetime.Overlaps reader.lifetime

/-- Outcomes expose the final committed database and reader observations as a
relation, so caller completion order is not confused with serialization order. -/
structure Outcome where
  final : Core.Database
  observed : TxnId → Core.Database → Prop

@[ext]
theorem Outcome.ext {left right : Outcome}
    (final : left.final = right.final)
    (observed : left.observed = right.observed) : left = right := by
  cases left
  cases right
  simp_all

/-- Execute the abstract timed schedule.  More than one writer is rejected.
A reader beginning before the one writer's commit tick retains the old visible
value; a reader beginning at or after it sees the published WAL frame. -/
def result (schedule : Schedule) : Option Outcome :=
  match schedule.writers with
  | [] => some {
      final := schedule.initial.visible
      observed := fun id database =>
        ∃ reader ∈ schedule.readers,
          reader.id = id ∧ database = schedule.initial.visible }
  | [writer] =>
      let committed := schedule.initial.commit writer.next
      some {
        final := committed.visible
        observed := fun id database =>
          ∃ reader ∈ schedule.readers, reader.id = id ∧
            database = if reader.lifetime.beginTick < writer.lifetime.endTick then
              schedule.initial.visible
            else committed.visible }
  | _ => none

/-- A serial execution has a reader phase, an optional atomic writer, and a
second reader phase.  Interleaving is unrepresentable in this type. -/
structure SerialExecution where
  initial : WAL
  beforeWriter : List ReaderTxn
  writer : Option WriterTxn
  afterWriter : List ReaderTxn

/-- The remaining well-formedness obligations for a serial execution. -/
def SerialExecution.WellFormed (serial : SerialExecution) : Prop :=
  (∀ reader ∈ serial.beforeWriter ++ serial.afterWriter, reader.lifetime.Valid) ∧
  match serial.writer with
  | none => True
  | some writer => writer.lifetime.Valid

def serialResult (serial : SerialExecution) : Outcome :=
  let old := serial.initial.visible
  let new := match serial.writer with
    | none => old
    | some writer => (serial.initial.commit writer.next).visible
  {
    final := new
    observed := fun id database =>
      (∃ reader ∈ serial.beforeWriter,
        reader.id = id ∧ database = old) ∨
      (∃ reader ∈ serial.afterWriter,
        reader.id = id ∧ database = new)
  }

/-- Construct the serial order selected by MVCC: readers whose snapshots began
before the commit serialize before the writer; all others serialize after it. -/
def serialize (schedule : Schedule) : SerialExecution :=
  match schedule.writers with
  | [writer] => {
      initial := schedule.initial
      beforeWriter := schedule.readers.filter
        (fun reader => reader.lifetime.beginTick < writer.lifetime.endTick)
      writer := some writer
      afterWriter := schedule.readers.filter
        (fun reader => ¬reader.lifetime.beginTick < writer.lifetime.endTick) }
  | _ => {
      initial := schedule.initial
      beforeWriter := schedule.readers
      writer := none
      afterWriter := [] }

theorem serialize_wellFormed (schedule : Schedule) (accepted : Accepts schedule) :
    (serialize schedule).WellFormed := by
  rcases accepted with ⟨writerCount, writersValid, readersValid, _⟩
  rcases writerCount with empty | ⟨writer, singleton⟩
  · simpa [serialize, empty, SerialExecution.WellFormed] using readersValid
  · simp only [serialize, singleton, SerialExecution.WellFormed]
    constructor
    · intro reader membership
      simp only [List.mem_append, List.mem_filter] at membership
      rcases membership with ⟨membership, _⟩ | ⟨membership, _⟩
      · exact readersValid reader membership
      · exact readersValid reader membership
    · apply writersValid writer
      rw [singleton]
      simp

private theorem result_eq_serialResult_single (schedule : Schedule) (writer : WriterTxn)
    (writers : schedule.writers = [writer]) :
    result schedule = some (serialResult (serialize schedule)) := by
  simp only [result, writers, serialize]
  apply congrArg some
  apply Outcome.ext
  · exact WAL.commit_publishes schedule.initial writer.next
  · funext id database
    apply propext
    simp only [result, serialize, serialResult, List.mem_filter, true_and]
    constructor
    · rintro ⟨reader, membership, idEq, databaseEq⟩
      by_cases before : reader.lifetime.beginTick < writer.lifetime.endTick
      · have selected : decide (reader.lifetime.beginTick < writer.lifetime.endTick) = true :=
          by simp [before]
        exact Or.inl ⟨reader, ⟨membership, selected⟩, idEq,
          by simpa [before] using databaseEq⟩
      · have selected : decide (¬reader.lifetime.beginTick < writer.lifetime.endTick) = true :=
          by simp [before]
        exact Or.inr ⟨reader, ⟨membership, selected⟩, idEq,
          by simpa [before, WAL.commit_publishes] using databaseEq⟩
    · rintro (⟨reader, ⟨membership, before⟩, idEq, databaseEq⟩ |
        ⟨reader, ⟨membership, after⟩, idEq, databaseEq⟩)
      · have beforeProp : reader.lifetime.beginTick < writer.lifetime.endTick := by
          simpa using before
        exact ⟨reader, membership, idEq, by simpa [beforeProp] using databaseEq⟩
      · have afterProp : ¬reader.lifetime.beginTick < writer.lifetime.endTick := by
          simpa using after
        exact ⟨reader, membership, idEq,
          by simpa [afterProp, WAL.commit_publishes] using databaseEq⟩

private theorem result_eq_serialResult_empty (schedule : Schedule)
    (writers : schedule.writers = []) :
    result schedule = some (serialResult (serialize schedule)) := by
  simp only [result, writers, serialize]
  apply congrArg some
  apply Outcome.ext
  · rfl
  · funext id database
    apply propext
    simp [result, serialize, serialResult]

/-- Every history admitted by the one-writer protocol has an observationally
equivalent serial execution.  The equality covers both the final database and
all reader snapshots, not only the final writer state. -/
theorem accepted_schedules_are_serializable (schedule : Schedule)
    (accepted : Accepts schedule) :
    ∃ serial, serial.WellFormed ∧ result schedule = some (serialResult serial) := by
  refine ⟨serialize schedule, serialize_wellFormed schedule accepted, ?_⟩
  rcases accepted.1 with writers | ⟨writer, writers⟩
  · exact result_eq_serialResult_empty schedule writers
  · exact result_eq_serialResult_single schedule writer writers

def interleavedExample : Schedule := {
  initial := { main := Core.Database.empty }
  writers := [{
    id := 1
    lifetime := { beginTick := 2, endTick := 4 }
    next := Core.Database.empty }]
  readers := [{ id := 2, lifetime := { beginTick := 1, endTick := 5 } }]
}

/-- The accepted language is not secretly restricted to serial histories: a
reader may span the writer's entire commit interval. -/
theorem some_nontrivial_interleaving_is_accepted :
    Accepts interleavedExample ∧ ¬interleavedExample.Serial := by
  simp [Accepts, interleavedExample, Schedule.Serial, Interval.Valid,
    Interval.Overlaps]

def lostUpdateExample : Schedule := {
  initial := { main := Core.Database.empty }
  writers := [
    { id := 1
      lifetime := { beginTick := 1, endTick := 4 }
      next := Core.Database.empty },
    { id := 2
      lifetime := { beginTick := 2, endTick := 5 }
      next := Core.Database.empty }]
  readers := []
}

/-- Two writers based on the same old snapshot are expressible as a raw
schedule but rejected by the accepted protocol. -/
theorem lost_update_schedule_is_rejected : ¬Accepts lostUpdateExample := by
  simp [Accepts, lostUpdateExample]

end WALConcurrency

end SQLeanite
