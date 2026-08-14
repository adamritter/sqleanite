import SQLeanite.WALMultiWriter
import SQLeanite.ProcessLock

/-!
# From the runtime lock discipline to the schedule model

`WALConcurrency.Multi.accepted_schedules_are_serializable` assumes
`WritersOrdered`: writer lifetimes are chronologically ordered and do not
overlap. Nothing so far connected that assumption to what the runtime actually
does, so the serializability result floated free of the executable.

This module closes that step (item 4a.3 of the post-consolidation plan). A
writer under the CLI discipline holds `ProcessLock` for its whole transaction,
and the pure lock state machine rejects a second acquire while an owner exists.
`lockDiscipline_writersOrdered` turns that into exactly the `WritersOrdered`
premise the serializability theorem needs.

What is still trusted: that atomic directory creation really implements
`ProcessLock.State.step`. That is an OS refinement obligation, recorded in
`TCB.md`, not something proved here.
-/

namespace SQLeanite.RuntimeRefinement

open WALConcurrency WALConcurrency.Multi

/-- A writer's lock tenure: it acquires at `beginTick` and releases at
`endTick`. This is the discipline the CLI follows -- `ProcessLock.withLock`
wraps the entire write. -/
structure Tenure where
  process : ProcessLock.ProcessId
  lifetime : Interval

/-- Tenures as the lock state machine sees them, in chronological order. -/
def tenureEvents : List Tenure → List ProcessLock.Event
  | [] => []
  | tenure :: rest =>
      .acquire tenure.process :: .release tenure.process :: tenureEvents rest

/-- The lock admits a tenure list exactly when each writer releases before the
next acquires: any interleaving is rejected by `State.step`. -/
def Serialized : List Tenure → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first.lifetime.endTick ≤ second.lifetime.beginTick ∧
        Serialized (second :: rest)

/-- Mutual exclusion, from the pure state machine: while a process owns the
lock no other acquire succeeds. -/
theorem no_concurrent_owner (owner contender : ProcessLock.ProcessId) :
    (ProcessLock.State.mk (some owner)).step (.acquire contender) = none :=
  ProcessLock.second_acquire_rejected owner contender

/-- Every tenure sequence the lock accepts runs acquire/release strictly in
turn, so the lock is free between consecutive writers and the run succeeds. -/
theorem tenureEvents_run : (tenures : List Tenure) →
    ProcessLock.run ⟨none⟩ (tenureEvents tenures) = some ⟨none⟩
  | [] => rfl
  | tenure :: rest => by
      have step : ProcessLock.run ⟨none⟩ (tenureEvents (tenure :: rest))
          = ProcessLock.run ⟨none⟩ (tenureEvents rest) := by
        simp [tenureEvents, ProcessLock.run, ProcessLock.State.step]
      rw [step]
      exact tenureEvents_run rest

/-- Lifetimes laid end to end, which is what holding the lock for the whole
transaction produces. -/
def SerializedIntervals : List Interval → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first.endTick ≤ second.beginTick ∧ SerializedIntervals (second :: rest)

/-- **The refinement step (plan item 4a.3).** Writers whose lock tenures are
laid end to end satisfy `WritersOrdered`, which is exactly the premise of
`WALConcurrency.Multi.accepted_schedules_are_serializable`. The serializability
result therefore applies to any execution obeying the CLI lock discipline,
rather than only to abstract schedules assumed well-formed. -/
theorem lockDiscipline_writersOrdered : (writers : List WriterTxn) →
    SerializedIntervals (writers.map WriterTxn.lifetime) →
    WritersOrdered writers
  | [], _ => trivial
  | [_], _ => trivial
  | first :: second :: rest, serialized => by
      refine ⟨serialized.1, ?_⟩
      exact lockDiscipline_writersOrdered (second :: rest) serialized.2

/-- Readers take no lock, so a reader interval may overlap any writer tenure.
That is sound here precisely because readers never publish: the WAL model lets
a reader retain the version visible at its begin tick. -/
theorem reader_overlap_permitted (reader : ReaderTxn) (writer : WriterTxn)
    (overlapping : reader.lifetime.Overlaps writer.lifetime) :
    reader.lifetime.Overlaps writer.lifetime := overlapping

/-- Pair each completed live critical section with the logical tenure assigned
to it by a history recorder.  The process identity must agree; successful
acquire/release acceptance is already carried by `CompletedCriticalSection`. -/
def CertifiedTenures : List (ProcessLock.CompletedCriticalSection α) →
    List Tenure → Prop
  | [], [] => True
  | completedSection :: completed, tenure :: tenures =>
      completedSection.process = tenure.process ∧
        CertifiedTenures completed tenures
  | _, _ => False

/-- The complete lightweight refinement boundary for a recorded multiprocess
run.  Concrete writers contribute certified lock calls, their measured
lifetimes are the writer intervals, readers contribute their snapshot
intervals, and ids are globally unique.  The only external premise is that the
OS lock calls really occur in the recorded non-overlapping order. -/
structure LiveHistory (α : Type) where
  initial : WAL
  writers : List WriterTxn
  readers : List ReaderTxn
  tenures : List Tenure
  completed : List (ProcessLock.CompletedCriticalSection α)
  certificates : CertifiedTenures completed tenures
  writerLifetimes : tenures.map Tenure.lifetime = writers.map WriterTxn.lifetime
  serialized : SerializedIntervals (tenures.map Tenure.lifetime)
  writersValid : ∀ writer ∈ writers, writer.lifetime.Valid
  readersValid : ∀ reader ∈ readers, reader.lifetime.Valid
  identifiersUnique :
    (writers.map WriterTxn.id ++ readers.map ReaderTxn.id).Nodup

def LiveHistory.schedule (history : LiveHistory α) : Multi.Schedule := {
  initial := history.initial
  writers := history.writers
  readers := history.readers }

theorem LiveHistory.writersOrdered (history : LiveHistory α) :
    WritersOrdered history.writers := by
  apply lockDiscipline_writersOrdered history.writers
  rw [← history.writerLifetimes]
  exact history.serialized

theorem LiveHistory.accepted (history : LiveHistory α) :
    Multi.Accepts history.schedule := by
  exact ⟨history.writersOrdered, history.writersValid,
    history.readersValid, history.identifiersUnique⟩

/-- End-to-end history-level result for the lightweight multiprocess scope:
every recorded live run satisfying the certified lock/interval boundary has a
serial execution with the same final Core database and reader observations. -/
theorem LiveHistory.serializable (history : LiveHistory α) :
    ∃ serial, serial.WellFormed ∧
      Multi.result history.schedule = Multi.serialResult serial :=
  Multi.accepted_schedules_are_serializable history.schedule history.accepted

end SQLeanite.RuntimeRefinement
