namespace SQLeanite
namespace GroupCommit

/-!
# Pure group-commit and full-image write-absorption model

The model is generic, but the live database instantiation uses
`Core.Database`. Pending states are newest-first. A single durability barrier
publishes the entire batch atomically.
-/

structure WAL (State : Type) where
  main : State
  durableFrames : List State := []
  pendingFrames : List State := []

def WAL.visible (wal : WAL State) : State :=
  wal.durableFrames.head?.getD wal.main

def WAL.appendPending (wal : WAL State) (next : State) : WAL State :=
  { wal with pendingFrames := next :: wal.pendingFrames }

def WAL.sync (wal : WAL State) : WAL State :=
  match wal.pendingFrames with
  | [] => wal
  | pending =>
      { wal with
        durableFrames := pending ++ wal.durableFrames
        pendingFrames := [] }

def WAL.commitOne (wal : WAL State) (next : State) : WAL State :=
  (wal.appendPending next).sync

def WAL.commitSequential : WAL State → List State → WAL State
  | wal, [] => wal
  | wal, next :: rest => commitSequential (wal.commitOne next) rest

/-- The optimized result of staging the whole chronological batch and crossing
one barrier. -/
def WAL.commitGroup (wal : WAL State) : List State → WAL State
  | [] => wal
  | states =>
      { wal with
        durableFrames := states.reverse ++ wal.pendingFrames ++ wal.durableFrames
        pendingFrames := [] }

def newest? (states : List State) : Option State :=
  states.reverse.head?

theorem WAL.commitGroup_visible_eq_newest (wal : WAL State)
    (states : List State) :
    (wal.commitGroup states).visible = (newest? states).getD wal.visible := by
  cases states with
  | nil => rfl
  | cons state states =>
      simp [WAL.commitGroup, WAL.visible, newest?, List.append_assoc]

/-- One barrier for a batch is state-for-state equivalent to committing every
full-image frame separately in the supplied serial order. -/
theorem WAL.commitGroup_eq_commitSequential (wal : WAL State) :
    ∀ states, wal.commitGroup states = wal.commitSequential states
  | [] => rfl
  | [state] => by
      simp [WAL.commitGroup, WAL.commitSequential, WAL.commitOne,
        WAL.appendPending, WAL.sync]
  | first :: second :: rest => by
      rw [WAL.commitSequential]
      rw [← WAL.commitGroup_eq_commitSequential (wal.commitOne first)
        (second :: rest)]
      simp [WAL.commitGroup, WAL.commitOne, WAL.appendPending, WAL.sync,
        List.reverse_cons, List.append_assoc]

theorem WAL.commitGroup_visible (wal : WAL State) (states : List State) :
    (wal.commitGroup states).visible = (wal.commitSequential states).visible := by
  rw [wal.commitGroup_eq_commitSequential]

/-- For full-image frames, only the newest pending image affects the state
visible after sync. Older pending images may be absorbed when history itself is
not an observable API. -/
def WAL.absorbPending (wal : WAL State) : WAL State :=
  match wal.pendingFrames with
  | [] => wal
  | newest :: _ => { wal with pendingFrames := [newest] }

theorem WAL.sync_absorbPending_visible (wal : WAL State) :
    wal.absorbPending.sync.visible = wal.sync.visible := by
  cases wal with
  | mk main durableFrames pendingFrames =>
      cases pendingFrames <;> simp [WAL.absorbPending, WAL.sync, WAL.visible]

inductive Event (State : Type) where
  | append (next : State)
  | sync

def groupProtocol : List State → List (Event State)
  | [] => [.sync]
  | state :: states => .append state :: groupProtocol states

def sequentialProtocol : List State → List (Event State)
  | [] => []
  | state :: states => .append state :: .sync :: sequentialProtocol states

def syncCount : List (Event State) → Nat
  | [] => 0
  | .append _ :: events => syncCount events
  | .sync :: events => syncCount events + 1

theorem syncCount_groupProtocol (states : List State) :
    syncCount (groupProtocol states) = 1 := by
  induction states with
  | nil => rfl
  | cons state states induction =>
      simp [groupProtocol, syncCount, induction]

theorem syncCount_sequentialProtocol (states : List State) :
    syncCount (sequentialProtocol states) = states.length := by
  induction states with
  | nil => rfl
  | cons state states induction =>
      simp [sequentialProtocol, syncCount, induction]

end GroupCommit
end SQLeanite
