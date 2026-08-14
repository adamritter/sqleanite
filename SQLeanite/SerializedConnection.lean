import SQLeanite.CoreSQL
import Std.Sync.Mutex

namespace SQLeanite

/-!
# Serialized connections

The SQL engine remains a pure transition.  `SerializedConnection` is the small
runtime shell that places one mutex around a complete transition.  The mutex
implementation is part of the executable trusted computing base; the pure
definitions below state the refinement obligation for that shell.
-/

namespace Serialization

/-- A submitted operation has a stable identifier so responses can be matched
to requests independently of the order chosen by a scheduler. -/
structure Request where
  id : Nat
  sql : String

/-- The observable response to one request in serialization order. -/
structure Completion where
  id : Nat
  outcome : Except String (List Core.Result)

/-- Run a proposed serialization order through the actual pure SQL entry
point.  This is the reference semantics for the imperative shell. -/
def runSchedule : Core.Database → List Request → Core.Database × List Completion
  | database, [] => (database, [])
  | database, request :: requests =>
      let (next, outcome) :=
        match CoreSQL.execute { database := database } request.sql with
        | .ok (state, results) => (state.database, .ok results)
        | .error message => (database, .error message)
      let (final, completions) := runSchedule next requests
      (final, { id := request.id, outcome := outcome } :: completions)

/-- Every submitted request produces exactly one completion with the same id
and in the chosen serialization order. -/
theorem runSchedule_completionIds (database : Core.Database) (requests : List Request) :
    (runSchedule database requests).2.map Completion.id = requests.map Request.id := by
  induction requests generalizing database with
  | nil => rfl
  | cons request requests induction =>
      simp [runSchedule, induction]

/-- Running a prefix and then a suffix is equivalent to running their
concatenation.  Besides being useful for future history refinement, this is a
non-definitional induction over the live engine transition. -/
theorem runSchedule_append (database : Core.Database) (first second : List Request) :
    runSchedule database (first ++ second) =
      (let prefixResult := runSchedule database first
       let suffixResult := runSchedule prefixResult.1 second
       (suffixResult.1, prefixResult.2 ++ suffixResult.2)) := by
  induction first generalizing database with
  | nil => rfl
  | cons request requests induction =>
      simp [runSchedule, induction]

/--
The contract required of any concurrent connection adapter.  `completed` is in
lock-acquisition (serialization) order, not caller join order.  A valid history
must be observationally identical to some permutation of the submitted
requests executed by `runSchedule`.
-/
def SerializationContract (initial : Core.Database) (submitted : List Request)
    (final : Core.Database) (completed : List Completion) : Prop :=
  ∃ serialOrder, serialOrder.Perm submitted ∧
    runSchedule initial serialOrder = (final, completed)

/-- The contract is satisfiable by every ordinary sequential execution.  Thus
the contract does not rule out all histories merely to make refinement easy. -/
theorem sequential_satisfies_contract (initial : Core.Database) (requests : List Request) :
    SerializationContract initial requests (runSchedule initial requests).1
      (runSchedule initial requests).2 := by
  exact ⟨requests, .refl _, rfl⟩

end Serialization

/-- A thread-safe connection in serialized mode.  The pure `Database` is the
only mutable state and the mutex is held across the whole SQL transition. -/
structure SerializedConnection where
  private state : Std.Mutex Core.Database

namespace SerializedConnection

/-- Create a serialized connection from an immutable initial database value. -/
def create (initial : Core.Database := Core.Database.empty) : BaseIO SerializedConnection := do
  return ⟨← Std.Mutex.new initial⟩

/-- Execute one SQL request while holding the connection's coarse lock.  Error
outcomes retain the exact progressed state chosen by `runSQLProgress`, On error the database is left unchanged. -/
def execute (connection : SerializedConnection) (sql : String) :
    IO (Except String (List Core.Result)) :=
  connection.state.atomically do
    let database ← get
    match CoreSQL.execute { database := database } sql with
    | .ok (state, results) => set state.database; return .ok results
    | .error message => return .error message

/-- Take an immutable snapshot while holding the same lock as writers. -/
def snapshot (connection : SerializedConnection) : IO Core.Database :=
  connection.state.atomically get

end SerializedConnection

end SQLeanite
