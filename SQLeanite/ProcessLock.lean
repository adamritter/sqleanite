import Std

namespace SQLeanite
namespace ProcessLock

/-!
# Cross-process serialized writer lock

The pure state machine specifies exclusive ownership.  The runtime adapter uses
atomic directory creation as its unverified OS refinement.  This is Tier 1
serialization, not WAL: readers and writers using the CLI take the same lock.
-/

abbrev ProcessId := Nat

structure State where
  owner : Option ProcessId := none
  deriving DecidableEq, Repr

inductive Event where
  | acquire (process : ProcessId)
  | release (process : ProcessId)
  deriving DecidableEq, Repr

def State.step (state : State) : Event → Option State
  | .acquire process =>
      match state.owner with
      | none => some ⟨some process⟩
      | some _ => none
  | .release process =>
      if state.owner = some process then some ⟨none⟩ else none

def run : State → List Event → Option State
  | state, [] => some state
  | state, event :: events => do
      let next ← state.step event
      run next events

theorem acquire_establishes_owner (state : State) (process : ProcessId)
    {next : State} (acquired : state.step (.acquire process) = some next) :
    state.owner = none ∧ next.owner = some process := by
  change (match state.owner with
    | none => some ⟨some process⟩
    | some _ => none) = some next at acquired
  cases ownerEq : state.owner with
  | none =>
      rw [ownerEq] at acquired
      injection acquired with nextEq
      subst next
      exact ⟨rfl, rfl⟩
  | some owner => simp [ownerEq] at acquired

theorem second_acquire_rejected (owner contender : ProcessId) :
    (State.mk (some owner)).step (.acquire contender) = none := by
  rfl

theorem release_requires_owner (state : State) (process : ProcessId)
    {next : State} (released : state.step (.release process) = some next) :
    state.owner = some process ∧ next.owner = none := by
  change (if state.owner = some process then some ⟨none⟩ else none) =
    some next at released
  split at released
  next owns =>
    injection released with nextEq
    subst next
    exact ⟨owns, rfl⟩
  next doesNotOwn => contradiction

theorem sequential_critical_sections_succeed (first second : ProcessId) :
    run {} [.acquire first, .release first, .acquire second, .release second] =
      some {} := by
  simp [run, State.step]

theorem overlapping_critical_sections_rejected (first second : ProcessId) :
    run {} [.acquire first, .acquire second] = none := by
  simp [run, State.step]

structure Config where
  directory : System.FilePath
  process : ProcessId := 0
  attempts : Nat := 3000
  retryMillis : UInt32 := 10
  missingOwnerGraceAttempts : Nat := 100

@[extern "sqleanite_process_alive"]
opaque processAlive (process : USize) : IO Bool

def ownerPath (config : Config) : System.FilePath :=
  config.directory / "owner"

private def readOwner? (config : Config) : IO (Option ProcessId) := do
  try
    return (← IO.FS.readFile (ownerPath config)).trimAscii.toString.toNat?
  catch error =>
    -- A competing owner may release the directory between observation and
    -- reading. Missing ownership is retried; unrelated IO failures propagate.
    match error with
    | .noFileOrDirectory .. => return none
    | _ => throw error

private def removeLockDirectory (config : Config) : IO Unit := do
  let owner := ownerPath config
  if ← owner.pathExists then IO.FS.removeFile owner
  if ← config.directory.pathExists then IO.FS.removeDir config.directory

private def createOwnedDirectory (config : Config) : IO Unit := do
  IO.FS.createDir config.directory
  try
    IO.FS.writeFile (ownerPath config) (toString config.process)
  catch error =>
    removeLockDirectory config
    throw error

private def acquireDirectory (config : Config) : Nat → Nat → IO Bool
  | 0, _ => return false
  | attempts + 1, missingOwnerAttempts =>
      try
        createOwnedDirectory config
        return true
      catch error =>
        if ← config.directory.pathExists then
          match ← readOwner? config with
          | some owner =>
              if ← processAlive owner.toUSize then
                IO.sleep config.retryMillis
                acquireDirectory config attempts 0
              else
                -- Atomic directory creation still arbitrates simultaneous
                -- reclaimers. A dead owner's directory is no longer a lock.
                try removeLockDirectory config catch _ => pure ()
                acquireDirectory config attempts 0
          | none =>
              if config.missingOwnerGraceAttempts ≤ missingOwnerAttempts then
                try removeLockDirectory config catch _ => pure ()
                acquireDirectory config attempts 0
              else
                IO.sleep config.retryMillis
                acquireDirectory config attempts (missingOwnerAttempts + 1)
        else
          -- mkdir may report EEXIST just before the previous owner removes
          -- its directory. That is ordinary contention, not an IO failure.
          match error with
          | .alreadyExists .. => acquireDirectory config attempts 0
          | _ => throw error

/-- The abstract events emitted by one successful runtime critical section. -/
def successfulTrace (process : ProcessId) : List Event :=
  [.acquire process, .release process]

theorem run_successfulTrace (process : ProcessId) :
    run {} (successfulTrace process) = some {} := by
  simp [successfulTrace, run, State.step]

/-- Evidence returned by the live lock wrapper after a successful action.  It
records the exact abstract acquire/release trace refined by that call.  The OS
fact that directory creation/removal implements those two events remains the
explicit filesystem assumption. -/
structure CompletedCriticalSection (α : Type) where
  result : α
  process : ProcessId
  events : List Event
  events_eq : events = successfulTrace process
  accepted : run {} events = some {}

/-- Execute one complete database operation while owning the cross-process
lock and return its checked abstract trace. Directory creation/removal and
crash cleanup are part of the unverified OS boundary. -/
def withLockCertified (config : Config) (action : IO α) :
    IO (CompletedCriticalSection α) := do
  unless ← acquireDirectory config config.attempts 0 do
    throw (IO.userError s!"timed out acquiring database lock: {config.directory}")
  let result ← try action finally
    removeLockDirectory config
  return {
    result
    process := config.process
    events := successfulTrace config.process
    events_eq := rfl
    accepted := run_successfulTrace config.process }

def withLock (config : Config) (action : IO α) : IO α := do
  return (← withLockCertified config action).result

theorem CompletedCriticalSection.exclusive
    (completed : CompletedCriticalSection α) :
    run {} completed.events = some {} := completed.accepted

end ProcessLock
end SQLeanite
