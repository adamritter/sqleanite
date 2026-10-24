/-! Whole-image publication with a synced temporary file and directory barrier.
This is a conditional filesystem model, not a proof of POSIX or a host kernel.
During an unsynced rename the old or new complete directory entry may survive. -/
namespace SQLeanite.AtomicFileReplacement

inductive Request (α : Type) where
  | stage (contents : α)
  | syncTemporary
  | publish
  | syncDirectory

structure State (α : Type) where
  visible : α
  durable : α
  staged : Option α := none
  synced : Option α := none

def initial (old : α) : State α := ⟨old, old, none, none⟩

def step (state : State α) : Request α → State α
  | .stage value => { state with staged := some value, synced := none }
  | .syncTemporary => { state with synced := state.staged }
  | .publish => match state.synced with
      | none => state
      | some value => { state with visible := value }
  | .syncDirectory => { state with durable := state.visible }

def run (state : State α) (requests : List (Request α)) : State α :=
  requests.foldl step state

def plan (contents : α) : List (Request α) :=
  [.stage contents, .syncTemporary, .publish, .syncDirectory]

def CrashOutcome (state : State α) (contents : α) : Prop :=
  contents = state.durable ∨ contents = state.visible

theorem committed (old new : α) : (run (initial old) (plan new)).durable = new := rfl

theorem prefix_atomic (old new : α) (count : Nat) (contents : α)
    (crashed : CrashOutcome (run (initial old) ((plan new).take count)) contents) :
    contents = old ∨ contents = new := by
  cases count with
  | zero => simp [CrashOutcome, run, plan, initial] at crashed; exact Or.inl crashed
  | succ count =>
    cases count with
    | zero => simp [CrashOutcome, run, plan, initial, step] at crashed; exact Or.inl crashed
    | succ count =>
      cases count with
      | zero => simp [CrashOutcome, run, plan, initial, step] at crashed; exact Or.inl crashed
      | succ count =>
        cases count with
        | zero => simpa [CrashOutcome, run, plan, initial, step] using crashed
        | succ count =>
            simp [CrashOutcome, run, plan, initial, step] at crashed
            exact Or.inr crashed

end SQLeanite.AtomicFileReplacement
