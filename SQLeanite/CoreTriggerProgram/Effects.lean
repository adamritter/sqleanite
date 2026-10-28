import SQLeanite.CoreTriggerProgram.Binding
import Init.Control.EState

namespace SQLeanite.CoreTriggerProgram

/-- Runtime state survives an exception. Logical data rollback is an explicit
outer-statement operation, separate from connection counter/frame effects. -/
structure ExecutionContext where
  state : Core.State
  running : Bool := false

abbrev ExecutionM := EStateM String ExecutionContext
abbrev EffectExecutor := Core.State → Statement → String → ExecutionM (Core.State × List Core.Result)
abbrev ScopedEffectExecutor := List CoreScalarQuery.Frame → EffectExecutor

instance : MonadLift (Except String) ExecutionM where
  monadLift action := fun context => match action with
    | .ok value => .ok value context
    | .error message => .error message context

namespace Execution

def remember (state : Core.State) : ExecutionM Unit :=
  modify fun context => { context with state }

def current : ExecutionM Core.State := do return (← get).state

def start : ExecutionM Unit := modify fun context => { context with running := true }

/-- ABORT restores the original statement data/context while retaining actual
connection effects. Preparation failures keep the preceding changes() count. -/
def abort (original : Core.State) (context : ExecutionContext) : Core.State :=
  { original with
    lastChanges := if context.running then 0 else original.lastChanges
    totalChanges := context.state.totalChanges
    lastInsertRowid := context.state.lastInsertRowid }

theorem abort_database (original : Core.State) (context : ExecutionContext) :
    (abort original context).database = original.database := rfl

theorem abort_totalChanges (original : Core.State) (context : ExecutionContext) :
    (abort original context).totalChanges = context.state.totalChanges := rfl

end Execution

inductive ExecutionOutcome where
  | success (state : Core.State) (results : List Core.Result)
  | failure (state : Core.State) (message : String)

def ExecutionOutcome.toExcept : ExecutionOutcome → Except String (Core.State × List Core.Result)
  | .success state results => .ok (state,results)
  | .failure _ message => .error message

end SQLeanite.CoreTriggerProgram
