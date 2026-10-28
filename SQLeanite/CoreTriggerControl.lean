import SQLeanite.CoreForeignKey

namespace SQLeanite.CoreTriggerControl

/-- A connection flag: unlike foreign_keys, recursive_triggers can change in
an active transaction and is not reverted by transaction/savepoint rollback. -/
def pragma (state : Core.State) (argument : Option Expr) (schema : Option String) :
    Except String (Core.State × List Core.Result) := do
  if schema.any (fun name => !["main", "temp"].contains name.toLower) then
    throw s!"unknown database {schema.getD ""}"
  match argument with
  | none =>
      let value ← SQLSurface.value (.integer (if state.recursiveTriggers then 1 else 0))
      return (state, [{ rows := [[value]] }])
  | some argument =>
      let enabled ← CoreForeignKey.boolArgument argument
      return ({ state with recursiveTriggers := enabled }, [{}])

theorem pragma_read_preserves_state (state next : Core.State) (schema : Option String)
    (results : List Core.Result) (success : pragma state none schema = .ok (next,results)) : next = state := by
  simp only [pragma] at success
  split at success
  · simp [bind, Except.bind, throw, Except.error] at success
  · cases evaluated : SQLSurface.value (.integer (if state.recursiveTriggers then 1 else 0)) with
    | error message => simp [evaluated, bind, Except.bind] at success
    | ok value =>
        simp only [evaluated, bind, Except.bind, pure, Except.pure] at success
        exact (congrArg Prod.fst (Except.ok.inj success)).symm

end SQLeanite.CoreTriggerControl
