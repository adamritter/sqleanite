import SQLeanite.CoreTriggerProgram.Scope

namespace SQLeanite.CoreTriggerProgram

/-- A later source or constraint failure must retain connection effects from
actual earlier points, even when logical ABORT restores the complete statement.
The recognized VALUES coroutine uses the same rules. Other SELECTs retain
their dedicated checked input plans, including register scans and empty setup. -/
def requiresInputEffects : Statement → Bool
  | .insert _ _ rows .. => rows.size > 1
  | .insertSelect _ _ query .. => (streamingInput query).isSome
  | _ => false

theorem requiresInputEffects_single (target : String) (columns : Option (Array String))
    (row : Array Expr) (action : ConflictAction) (outputs : Array ResultColumn) :
    requiresInputEffects (.insert target columns #[row] action outputs) = false := by
  simp [requiresInputEffects]

theorem requiresInputEffects_select (target : String) (columns : Option (Array String))
    (query : Select) (action : ConflictAction) (outputs : Array ResultColumn)
    (rows : Array (Array Expr)) (streamed : streamingInput query = some rows) :
    requiresInputEffects (.insertSelect target columns query action outputs) = true := by
  simp [requiresInputEffects, streamed]

end SQLeanite.CoreTriggerProgram
