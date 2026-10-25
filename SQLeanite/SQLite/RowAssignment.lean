import SQLeanite.Syntax

/-! Checked lowering of a scalar-expression row assignment. A width mismatch
must fail before zip can silently discard a target or a value. Subquery row
assignments require a separate query lowering and are not handled here. -/
namespace SQLeanite.SQLite.RowAssignment

def bind (names : List String) (values : List Expr) : Except String (List (String × Expr)) :=
  if names.length = values.length then .ok (names.zip values)
  else .error s!"{names.length} columns assigned {values.length} values"

theorem bind_exact {names : List String} {values : List Expr} {assignments : List (String × Expr)}
    (success : bind names values = .ok assignments) :
    names.length = values.length ∧ assignments = names.zip values := by
  unfold bind at success
  split at success
  next same => exact ⟨same, (Except.ok.inj success).symm⟩
  next => contradiction

theorem bind_length {names : List String} {values : List Expr} {assignments : List (String × Expr)}
    (success : bind names values = .ok assignments) : assignments.length = names.length := by
  obtain ⟨same, rfl⟩ := bind_exact success
  simp [List.length_zip, same]

end SQLeanite.SQLite.RowAssignment
