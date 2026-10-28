import SQLeanite.CoreEngine.ChooseExtremeEqLeftOrRight

namespace SQLeanite
namespace Core

theorem execute_rollback_restores_headers {state next : State} {result : Result}
    (success : execute state .rollback = .ok (next, result)) :
    next.headers = state.transactionHeaderSnapshot.getD state.headers := by
  unfold execute at success
  cases snapshot : state.transactionSnapshot with
  | none => simp [snapshot] at success
  | some database =>
      simp only [snapshot] at success
      exact (congrArg (fun pair => pair.1.headers) (Except.ok.inj success)).symm

end Core

end SQLeanite
