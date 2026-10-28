import SQLeanite.RelationalAlgebra.OfListWhereRows

namespace SQLeanite
namespace RelationalAlgebra

/-- A predicate depending only on the preserved side of a left outer join may
be pushed below the join.  No corresponding theorem is stated for the nullable
right side: that rewrite is unsound in general under SQL three-valued logic. -/
theorem selectLeftOuterLeft_eval (decEq : DecidableEq Right)
    (domain : Domain Right) (nullRight : Right)
    (joinPredicate : Left → Right → Truth) (predicate : Left → Truth)
    (left : Expr Left) (right : Expr Right) :
    eval (.select (fun row : Left × Right => predicate row.1)
        (.leftOuter decEq domain nullRight joinPredicate left right)) =
      eval (.leftOuter decEq domain nullRight joinPredicate
        (.select predicate left) right) := by
  apply KRelation.Relation.ext
  intro row
  cases predicateResult : predicate row.1 <;>
    simp [eval, KRelation.select, leftOuterRelation, hasMatch,
      predicateResult]

theorem leftOuter_unmatched [DecidableEq Right] (domain : Domain Right)
    (nullRight : Right) (predicate : Left → Right → Truth)
    (left : Relation Left) (right : Relation Right) (row : Left)
    (none : hasMatch domain predicate right row = false) :
    leftOuterRelation domain nullRight predicate left right (row, nullRight) =
      left row := by
  simp [leftOuterRelation, none]

theorem leftOuter_matched [DecidableEq Right] (domain : Domain Right)
    (nullRight : Right) (predicate : Left → Right → Truth)
    (left : Relation Left) (right : Relation Right) (leftRow : Left)
    (rightRow : Right) (some : hasMatch domain predicate right leftRow = true)
    (predicateTrue : predicate leftRow rightRow = .true) :
    leftOuterRelation domain nullRight predicate left right
        (leftRow, rightRow) = left leftRow * right rightRow := by
  simp [leftOuterRelation, some, predicateTrue]

end RelationalAlgebra

end SQLeanite
