import SQLeanite.CoreSQLGrammar.LiteralSyntax

namespace SQLeanite
namespace CoreSQL

private theorem joinComparisonOperands_of_success {context : JoinContext}
    {operation : BinaryOp}
    (allowed : operation = .eq ∨ operation = .ne ∨ operation = .lt ∨
      operation = .le ∨ operation = .gt ∨ operation = .ge ∨ operation = .is ∨ operation = .isNot)
    (constructor : CoreJoin.Operand → CoreJoin.Operand → CoreJoin.Predicate)
    {left right : Expr} {predicate : CoreJoin.Predicate}
    (success : joinComparison context constructor left right = .ok predicate) :
    JoinPredicateSyntax (.binary operation left right) := by
  unfold joinComparison at success
  cases kind : SQLite.ExprCollation.require (SQLite.ExprCollation.binaryKind? left right) with
  | error message => simp [kind, bind, Except.bind] at success
  | ok collation =>
      cases leftResult : joinOperand context left with
      | error message =>
          simp [kind, leftResult, Seq.seq, bind, Functor.map, Except.bind, Except.map] at success
      | ok leftOperand =>
          cases rightResult : joinOperand context right with
          | error message =>
              simp [kind, leftResult, rightResult, Seq.seq, bind, Functor.map, Except.bind,
                Except.map] at success
          | ok rightOperand =>
              exact .comparison operation allowed
                (joinOperandSyntax_of_success leftResult)
                (joinOperandSyntax_of_success rightResult)

private theorem joinIsComparisonSyntax_of_success {context : JoinContext}
    {negated : Bool} {left right : Expr} {predicate : CoreJoin.Predicate}
    (success : joinIsComparison context negated left right = .ok predicate) :
    JoinPredicateSyntax (.binary (if negated then .isNot else .is) left right) := by
  cases keyword : SQLite.Scalar.isTruthKeyword? right with
  | some expected =>
      cases translated : joinOperand context left with
      | error message => simp [joinIsComparison, keyword, translated, bind, Except.bind] at success
      | ok operand => exact .isTruth negated expected (joinOperandSyntax_of_success translated) keyword
  | none =>
      cases translated : joinComparison context CoreJoin.Predicate.isEqual left right with
      | error message => simp [joinIsComparison, keyword, translated, bind, Except.bind] at success
      | ok operand =>
          exact joinComparisonOperands_of_success (by cases negated <;> simp) _ translated

private theorem joinTruthSyntax_of_success {context : JoinContext} {expression : Expr}
    {predicate : CoreJoin.Predicate}
    (success : CoreJoin.Predicate.truthy <$> joinOperand context expression = .ok predicate) :
    JoinPredicateSyntax expression := by
  cases translated : joinOperand context expression with
  | error message => simp [translated, Functor.map, Except.map] at success
  | ok operand => exact .truthy (joinOperandSyntax_of_success translated)

theorem joinPredicateRawSyntax_of_success {context : JoinContext} {expression : Expr}
    {predicate : CoreJoin.Predicate}
    (success : joinPredicateRaw context expression = .ok predicate) :
    JoinPredicateSyntax expression := by
  cases expression with
  | inList argument values negated affinity => exact joinInListSyntax_of_success success
  | binary operation left right =>
      cases operation with
      | is => exact joinIsComparisonSyntax_of_success success
      | isNot => exact joinIsComparisonSyntax_of_success success
      | eq => exact joinComparisonOperands_of_success (by simp) _ success
      | ne => exact joinComparisonOperands_of_success (by simp) _ success
      | lt => exact joinComparisonOperands_of_success (by simp) _ success
      | le => exact joinComparisonOperands_of_success (by simp) _ success
      | gt => exact joinComparisonOperands_of_success (by simp) _ success
      | ge => exact joinComparisonOperands_of_success (by simp) _ success
      | and =>
          change CoreJoin.Predicate.and <$> joinPredicateRaw context left <*>
            joinPredicateRaw context right = Except.ok predicate at success
          cases leftResult : joinPredicateRaw context left with
          | error message =>
              rw [leftResult] at success
              change Except.error message = Except.ok predicate at success
              contradiction
          | ok leftPredicate =>
              cases rightResult : joinPredicateRaw context right with
              | error message =>
                  rw [leftResult, rightResult] at success
                  change Except.error message = Except.ok predicate at success
                  contradiction
              | ok rightPredicate =>
                  exact .and (joinPredicateRawSyntax_of_success leftResult)
                    (joinPredicateRawSyntax_of_success rightResult)
      | or =>
          change CoreJoin.Predicate.or <$> joinPredicateRaw context left <*>
            joinPredicateRaw context right = Except.ok predicate at success
          cases leftResult : joinPredicateRaw context left with
          | error message =>
              rw [leftResult] at success
              change Except.error message = Except.ok predicate at success
              contradiction
          | ok leftPredicate =>
              cases rightResult : joinPredicateRaw context right with
              | error message =>
                  rw [leftResult, rightResult] at success
                  change Except.error message = Except.ok predicate at success
                  contradiction
              | ok rightPredicate =>
                  exact .or (joinPredicateRawSyntax_of_success leftResult)
                    (joinPredicateRawSyntax_of_success rightResult)
      | add | sub | mul | div | mod | like | glob | «match» |
          concat | bitAnd | bitOr | shiftLeft | shiftRight | arrow | arrowText =>
          exact joinTruthSyntax_of_success (by simpa only [joinPredicateRaw] using success)
  | isNull operand negated =>
      cases negated with
      | false =>
        change CoreJoin.Predicate.isNull <$> joinOperand context operand =
          Except.ok predicate at success
        cases operandResult : joinOperand context operand with
        | error message =>
            rw [operandResult] at success
            change Except.error message = Except.ok predicate at success
            contradiction
        | ok translated =>
            exact .isNull false (joinOperandSyntax_of_success operandResult)
      | true =>
        change CoreJoin.Predicate.not <$> (CoreJoin.Predicate.isNull <$>
          joinOperand context operand) = Except.ok predicate at success
        cases operandResult : joinOperand context operand with
        | error message =>
            rw [operandResult] at success
            change Except.error message = Except.ok predicate at success
            contradiction
        | ok translated =>
            exact .isNull true (joinOperandSyntax_of_success operandResult)
  | unary operation argument =>
      cases operation with
      | not =>
          change CoreJoin.Predicate.not <$> joinPredicateRaw context argument =
            Except.ok predicate at success
          cases translated : joinPredicateRaw context argument with
          | error message =>
              rw [translated] at success
              change Except.error message = Except.ok predicate at success
              contradiction
          | ok nested => exact .not (joinPredicateRawSyntax_of_success translated)
      | plus | neg | bitNot => exact joinTruthSyntax_of_success (by simpa only [joinPredicateRaw] using success)
  | literal | column | star | call | collate | case_ | scalarSubquery |
      inSubquery | existsSubquery => exact joinTruthSyntax_of_success (by simpa only [joinPredicateRaw] using success)
termination_by expression.height
decreasing_by all_goals simp_all [Expr.height] <;> omega

theorem joinPredicateSyntax_of_success {context : JoinContext} {expression : Expr}
    {predicate : CoreJoin.Predicate} {outer : Bool}
    (success : joinPredicate context expression outer = .ok predicate) :
    JoinPredicateSyntax expression := by
  apply JoinPredicateSyntax.prepared context expression
  cases classified : SQLite.StaticCondition.classify outer
      (SQLite.Scalar.prepare (joinBindNames context expression)) with
  | none =>
      exact joinPredicateRawSyntax_of_success (by simpa [joinPredicate, classified] using success)
  | some truth =>
      cases checked : joinStaticAdmitted context (SQLite.Scalar.prepare (joinBindNames context expression)) outer with
      | false => simp [joinPredicate, classified, checked, unsupported, bind, Except.bind] at success
      | true => exact .static context outer truth checked classified

end CoreSQL

end SQLeanite
