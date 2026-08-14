import SQLeanite.CoreSQL

namespace SQLeanite
namespace CoreSQL

/-!
# Declarative grammar for the verified Core SQL surface

`CoreSQL` is executable translation code.  This module gives its accepted AST
forms an independent, inductive description.  The propositions erase at
runtime; the accompanying theorems show that successful live translations
cannot escape the advertised grammar without breaking a proof.
-/

inductive LiteralSyntax : Expr → Prop where
  | literal (value : Value) : LiteralSyntax (.literal value)
  | plus {expression : Expr} : LiteralSyntax expression →
      LiteralSyntax (.unary .plus expression)
  | neg {expression : Expr} : LiteralSyntax expression →
      LiteralSyntax (.unary .neg expression)

theorem literalSyntax_of_success {expression : Expr} {value : Core.Value}
    (success : literal expression = .ok value) : LiteralSyntax expression := by
  cases expression with
  | literal input => exact .literal input
  | unary operation argument =>
      cases operation with
      | plus =>
          exact .plus (literalSyntax_of_success
            (by simpa [literal, SQLSurface.literal] using success))
      | neg =>
          cases decoded : SQLSurface.literal argument with
          | error message =>
              simp only [literal, SQLSurface.literal, decoded, Except.instMonad,
                Except.bind] at success
              cases success
          | ok decodedValue =>
              cases decodedValue with
              | integer integer =>
                  exact .neg (literalSyntax_of_success
                    (by simpa [literal] using decoded))
              | null | realBits | text | blob =>
                  simp only [literal, SQLSurface.literal, decoded,
                    Except.instMonad, Except.bind, SQLSurface.unsupported] at success
                  cases success
      | not | bitNot =>
          simp [literal, SQLSurface.literal, SQLSurface.unsupported] at success
  | column | star | binary | call | isNull | inList | collate | case_ |
      scalarSubquery | inSubquery | existsSubquery =>
      simp [literal, SQLSurface.literal, SQLSurface.unsupported] at success
termination_by expression.height
decreasing_by all_goals simp_all [Expr.height]

inductive PredicateSyntax : Expr → Prop where
  | columnRight (operation : BinaryOp)
      (allowed : operation = .eq ∨ operation = .ne ∨ operation = .lt ∨
        operation = .le ∨ operation = .gt ∨ operation = .ge)
      (qualifier : Option String) (name : String) (right : Expr)
      (rightLiteral : LiteralSyntax right) :
      PredicateSyntax (.binary operation (.column qualifier name) right)
  | columnLeft (operation : BinaryOp)
      (allowed : operation = .eq ∨ operation = .ne ∨ operation = .lt ∨
        operation = .le ∨ operation = .gt ∨ operation = .ge)
      (left : Expr) (qualifier : Option String) (name : String)
      (leftLiteral : LiteralSyntax left) :
      PredicateSyntax (.binary operation left (.column qualifier name))
  | isNull (qualifier : Option String) (name : String) (negated : Bool) :
      PredicateSyntax (.isNull (.column qualifier name) negated)
  | not {expression : Expr} : PredicateSyntax expression →
      PredicateSyntax (.unary .not expression)
  | and {left right : Expr} : PredicateSyntax left → PredicateSyntax right →
      PredicateSyntax (.binary .and left right)
  | or {left right : Expr} : PredicateSyntax left → PredicateSyntax right →
      PredicateSyntax (.binary .or left right)

private theorem comparisonSyntax_of_success {schema : Core.Schema}
    {operation : BinaryOp}
    (allowed : operation = .eq ∨ operation = .ne ∨ operation = .lt ∨
      operation = .le ∨ operation = .gt ∨ operation = .ge)
    (forward reverse : Nat → Core.Value → Core.Predicate)
    {left right : Expr} {translated : Core.Predicate}
    (success : comparisonPredicate schema forward reverse left right =
      .ok translated) :
    PredicateSyntax (.binary operation left right) := by
  cases leftRef : columnRef? left with
  | some reference =>
      rcases reference with ⟨qualifier, name⟩
      have leftEqual := columnRef?_eq_some_iff.mp leftRef
      subst left
      unfold comparisonPredicate at success
      rw [leftRef] at success
      cases found : column schema name with
      | error message =>
          simp [found, Except.map] at success
          cases success
      | ok index =>
          cases decoded : literal right with
          | error message =>
              simp [found, decoded, Except.instMonad, Except.bind,
                Except.map] at success
          | ok value =>
              exact .columnRight operation allowed qualifier name right
                (literalSyntax_of_success decoded)
  | none =>
      cases rightRef : columnRef? right with
      | none =>
          simp [comparisonPredicate, leftRef, rightRef, unsupported] at success
      | some reference =>
          rcases reference with ⟨qualifier, name⟩
          have rightEqual := columnRef?_eq_some_iff.mp rightRef
          subst right
          unfold comparisonPredicate at success
          rw [leftRef, rightRef] at success
          cases found : column schema name with
          | error message =>
              simp [found, Except.map] at success
              cases success
          | ok index =>
              cases decoded : literal left with
              | error message =>
                  simp [found, decoded, Except.instMonad, Except.bind,
                    Except.map] at success
              | ok value =>
                  exact .columnLeft operation allowed left qualifier name
                    (literalSyntax_of_success decoded)

theorem predicateSyntax_of_success {schema : Core.Schema} {expression : Expr}
    {translated : Core.Predicate}
    (success : predicate schema expression = .ok translated) :
    PredicateSyntax expression := by
  cases expression with
  | binary operation left right =>
      cases operation with
      | eq => exact comparisonSyntax_of_success (by simp) _ _ success
      | ne => exact comparisonSyntax_of_success (by simp) _ _ success
      | lt => exact comparisonSyntax_of_success (by simp) _ _ success
      | le => exact comparisonSyntax_of_success (by simp) _ _ success
      | gt => exact comparisonSyntax_of_success (by simp) _ _ success
      | ge => exact comparisonSyntax_of_success (by simp) _ _ success
      | and =>
          cases leftResult : predicate schema left with
          | error message =>
              simp [predicate, leftResult, Except.map] at success
              cases success
          | ok leftPredicate =>
              cases rightResult : predicate schema right with
              | error message =>
                  simp [predicate, leftResult, rightResult, Except.map] at success
                  cases success
              | ok rightPredicate =>
                  exact .and (predicateSyntax_of_success leftResult)
                    (predicateSyntax_of_success rightResult)
      | or =>
          cases leftResult : predicate schema left with
          | error message =>
              simp [predicate, leftResult, Except.map] at success
              cases success
          | ok leftPredicate =>
              cases rightResult : predicate schema right with
              | error message =>
                  simp [predicate, leftResult, rightResult, Except.map] at success
                  cases success
              | ok rightPredicate =>
                  exact .or (predicateSyntax_of_success leftResult)
                    (predicateSyntax_of_success rightResult)
      | add | sub | mul | div | mod | is | isNot | like | glob |
          concat | bitAnd | bitOr | shiftLeft | shiftRight | arrow | arrowText =>
          simp [predicate, unsupported] at success
      | «match» => simp [predicate, unsupported] at success
  | unary operation argument =>
      cases operation with
      | not =>
          cases translatedArgument : predicate schema argument with
          | error message =>
              simp [predicate, translatedArgument, Except.map] at success
              cases success
          | ok argumentPredicate =>
              exact .not (predicateSyntax_of_success translatedArgument)
      | plus | neg | bitNot => simp [predicate, unsupported] at success
  | isNull argument negated =>
      cases argument with
      | column qualifier name => exact .isNull qualifier name negated
      | literal | star | unary | binary | call | isNull | inList | collate |
          case_ | scalarSubquery | inSubquery | existsSubquery =>
          simp [predicate, unsupported] at success
  | literal | column | star | call | inList | collate | case_ | scalarSubquery |
      inSubquery | existsSubquery => simp [predicate, unsupported] at success
termination_by expression.height
decreasing_by all_goals simp_all [Expr.height] <;> omega

end CoreSQL
end SQLeanite
