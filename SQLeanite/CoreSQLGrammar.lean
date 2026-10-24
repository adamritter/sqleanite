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
  | constantExpression (expression : Expr)
      (admitted : SQLite.Scalar.admitted expression = true) : LiteralSyntax expression

theorem literalSyntax_of_success {expression : Expr} {value : Core.Value}
    (success : literal expression = .ok value) : LiteralSyntax expression := by
  by_cases admitted : SQLite.Scalar.admitted expression = true
  · exact .constantExpression expression admitted
  · simp [literal, SQLSurface.literal, admitted, SQLSurface.unsupported] at success

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
              simp [found, decoded, Seq.seq, bind, Functor.map, Except.bind,
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
                  simp [found, decoded, Seq.seq, bind, Functor.map, Except.bind,
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

inductive ProjectionColumnSyntax : ResultColumn → Prop where
  | star (alias sourceSql) :
      ProjectionColumnSyntax ⟨.star none, alias, sourceSql⟩
  | column (qualifier name alias sourceSql) :
      ProjectionColumnSyntax ⟨.column qualifier name, alias, sourceSql⟩

def ProjectionSyntax (columns : List ResultColumn) : Prop :=
  ∀ column ∈ columns, ProjectionColumnSyntax column

theorem projectionColumnSyntax_of_success {schema : Core.Schema}
    {input : ResultColumn} {columns : List Nat}
    (success : projectionColumn schema input = .ok columns) :
    ProjectionColumnSyntax input := by
  rcases input with ⟨expression, alias, sourceSql⟩
  cases expression with
  | star qualifier =>
      cases qualifier with
      | none => exact .star alias sourceSql
      | some qualifier => simp [projectionColumn, unsupported] at success
  | column qualifier name => exact .column qualifier name alias sourceSql
  | literal | unary | binary | call | isNull | inList | collate | case_ |
      scalarSubquery | inSubquery | existsSubquery =>
      simp [projectionColumn, unsupported] at success

theorem projectionSyntax_of_success (schema : Core.Schema) :
    ∀ {inputs : List ResultColumn} {columns : List Nat},
      projection schema inputs = .ok columns → ProjectionSyntax inputs
  | [], _, _ => by simp [ProjectionSyntax]
  | input :: inputs, columns, success => by
      unfold projection at success
      cases head : projectionColumn schema input with
      | error message =>
          simp [head, Seq.seq, bind, Functor.map, Except.bind, Except.map] at success
      | ok first =>
          cases tail : projection schema inputs with
          | error message =>
              simp [head, tail, Seq.seq, bind, Functor.map, Except.bind, Except.map] at success
          | ok remaining =>
              intro candidate member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact projectionColumnSyntax_of_success head
              · exact projectionSyntax_of_success schema tail candidate member

inductive OrderTermSyntax : OrderTerm → Prop where
  | column (qualifier name descending) :
      OrderTermSyntax ⟨.column qualifier name, descending⟩

def OrderingSyntax (terms : List OrderTerm) : Prop :=
  ∀ term ∈ terms, OrderTermSyntax term

theorem orderingSyntax_of_success (schema : Core.Schema) :
    ∀ {inputs : List OrderTerm} {ordering : List (Nat × Bool)},
      orderBy schema inputs = .ok ordering → OrderingSyntax inputs
  | [], _, _ => by simp [OrderingSyntax]
  | term :: terms, ordering, success => by
      rcases term with ⟨expression, descending⟩
      cases expression with
      | column qualifier name =>
          unfold orderBy at success
          cases first : column schema name with
          | error message =>
              simp [first, Seq.seq, bind, Functor.map, Except.bind, Except.map] at success
          | ok index =>
              cases rest : orderBy schema terms with
              | error message =>
                  simp [first, rest, Seq.seq, bind, Functor.map, Except.bind,
                    Except.map] at success
              | ok tail =>
                  intro candidate member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact .column qualifier name descending
                  · exact orderingSyntax_of_success schema rest candidate member
      | literal | star | unary | binary | call | isNull | inList | collate |
          case_ | scalarSubquery | inSubquery | existsSubquery =>
          simp [orderBy, unsupported] at success

inductive GroupColumnSyntax : Expr → Prop where
  | column (qualifier name) : GroupColumnSyntax (.column qualifier name)

def GroupingSyntax (expressions : List Expr) : Prop :=
  ∀ expression ∈ expressions, GroupColumnSyntax expression

theorem groupingSyntax_of_success (schema : Core.Schema) :
    ∀ {inputs : List Expr} {groups : List Nat},
      groupColumns schema inputs = .ok groups → GroupingSyntax inputs
  | [], _, _ => by simp [GroupingSyntax]
  | expression :: expressions, groups, success => by
      cases expression with
      | column qualifier name =>
          unfold groupColumns at success
          cases first : column schema name with
          | error message =>
              simp [first, Seq.seq, bind, Functor.map, Except.bind, Except.map] at success
          | ok index =>
              cases rest : groupColumns schema expressions with
              | error message =>
                  simp [first, rest, Seq.seq, bind, Functor.map, Except.bind,
                    Except.map] at success
              | ok tail =>
                  intro candidate member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact .column qualifier name
                  · exact groupingSyntax_of_success schema rest candidate member
      | literal | star | unary | binary | call | isNull | inList | collate |
          case_ | scalarSubquery | inSubquery | existsSubquery =>
          simp [groupColumns, unsupported] at success

inductive GroupOutputSyntax : ResultColumn → Prop where
  | key (qualifier name alias sourceSql) :
      GroupOutputSyntax ⟨.column qualifier name, alias, sourceSql⟩
  | countStar (name arguments alias sourceSql) : canonical name = "count" →
      arguments.isEmpty →
      GroupOutputSyntax ⟨.call name arguments true, alias, sourceSql⟩
  | aggregate (name arguments qualifier columnName alias sourceSql) :
      arguments.toList = [.column qualifier columnName] →
      (canonical name = "count" ∨ canonical name = "sum" ∨
        canonical name = "min" ∨ canonical name = "max") →
      GroupOutputSyntax
        ⟨.call name arguments false, alias, sourceSql⟩

theorem groupOutputSyntax_of_success {schema : Core.Schema} {groups : List Nat}
    {input : ResultColumn} {output : Core.GroupOutput}
    (success : groupOutput schema groups input = .ok output) :
    GroupOutputSyntax input := by
  rcases input with ⟨expression, alias, sourceSql⟩
  cases expression with
  | column qualifier name => exact .key qualifier name alias sourceSql
  | call name arguments star =>
      cases star with
      | true =>
          by_cases count : canonical name = "count"
          · by_cases empty : arguments.isEmpty
            · exact .countStar name arguments alias sourceSql count empty
            · simp [groupOutput, count, empty, unsupported] at success
          · simp [groupOutput, count, unsupported] at success
      | false =>
          cases listShape : arguments.toList with
          | nil => simp [groupOutput, listShape, unsupported] at success
          | cons first rest =>
              cases rest with
              | nil =>
                  cases first with
                  | column qualifier columnName =>
                      by_cases count : canonical name = "count"
                      · exact .aggregate name arguments qualifier columnName alias
                          sourceSql listShape (Or.inl count)
                      · by_cases sum : canonical name = "sum"
                        · exact .aggregate name arguments qualifier columnName alias
                            sourceSql listShape (Or.inr (Or.inl sum))
                        · by_cases minimum : canonical name = "min"
                          · exact .aggregate name arguments qualifier columnName alias
                              sourceSql listShape (Or.inr (Or.inr (Or.inl minimum)))
                          · by_cases maximum : canonical name = "max"
                            · exact .aggregate name arguments qualifier columnName alias
                                sourceSql listShape (Or.inr (Or.inr (Or.inr maximum)))
                            · simp [groupOutput, listShape, count, sum, minimum,
                                maximum, unsupported] at success
                  | literal | star | unary | binary | call | isNull | inList |
                      collate | case_ | scalarSubquery | inSubquery |
                      existsSubquery =>
                      simp [groupOutput, listShape, unsupported] at success
              | cons second tail =>
                  simp [groupOutput, listShape, unsupported] at success
  | literal | star | unary | binary | isNull | inList | collate | case_ |
      scalarSubquery | inSubquery | existsSubquery =>
      simp [groupOutput, unsupported] at success

inductive JoinOperandSyntax : Expr → Prop where
  | column (qualifier name) :
      JoinOperandSyntax (.column qualifier name)
  | literal {expression : Expr} : LiteralSyntax expression →
      JoinOperandSyntax expression

theorem joinOperandSyntax_of_success {context : JoinContext} {expression : Expr}
    {operand : CoreJoin.Operand}
    (success : joinOperand context expression = .ok operand) :
    JoinOperandSyntax expression := by
  have constant (e : Expr)
      (h : CoreJoin.Operand.literal <$> literal e = .ok operand) : JoinOperandSyntax e := by
    cases decoded : literal e with
    | error message => simp [decoded, Functor.map, Except.map] at h
    | ok value => exact .literal (literalSyntax_of_success decoded)
  cases expression with
  | column qualifier name => exact .column qualifier name
  | literal value => exact .literal (.literal value)
  | unary | star | binary | call | isNull | inList | collate | case_ | scalarSubquery |
      inSubquery | existsSubquery => exact constant _ success

inductive JoinPredicateSyntax : Expr → Prop where
  | comparison (operation : BinaryOp)
      (allowed : operation = .eq ∨ operation = .ne ∨ operation = .lt ∨
        operation = .le ∨ operation = .gt ∨ operation = .ge)
      {left right : Expr} : JoinOperandSyntax left → JoinOperandSyntax right →
      JoinPredicateSyntax (.binary operation left right)
  | isNull {operand : Expr} (negated : Bool) : JoinOperandSyntax operand →
      JoinPredicateSyntax (.isNull operand negated)
  | not {expression : Expr} : JoinPredicateSyntax expression →
      JoinPredicateSyntax (.unary .not expression)
  | and {left right : Expr} : JoinPredicateSyntax left →
      JoinPredicateSyntax right → JoinPredicateSyntax (.binary .and left right)
  | or {left right : Expr} : JoinPredicateSyntax left →
      JoinPredicateSyntax right → JoinPredicateSyntax (.binary .or left right)

private theorem joinComparisonOperands_of_success {context : JoinContext}
    {operation : BinaryOp}
    (allowed : operation = .eq ∨ operation = .ne ∨ operation = .lt ∨
      operation = .le ∨ operation = .gt ∨ operation = .ge)
    (constructor : CoreJoin.Operand → CoreJoin.Operand → CoreJoin.Predicate)
    {left right : Expr} {predicate : CoreJoin.Predicate}
    (success : constructor <$> joinOperand context left <*>
      joinOperand context right = .ok predicate) :
    JoinPredicateSyntax (.binary operation left right) := by
  cases leftResult : joinOperand context left with
  | error message =>
      simp [leftResult, Seq.seq, bind, Functor.map, Except.bind, Except.map] at success
  | ok leftOperand =>
      cases rightResult : joinOperand context right with
      | error message =>
          simp [leftResult, rightResult, Seq.seq, bind, Functor.map, Except.bind,
            Except.map] at success
      | ok rightOperand =>
          exact .comparison operation allowed
            (joinOperandSyntax_of_success leftResult)
            (joinOperandSyntax_of_success rightResult)

theorem joinPredicateSyntax_of_success {context : JoinContext} {expression : Expr}
    {predicate : CoreJoin.Predicate}
    (success : joinPredicate context expression = .ok predicate) :
    JoinPredicateSyntax expression := by
  cases expression with
  | binary operation left right =>
      cases operation with
      | eq => exact joinComparisonOperands_of_success (by simp) _ success
      | ne => exact joinComparisonOperands_of_success (by simp) _ success
      | lt => exact joinComparisonOperands_of_success (by simp) _ success
      | le => exact joinComparisonOperands_of_success (by simp) _ success
      | gt => exact joinComparisonOperands_of_success (by simp) _ success
      | ge => exact joinComparisonOperands_of_success (by simp) _ success
      | and =>
          change CoreJoin.Predicate.and <$> joinPredicate context left <*>
            joinPredicate context right = Except.ok predicate at success
          cases leftResult : joinPredicate context left with
          | error message =>
              rw [leftResult] at success
              change Except.error message = Except.ok predicate at success
              contradiction
          | ok leftPredicate =>
              cases rightResult : joinPredicate context right with
              | error message =>
                  rw [leftResult, rightResult] at success
                  change Except.error message = Except.ok predicate at success
                  contradiction
              | ok rightPredicate =>
                  exact .and (joinPredicateSyntax_of_success leftResult)
                    (joinPredicateSyntax_of_success rightResult)
      | or =>
          change CoreJoin.Predicate.or <$> joinPredicate context left <*>
            joinPredicate context right = Except.ok predicate at success
          cases leftResult : joinPredicate context left with
          | error message =>
              rw [leftResult] at success
              change Except.error message = Except.ok predicate at success
              contradiction
          | ok leftPredicate =>
              cases rightResult : joinPredicate context right with
              | error message =>
                  rw [leftResult, rightResult] at success
                  change Except.error message = Except.ok predicate at success
                  contradiction
              | ok rightPredicate =>
                  exact .or (joinPredicateSyntax_of_success leftResult)
                    (joinPredicateSyntax_of_success rightResult)
      | add | sub | mul | div | mod | is | isNot | like | glob | «match» |
          concat | bitAnd | bitOr | shiftLeft | shiftRight | arrow | arrowText =>
          simp [joinPredicate, unsupported] at success
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
          change CoreJoin.Predicate.not <$> joinPredicate context argument =
            Except.ok predicate at success
          cases translated : joinPredicate context argument with
          | error message =>
              rw [translated] at success
              change Except.error message = Except.ok predicate at success
              contradiction
          | ok nested => exact .not (joinPredicateSyntax_of_success translated)
      | plus | neg | bitNot => simp [joinPredicate, unsupported] at success
  | literal | column | star | call | inList | collate | case_ | scalarSubquery |
      inSubquery | existsSubquery => simp [joinPredicate, unsupported] at success
termination_by expression.height
decreasing_by all_goals simp_all [Expr.height] <;> omega

end CoreSQL
end SQLeanite
