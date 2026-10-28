import SQLeanite.CoreSQL.SchemaReplacementRows

namespace SQLeanite
namespace CoreSQL

inductive LiteralSyntax : Expr → Prop where
  | literal (value : Value) (spelling : Option String := none) : LiteralSyntax (.literal value spelling)
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
          simp [found, bind, Except.bind, Except.map] at success
      | ok index =>
          cases decoded : literal right with
          | error message =>
              simp [comparisonLiteral, found, decoded, Seq.seq, bind, Functor.map, Except.bind,
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
              simp [found, bind, Except.bind, Except.map] at success
          | ok index =>
              cases decoded : literal left with
              | error message =>
                  simp [comparisonLiteral, found, decoded, Seq.seq, bind, Functor.map, Except.bind,
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
  | column (qualifier name descending nullsFirst) :
      OrderTermSyntax ⟨.column qualifier name, descending, nullsFirst⟩
  | boundColumn (ctx : CoreExpr.Context) (expression : Expr) (descending : Bool)
      (nullsFirst : Option Bool) (qualifier : Option String) (name : String)
      (bound : ctx.bindNames expression = .column qualifier name) :
      OrderTermSyntax ⟨expression, descending, nullsFirst⟩

def OrderingSyntax (terms : List OrderTerm) : Prop :=
  ∀ term ∈ terms, OrderTermSyntax term

theorem orderingSyntax_of_success (schema : Core.Schema) :
    ∀ {inputs : List OrderTerm} {ordering : List (Nat × Bool)},
      orderBy schema inputs = .ok ordering → OrderingSyntax inputs
  | [], _, _ => by simp [OrderingSyntax]
  | term :: terms, ordering, success => by
      rcases term with ⟨expression, descending, nullsFirst⟩
      let ctx : CoreExpr.Context := { schema, sourceName := schema.name }
      cases bound : ({ schema, sourceName := schema.name } : CoreExpr.Context).bindNames expression with
      | column qualifier name =>
          simp only [orderBy, bound] at success
          cases first : column schema name with
          | error message =>
              simp [first, bind, Functor.map, Except.bind, Except.map] at success
          | ok index =>
              cases rest : orderBy schema terms with
              | error message =>
                  simp [first, rest, bind, Functor.map, Except.bind, Except.map] at success
              | ok tail =>
                  intro candidate member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact .boundColumn ctx expression descending nullsFirst qualifier name bound
                  · exact orderingSyntax_of_success schema rest candidate member
      | literal | star | unary | binary | call | isNull | inList | collate |
          case_ | scalarSubquery | inSubquery | existsSubquery =>
          simp [orderBy, bound, unsupported] at success

inductive GroupColumnSyntax : Expr → Prop where
  | column (qualifier name) : GroupColumnSyntax (.column qualifier name)
  | boundColumn (ctx : CoreExpr.Context) (expression : Expr)
      (qualifier : Option String) (name : String)
      (bound : ctx.bindNames expression = .column qualifier name) :
      GroupColumnSyntax expression

def GroupingSyntax (expressions : List Expr) : Prop :=
  ∀ expression ∈ expressions, GroupColumnSyntax expression

theorem groupingSyntax_of_success (schema : Core.Schema) :
    ∀ {inputs : List Expr} {groups : List Nat},
      groupColumns schema inputs = .ok groups → GroupingSyntax inputs
  | [], _, _ => by simp [GroupingSyntax]
  | expression :: expressions, groups, success => by
      let ctx : CoreExpr.Context := { schema, sourceName := schema.name }
      cases bound : ({ schema, sourceName := schema.name } : CoreExpr.Context).bindNames expression with
      | column qualifier name =>
          simp only [groupColumns, bound] at success
          cases first : column schema name with
          | error message =>
              simp [first, bind, Functor.map, Except.bind, Except.map] at success
          | ok index =>
              cases rest : groupColumns schema expressions with
              | error message =>
                  simp [first, rest, bind, Functor.map, Except.bind, Except.map] at success
              | ok tail =>
                  intro candidate member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact .boundColumn ctx candidate qualifier name bound
                  · exact groupingSyntax_of_success schema rest candidate member
      | literal | star | unary | binary | call | isNull | inList | collate |
          case_ | scalarSubquery | inSubquery | existsSubquery =>
          simp [groupColumns, bound, unsupported] at success

inductive GroupOutputSyntax : ResultColumn → Prop where
  | key (qualifier name alias sourceSql) :
      GroupOutputSyntax ⟨.column qualifier name, alias, sourceSql⟩
  | countStar (name arguments alias sourceSql) : canonical name = "count" →
      arguments.isEmpty →
      GroupOutputSyntax ⟨.call name arguments true, alias, sourceSql⟩
  | aggregate (name arguments qualifier columnName alias sourceSql) :
      arguments.toList = [.column qualifier columnName] →
      (canonical name = "count" ∨ canonical name = "sum" ∨
        canonical name = "min" ∨ canonical name = "max" ∨
        canonical name = "avg" ∨ canonical name = "total") →
      GroupOutputSyntax
        ⟨.call name arguments false, alias, sourceSql⟩

  | bound (ctx : CoreExpr.Context) (input : ResultColumn)
      (boundSyntax : GroupOutputSyntax { input with expr := ctx.bindNames input.expr }) :
      GroupOutputSyntax input

private theorem boundGroupOutputSyntax_of_success {schema : Core.Schema} {groups : List Nat}
    {input : ResultColumn} {output : Core.GroupOutput}
    (success : boundGroupOutput schema groups input = .ok output) :
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
            · simp [boundGroupOutput, count, empty, unsupported] at success
          · simp [boundGroupOutput, count, unsupported] at success
      | false =>
          cases listShape : arguments.toList with
          | nil => simp [boundGroupOutput, listShape, unsupported] at success
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
                                sourceSql listShape (by simp [maximum])
                            · by_cases average : canonical name = "avg"
                              · exact .aggregate name arguments qualifier columnName alias
                                  sourceSql listShape (by simp [average])
                              · by_cases total : canonical name = "total"
                                · exact .aggregate name arguments qualifier columnName alias
                                    sourceSql listShape (by simp [total])
                                · simp [boundGroupOutput, listShape, count, sum, minimum,
                                    maximum, average, total, unsupported] at success
                  | literal | star | unary | binary | call | isNull | inList |
                      collate | case_ | scalarSubquery | inSubquery |
                      existsSubquery =>
                      simp [boundGroupOutput, listShape, unsupported] at success
              | cons second tail =>
                  simp [boundGroupOutput, listShape, unsupported] at success
  | literal | star | unary | binary | isNull | inList | collate | case_ |
      scalarSubquery | inSubquery | existsSubquery =>
      simp [boundGroupOutput, unsupported] at success

theorem groupOutputSyntax_of_success {schema : Core.Schema} {groups : List Nat}
    {input : ResultColumn} {output : Core.GroupOutput}
    (success : groupOutput schema groups input = .ok output) :
    GroupOutputSyntax input := by
  exact .bound { schema, sourceName := schema.name } input
    (boundGroupOutputSyntax_of_success success)

inductive JoinOperandSyntax : Expr → Prop where
  | probability (name : String) {arguments : Array Expr} {inner : Expr} :
      SQLite.Probability.input? name arguments = some inner → JoinOperandSyntax inner →
      JoinOperandSyntax (.call name arguments false)
  | plus {expression : Expr} : JoinOperandSyntax expression → JoinOperandSyntax (.unary .plus expression)
  | collate {expression : Expr} (name : String) : JoinOperandSyntax expression → JoinOperandSyntax (.collate expression name)
  | column (qualifier name) :
      JoinOperandSyntax (.column qualifier name)
  | literal {expression : Expr} : LiteralSyntax expression →
      JoinOperandSyntax expression
  | bound (context : JoinContext) (expression : Expr) :
      JoinOperandSyntax (joinBindNames context expression) → JoinOperandSyntax expression

private theorem joinColumnAtomFuelSyntax_of_success {fuel : Nat} {expression : Expr}
    {reference : Option String × String}
    (success : joinColumnAtomFuel? fuel expression = some reference) : JoinOperandSyntax expression := by
  induction fuel generalizing expression with
  | zero => simp [joinColumnAtomFuel?] at success
  | succ fuel ih =>
      cases expression with
      | column qualifier name => exact .column qualifier name
      | unary operation argument =>
          cases operation with
          | plus => exact .plus (ih success)
          | neg | not | bitNot => simp [joinColumnAtomFuel?] at success
      | collate expression name => exact .collate name (ih success)
      | call name arguments star =>
          cases star with
          | true => simp [joinColumnAtomFuel?] at success
          | false =>
              cases input : SQLite.Probability.input? name arguments with
              | none => simp [joinColumnAtomFuel?, input] at success
              | some inner =>
                  exact .probability name input (ih (by simpa [joinColumnAtomFuel?, input] using success))
      | literal | star | binary | isNull | inList | case_ | scalarSubquery | inSubquery | existsSubquery =>
          simp [joinColumnAtomFuel?] at success

theorem joinOperandSyntax_of_success {context : JoinContext} {expression : Expr}
    {operand : CoreJoin.Operand}
    (success : joinOperand context expression = .ok operand) : JoinOperandSyntax expression := by
  apply JoinOperandSyntax.bound context expression
  cases found : joinColumnAtom? (joinBindNames context expression) with
  | some reference => exact joinColumnAtomFuelSyntax_of_success found
  | none =>
      cases decoded : literal (joinBindNames context expression) with
      | error message => simp [joinOperand, found, decoded, Functor.map, Except.map] at success
      | ok value => exact .literal (literalSyntax_of_success decoded)

inductive JoinPredicateSyntax : Expr → Prop where
  | static (context : JoinContext) (outer : Bool) {expression : Expr} (truth : Bool) :
      joinStaticAdmitted context expression outer = true →
      SQLite.StaticCondition.classify outer expression = some truth →
      JoinPredicateSyntax expression
  | membership {argument : Expr} {values : Array Expr} (negated affinity : Bool) :
      JoinOperandSyntax argument → (∀ value ∈ values.toList, JoinOperandSyntax value) →
      JoinPredicateSyntax (.inList argument values negated affinity)
  | isTruth (negated expected : Bool) {left right : Expr} :
      JoinOperandSyntax left → SQLite.Scalar.isTruthKeyword? right = some expected →
      JoinPredicateSyntax (.binary (if negated then .isNot else .is) left right)
  | truthy {expression : Expr} : JoinOperandSyntax expression → JoinPredicateSyntax expression
  | prepared (context : JoinContext) (expression : Expr) :
      JoinPredicateSyntax (SQLite.Scalar.prepare (joinBindNames context expression)) →
        JoinPredicateSyntax expression
  | comparison (operation : BinaryOp)
      (allowed : operation = .eq ∨ operation = .ne ∨ operation = .lt ∨
        operation = .le ∨ operation = .gt ∨ operation = .ge ∨ operation = .is ∨ operation = .isNot)
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

private theorem joinOperandListSyntax_of_success {context : JoinContext} {expressions : List Expr}
    {operands : List CoreJoin.Operand}
    (success : joinOperandList context expressions = .ok operands) :
    ∀ expression ∈ expressions, JoinOperandSyntax expression := by
  induction expressions generalizing operands with
  | nil => simp
  | cons expression rest ih =>
      cases first : joinOperand context expression with
      | error message => simp [joinOperandList, first, Seq.seq, Functor.map, Except.map, Except.bind] at success
      | ok operand =>
          cases remaining : joinOperandList context rest with
          | error message => simp [joinOperandList, first, remaining, Seq.seq, Functor.map, Except.map, Except.bind] at success
          | ok operands =>
              intro item member
              rcases List.mem_cons.mp member with equal | member
              · subst item; exact joinOperandSyntax_of_success first
              · exact ih remaining item member

theorem joinInListSyntax_of_success {context : JoinContext} {argument : Expr}
    {values : Array Expr} {negated affinity : Bool} {predicate : CoreJoin.Predicate}
    (success : joinInList context argument values negated affinity = .ok predicate) :
    JoinPredicateSyntax (.inList argument values negated affinity) := by
  cases first : joinOperand context argument with
  | error message => simp [joinInList, first, bind, Except.bind] at success
  | ok operand =>
      cases remaining : joinOperandList context values.toList with
      | error message => simp [joinInList, first, remaining, bind, Except.bind] at success
      | ok operands =>
          exact .membership negated affinity
            (joinOperandSyntax_of_success first) (joinOperandListSyntax_of_success remaining)

end CoreSQL

end SQLeanite
