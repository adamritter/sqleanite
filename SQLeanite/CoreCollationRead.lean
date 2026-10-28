import SQLeanite.CoreSQLGrammar
open SQLeanite
namespace SQLeanite.SQLite.Scalar

private theorem booleanKeyword_noCollation (expression : Expr) (truth : Bool) (fuel : Nat)
    (success : booleanKeyword? expression = some truth) :
    ExprCollation.nameFuel fuel expression = none := by
  cases expression <;> simp only [booleanKeyword?] at success
  all_goals try contradiction
  rename_i name args star
  split at success
  · rename_i allowed
    have empty : args = #[] := by
      simp only [Bool.and_eq_true, Array.isEmpty_iff] at allowed
      exact allowed.1
    subst args
    cases fuel <;> rfl
  · contradiction

private theorem quotedIdentifier_noCollation (expression : Expr) (name : String) (fuel : Nat)
    (success : quotedIdentifier? expression = some name) :
    ExprCollation.nameFuel fuel expression = none := by
  cases expression <;> simp only [quotedIdentifier?] at success
  all_goals try contradiction
  rename_i call args star
  split at success
  · cases args using Array.recOn with
    | mk values =>
      cases values with
      | nil => simp at success
      | cons first rest =>
        cases rest with
        | cons next rest => simp at success
        | nil =>
          cases first <;> simp at success
          rename_i value spelling
          cases value <;> cases spelling <;> simp at success
          cases fuel with
          | zero => rfl
          | succ fuel => cases fuel <;> rfl
  · contradiction

theorem bindNamesFuel_preserves_collation (hasColumn : String → Bool) (namesFuel : Nat) :
    ∀ (fuel : Nat) (expression : Expr),
      ExprCollation.nameFuel fuel (bindNamesFuel hasColumn namesFuel expression) =
        ExprCollation.nameFuel fuel expression := by
  induction namesFuel with
  | zero => intros; rfl
  | succ namesFuel ih =>
      intro fuel expression
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [bindNamesFuel]
          cases boolean : booleanKeyword? expression with
          | some truth =>
              simp only [boolean]
              split
              · exact (booleanKeyword_noCollation expression truth (fuel + 1) boolean).symm
              · rfl
          | none =>
              simp only [boolean]
              cases quoted : quotedIdentifier? expression with
              | some name =>
                  exact (quotedIdentifier_noCollation expression name (fuel + 1) quoted).symm
              | none =>
                  simp only [quoted]
                  cases expression <;> simp_all [ExprCollation.nameFuel, ExprCollation.callArguments_map, Array.foldl_map', Option.bind_map, Function.comp_def, ih]

private theorem booleanKeyword_noDeclaredCollation (expression : Expr) (truth : Bool) (fuel : Nat)
    (success : booleanKeyword? expression = some truth) :
    ExprCollation.declaredNameFuel fuel expression = none := by
  cases expression <;> simp only [booleanKeyword?] at success
  all_goals try contradiction
  rename_i name args star
  split at success
  · rename_i allowed
    have empty : args = #[] := by
      simp only [Bool.and_eq_true, Array.isEmpty_iff] at allowed
      exact allowed.1
    subst args
    cases star <;> cases fuel <;> simp [ExprCollation.declaredNameFuel]
  · contradiction

private theorem quotedIdentifier_noDeclaredCollation (expression : Expr) (name : String) (fuel : Nat)
    (success : quotedIdentifier? expression = some name) :
    ExprCollation.declaredNameFuel fuel expression = none := by
  cases expression <;> simp only [quotedIdentifier?] at success
  all_goals try contradiction
  rename_i call args star
  split at success
  · cases args using Array.recOn with
    | mk values =>
      cases values with
      | nil => simp at success
      | cons first rest =>
        cases rest with
        | cons next rest => simp at success
        | nil =>
          cases first <;> simp at success
          rename_i value spelling
          cases value <;> cases spelling <;> simp at success
          cases fuel with
          | zero => rfl
          | succ fuel => cases star <;> cases fuel <;> simp [ExprCollation.declaredNameFuel]
  · contradiction

private theorem bindNamesFuel_preserves_text (hasColumn : String → Bool) (fuel : Nat) (expression : Expr) :
    ExprCollation.literalText? (bindNamesFuel hasColumn fuel expression) = ExprCollation.literalText? expression := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases expression <;> simp only [bindNamesFuel, booleanKeyword?, quotedIdentifier?]
      all_goals repeat' (first | split | rfl)

theorem bindNamesFuel_preserves_declared_collation (hasColumn : String → Bool) (namesFuel : Nat) :
    ∀ (fuel : Nat) (expression : Expr),
      ExprCollation.declaredNameFuel fuel (bindNamesFuel hasColumn namesFuel expression) =
        ExprCollation.declaredNameFuel fuel expression := by
  induction namesFuel with
  | zero => intros; rfl
  | succ namesFuel ih =>
      intro fuel expression
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [bindNamesFuel]
          cases boolean : booleanKeyword? expression with
          | some truth =>
              simp only [boolean]
              split
              · exact (booleanKeyword_noDeclaredCollation expression truth (fuel + 1) boolean).symm
              · rfl
          | none =>
              simp only [boolean]
              cases quoted : quotedIdentifier? expression with
              | some name =>
                  exact (quotedIdentifier_noDeclaredCollation expression name (fuel + 1) quoted).symm
              | none =>
                  simp only [quoted]
                  cases expression <;> try rfl
                  case unary operation argument =>
                    cases operation <;> simp [ExprCollation.declaredNameFuel, ih]
                  case call name arguments star =>
                    cases star with
                    | true => rfl
                    | false =>
                        cases arguments using Array.recOn with
                        | mk values =>
                          cases values with
                          | nil => simp [ExprCollation.declaredNameFuel]
                          | cons first rest =>
                            cases rest with
                            | nil => simp [ExprCollation.declaredNameFuel, ih]
                            | cons second rest =>
                              cases rest with
                              | nil => simp [ExprCollation.declaredNameFuel, bindNamesFuel_preserves_text]
                              | cons third rest =>
                                cases rest with
                                | nil => simp [ExprCollation.declaredNameFuel, bindNamesFuel_preserves_text, ih]
                                | cons fourth rest => simp [ExprCollation.declaredNameFuel]

end SQLeanite.SQLite.Scalar

namespace SQLeanite.CoreSQLReadText

def NoExplicitCollation (expression : Expr) : Prop :=
  ∀ fuel, SQLite.ExprCollation.nameFuel fuel expression = none

theorem projection_noCollation (column : ResultColumn)
    (valid : CoreSQL.ProjectionColumnSyntax column) : NoExplicitCollation column.expr := by
  cases valid <;> intro fuel <;> cases fuel <;> rfl

theorem groupOutput_noCollation (column : ResultColumn)
    (valid : CoreSQL.GroupOutputSyntax column) : NoExplicitCollation column.expr := by
  induction valid with
  | key => intro fuel; cases fuel <;> rfl
  | countStar name arguments alias sourceSql named empty =>
      have equal : arguments = #[] := by simpa using empty
      subst arguments
      intro fuel; cases fuel <;> rfl
  | aggregate name arguments qualifier columnName alias sourceSql args named =>
      have equal : arguments = #[.column qualifier columnName] := Array.toList_inj.mp args
      subst arguments
      intro fuel; cases fuel with
      | zero => rfl
      | succ fuel => cases fuel <;> rfl
  | bound ctx input valid ih =>
      intro fuel
      rw [← SQLite.Scalar.bindNamesFuel_preserves_collation
        (fun name => (ctx.column? none name).isSome) input.expr.height fuel input.expr]
      exact ih fuel

@[simp] private theorem nameFuel_column (fuel : Nat) (qualifier : Option String) (name : String) :
    SQLite.ExprCollation.nameFuel fuel (.column qualifier name) = none := by cases fuel <;> rfl

theorem count_noCollation (schema : Core.Schema) (columns : List ResultColumn)
    (target : Core.CountTarget) (success : CoreSQL.countTarget? schema columns = .ok (some target)) :
    ∀ column ∈ columns, NoExplicitCollation column.expr := by
  fun_cases CoreSQL.countTarget? schema columns <;> simp_all [CoreSQL.countTarget?, CoreSQL.canonical]
  all_goals try (split at success <;> simp_all)
  all_goals
    intro fuel
    cases fuel <;> simp_all [SQLite.ExprCollation.nameFuel, SQLite.ExprCollation.callArguments, ← Array.foldl_toList]

theorem sum_noCollation (schema : Core.Schema) (columns : List ResultColumn)
    (target : Nat) (success : CoreSQL.sumColumn? schema columns = .ok (some target)) :
    ∀ column ∈ columns, NoExplicitCollation column.expr := by
  fun_cases CoreSQL.sumColumn? schema columns <;> simp_all [CoreSQL.sumColumn?, CoreSQL.canonical]
  all_goals intro fuel; cases fuel <;> simp_all [SQLite.ExprCollation.nameFuel, SQLite.ExprCollation.callArguments, ← Array.foldl_toList]

theorem extreme_noCollation (schema : Core.Schema) (columns : List ResultColumn)
    (target : Bool × Nat) (success : CoreSQL.extremeColumn? schema columns = .ok (some target)) :
    ∀ column ∈ columns, NoExplicitCollation column.expr := by
  fun_cases CoreSQL.extremeColumn? schema columns <;> simp_all [CoreSQL.extremeColumn?, CoreSQL.canonical]
  all_goals intro fuel; cases fuel <;> simp_all [SQLite.ExprCollation.nameFuel, SQLite.ExprCollation.callArguments, ← Array.foldl_toList]

theorem groups_noCollation (schema : Core.Schema) (groups : List Nat)
    (columns : List ResultColumn) (outputs : List Core.GroupOutput)
    (success : CoreSQL.groupOutputs schema groups columns = .ok outputs) :
    ∀ column ∈ columns, NoExplicitCollation column.expr := by
  induction columns generalizing outputs with
  | nil => simp
  | cons first rest ih =>
      simp only [CoreSQL.groupOutputs] at success
      cases head : CoreSQL.groupOutput schema groups first with
      | error message => simp [head, bind, Except.bind] at success
      | ok output =>
          cases tail : CoreSQL.groupOutputs schema groups rest with
          | error message => simp [head, tail, bind, Except.bind] at success
          | ok outputs =>
              intro column member
              rcases List.mem_cons.mp member with rfl | member
              · exact groupOutput_noCollation column (CoreSQL.groupOutputSyntax_of_success head)
              · exact ih outputs tail column member

private theorem joinLiteral_noCollation (expression : Expr)
    (admitted : CoreSQL.joinLiteralExpression expression = true) :
    NoExplicitCollation expression := by
  intro fuel
  induction fuel generalizing expression with
  | zero => rfl
  | succ fuel ih =>
      cases expression
      case literal value spelling => rfl
      case unary operation argument => exact ih argument admitted
      case call name arguments star =>
        have present : (SQLite.Scalar.booleanKeyword? (.call name arguments star)).isSome = true := admitted
        cases marked : SQLite.Scalar.booleanKeyword? (.call name arguments star) with
        | none => simp [marked] at present
        | some truth => exact SQLite.Scalar.booleanKeyword_noCollation _ truth (fuel + 1) marked
      all_goals simp [CoreSQL.joinLiteralExpression, SQLite.Scalar.booleanKeyword?] at admitted

private theorem joinResultExpr_noCollation (context : CoreSQL.JoinContext) (expression : Expr)
    (operands : List CoreJoin.Operand)
    (success : CoreSQL.joinResultExpr context expression = .ok operands) :
    NoExplicitCollation expression := by
  by_cases constant : CoreSQL.joinLiteralExpression expression = true
  · exact joinLiteral_noCollation expression constant
  · cases expression <;> simp_all [CoreSQL.joinResultExpr, CoreSQL.unsupported, bind, Except.bind]
    all_goals intro fuel; cases fuel <;> rfl

private theorem joinColumn_noCollation (context : CoreSQL.JoinContext) (column : ResultColumn)
    (operands : List CoreJoin.Operand)
    (success : CoreSQL.joinResultColumn context column = .ok operands) :
    NoExplicitCollation column.expr := by
  have bound := joinResultExpr_noCollation context (CoreSQL.joinBindNames context column.expr) operands success
  intro fuel
  have preserved := SQLite.Scalar.bindNamesFuel_preserves_collation
    (CoreSQL.joinHasColumn context) column.expr.height fuel column.expr
  calc SQLite.ExprCollation.nameFuel fuel column.expr
      = SQLite.ExprCollation.nameFuel fuel (CoreSQL.joinBindNames context column.expr) := by
          simpa [CoreSQL.joinBindNames, SQLite.Scalar.bindNames] using preserved.symm
    _ = none := bound fuel

theorem joinProjection_noCollation (context : CoreSQL.JoinContext)
    (columns : List ResultColumn) (references : List CoreJoin.Operand)
    (success : CoreSQL.joinProjection context columns = .ok references) :
    ∀ column ∈ columns, NoExplicitCollation column.expr := by
  induction columns generalizing references with
  | nil => simp
  | cons first rest ih =>
      simp only [CoreSQL.joinProjection] at success
      cases head : CoreSQL.joinResultColumn context first with
      | error message => simp [head, bind, Except.bind] at success
      | ok output =>
          cases tail : CoreSQL.joinProjection context rest with
          | error message => simp [head, tail, bind, Except.bind] at success
          | ok outputs =>
              intro column member
              rcases List.mem_cons.mp member with rfl | member
              · exact joinColumn_noCollation context column output head
              · exact ih outputs tail column member

theorem joinQueryBound_noCollation (select : Select) (source : TableRef)
    (context : CoreSQL.JoinContext) (query : CoreJoin.Query)
    (success : CoreSQL.joinQueryBound select source context = .ok query) :
    ∀ column ∈ select.columns.toList, NoExplicitCollation column.expr := by
  unfold CoreSQL.joinQueryBound at success
  simp only [bind, Except.bind, pure, Except.pure, CoreSQL.unsupported] at success
  repeat' (split at success)
  all_goals try contradiction
  all_goals exact joinProjection_noCollation _ _ _ (by assumption)

theorem joinQuery_noCollation (select : Select) (leftTable rightTable : String)
    (left right : Core.Schema) (query : CoreJoin.Query)
    (success : CoreSQL.joinQuery select leftTable rightTable left right = .ok query) :
    ∀ column ∈ select.columns.toList, NoExplicitCollation column.expr := by
  unfold CoreSQL.joinQuery at success
  by_cases aliases : CoreSQL.joinAliasesNeeded select left right = true
  · simp [aliases, CoreSQL.unsupported, bind, Except.bind] at success
  simp [aliases, bind, Except.bind, pure, Except.pure] at success
  cases sources : select.sources.toList with
  | nil => simp [sources, bind, Except.bind, CoreSQL.unsupported] at success
  | cons first rest =>
    cases rest with
    | nil => simp [sources, bind, Except.bind, CoreSQL.unsupported] at success
    | cons second rest =>
      cases rest with
      | cons third rest => simp [sources, bind, Except.bind, CoreSQL.unsupported] at success
      | nil =>
        simp only [sources, bind, Except.bind, pure, Except.pure, CoreSQL.unsupported] at success
        repeat' (split at success)
        all_goals try contradiction
        all_goals exact joinQueryBound_noCollation _ _ _ _ (by assumption)

def NoDeclaredCollation (expression : Expr) : Prop :=
  ∀ fuel, SQLite.ExprCollation.declaredNameFuel fuel expression = none

theorem projection_noDeclaredCollation (column : ResultColumn)
    (valid : CoreSQL.ProjectionColumnSyntax column) : NoDeclaredCollation column.expr := by
  cases valid <;> intro fuel <;> cases fuel <;> simp [SQLite.ExprCollation.declaredNameFuel]

theorem groupOutput_noDeclaredCollation (column : ResultColumn)
    (valid : CoreSQL.GroupOutputSyntax column) : NoDeclaredCollation column.expr := by
  induction valid with
  | key => intro fuel; cases fuel <;> simp [SQLite.ExprCollation.declaredNameFuel]
  | countStar name arguments alias sourceSql named empty =>
      have equal : arguments = #[] := by simpa using empty
      subst arguments
      intro fuel; cases fuel <;> simp [SQLite.ExprCollation.declaredNameFuel]
  | aggregate name arguments qualifier columnName alias sourceSql args named =>
      have equal : arguments = #[.column qualifier columnName] := Array.toList_inj.mp args
      subst arguments
      intro fuel; cases fuel with
      | zero => rfl
      | succ fuel => cases fuel <;> simp [SQLite.ExprCollation.declaredNameFuel]
  | bound ctx input valid ih =>
      intro fuel
      rw [← SQLite.Scalar.bindNamesFuel_preserves_declared_collation
        (fun name => (ctx.column? none name).isSome) input.expr.height fuel input.expr]
      exact ih fuel

@[simp] private theorem declaredNameFuel_column (fuel : Nat) (qualifier : Option String) (name : String) :
    SQLite.ExprCollation.declaredNameFuel fuel (.column qualifier name) = none := by cases fuel <;> simp [SQLite.ExprCollation.declaredNameFuel]

theorem count_noDeclaredCollation (schema : Core.Schema) (columns : List ResultColumn)
    (target : Core.CountTarget) (success : CoreSQL.countTarget? schema columns = .ok (some target)) :
    ∀ column ∈ columns, NoDeclaredCollation column.expr := by
  fun_cases CoreSQL.countTarget? schema columns <;> simp_all [CoreSQL.countTarget?, CoreSQL.canonical]
  all_goals try (split at success <;> simp_all)
  all_goals
    intro fuel
    cases fuel <;> simp_all [SQLite.ExprCollation.declaredNameFuel, SQLite.ExprCollation.callArguments, ← Array.foldl_toList]

theorem sum_noDeclaredCollation (schema : Core.Schema) (columns : List ResultColumn)
    (target : Nat) (success : CoreSQL.sumColumn? schema columns = .ok (some target)) :
    ∀ column ∈ columns, NoDeclaredCollation column.expr := by
  fun_cases CoreSQL.sumColumn? schema columns <;> simp_all [CoreSQL.sumColumn?, CoreSQL.canonical]
  all_goals intro fuel; cases fuel <;> simp_all [SQLite.ExprCollation.declaredNameFuel, SQLite.ExprCollation.callArguments, ← Array.foldl_toList]

theorem extreme_noDeclaredCollation (schema : Core.Schema) (columns : List ResultColumn)
    (target : Bool × Nat) (success : CoreSQL.extremeColumn? schema columns = .ok (some target)) :
    ∀ column ∈ columns, NoDeclaredCollation column.expr := by
  fun_cases CoreSQL.extremeColumn? schema columns <;> simp_all [CoreSQL.extremeColumn?, CoreSQL.canonical]
  all_goals intro fuel; cases fuel <;> simp_all [SQLite.ExprCollation.declaredNameFuel, SQLite.ExprCollation.callArguments, ← Array.foldl_toList]

theorem groups_noDeclaredCollation (schema : Core.Schema) (groups : List Nat)
    (columns : List ResultColumn) (outputs : List Core.GroupOutput)
    (success : CoreSQL.groupOutputs schema groups columns = .ok outputs) :
    ∀ column ∈ columns, NoDeclaredCollation column.expr := by
  induction columns generalizing outputs with
  | nil => simp
  | cons first rest ih =>
      simp only [CoreSQL.groupOutputs] at success
      cases head : CoreSQL.groupOutput schema groups first with
      | error message => simp [head, bind, Except.bind] at success
      | ok output =>
          cases tail : CoreSQL.groupOutputs schema groups rest with
          | error message => simp [head, tail, bind, Except.bind] at success
          | ok outputs =>
              intro column member
              rcases List.mem_cons.mp member with rfl | member
              · exact groupOutput_noDeclaredCollation column (CoreSQL.groupOutputSyntax_of_success head)
              · exact ih outputs tail column member

private theorem joinLiteral_noDeclaredCollation (expression : Expr)
    (admitted : CoreSQL.joinLiteralExpression expression = true) :
    NoDeclaredCollation expression := by
  intro fuel
  induction fuel generalizing expression with
  | zero => rfl
  | succ fuel ih =>
      cases expression
      case literal value spelling => rfl
      case unary operation argument =>
        cases operation <;> simp [SQLite.ExprCollation.declaredNameFuel, ih argument admitted]
      case call name arguments star =>
        have present : (SQLite.Scalar.booleanKeyword? (.call name arguments star)).isSome = true := admitted
        cases marked : SQLite.Scalar.booleanKeyword? (.call name arguments star) with
        | none => simp [marked] at present
        | some truth => exact SQLite.Scalar.booleanKeyword_noDeclaredCollation _ truth (fuel + 1) marked
      all_goals simp [CoreSQL.joinLiteralExpression, SQLite.Scalar.booleanKeyword?] at admitted

private theorem joinResultExpr_noDeclaredCollation (context : CoreSQL.JoinContext) (expression : Expr)
    (operands : List CoreJoin.Operand)
    (success : CoreSQL.joinResultExpr context expression = .ok operands) :
    NoDeclaredCollation expression := by
  by_cases constant : CoreSQL.joinLiteralExpression expression = true
  · exact joinLiteral_noDeclaredCollation expression constant
  · cases expression <;> simp_all [CoreSQL.joinResultExpr, CoreSQL.unsupported, bind, Except.bind]
    all_goals intro fuel; cases fuel <;> simp [SQLite.ExprCollation.declaredNameFuel]

private theorem joinColumn_noDeclaredCollation (context : CoreSQL.JoinContext) (column : ResultColumn)
    (operands : List CoreJoin.Operand)
    (success : CoreSQL.joinResultColumn context column = .ok operands) :
    NoDeclaredCollation column.expr := by
  have bound := joinResultExpr_noDeclaredCollation context (CoreSQL.joinBindNames context column.expr) operands success
  intro fuel
  have preserved := SQLite.Scalar.bindNamesFuel_preserves_declared_collation
    (CoreSQL.joinHasColumn context) column.expr.height fuel column.expr
  calc SQLite.ExprCollation.declaredNameFuel fuel column.expr
      = SQLite.ExprCollation.declaredNameFuel fuel (CoreSQL.joinBindNames context column.expr) := by
          simpa [CoreSQL.joinBindNames, SQLite.Scalar.bindNames] using preserved.symm
    _ = none := bound fuel

theorem joinProjection_noDeclaredCollation (context : CoreSQL.JoinContext)
    (columns : List ResultColumn) (references : List CoreJoin.Operand)
    (success : CoreSQL.joinProjection context columns = .ok references) :
    ∀ column ∈ columns, NoDeclaredCollation column.expr := by
  induction columns generalizing references with
  | nil => simp
  | cons first rest ih =>
      simp only [CoreSQL.joinProjection] at success
      cases head : CoreSQL.joinResultColumn context first with
      | error message => simp [head, bind, Except.bind] at success
      | ok output =>
          cases tail : CoreSQL.joinProjection context rest with
          | error message => simp [head, tail, bind, Except.bind] at success
          | ok outputs =>
              intro column member
              rcases List.mem_cons.mp member with rfl | member
              · exact joinColumn_noDeclaredCollation context column output head
              · exact ih outputs tail column member

theorem joinQueryBound_noDeclaredCollation (select : Select) (source : TableRef)
    (context : CoreSQL.JoinContext) (query : CoreJoin.Query)
    (success : CoreSQL.joinQueryBound select source context = .ok query) :
    ∀ column ∈ select.columns.toList, NoDeclaredCollation column.expr := by
  unfold CoreSQL.joinQueryBound at success
  simp only [bind, Except.bind, pure, Except.pure, CoreSQL.unsupported] at success
  repeat' (split at success)
  all_goals try contradiction
  all_goals exact joinProjection_noDeclaredCollation _ _ _ (by assumption)

theorem joinQuery_noDeclaredCollation (select : Select) (leftTable rightTable : String)
    (left right : Core.Schema) (query : CoreJoin.Query)
    (success : CoreSQL.joinQuery select leftTable rightTable left right = .ok query) :
    ∀ column ∈ select.columns.toList, NoDeclaredCollation column.expr := by
  unfold CoreSQL.joinQuery at success
  by_cases aliases : CoreSQL.joinAliasesNeeded select left right = true
  · simp [aliases, CoreSQL.unsupported, bind, Except.bind] at success
  simp [aliases, bind, Except.bind, pure, Except.pure] at success
  cases sources : select.sources.toList with
  | nil => simp [sources, bind, Except.bind, CoreSQL.unsupported] at success
  | cons first rest =>
    cases rest with
    | nil => simp [sources, bind, Except.bind, CoreSQL.unsupported] at success
    | cons second rest =>
      cases rest with
      | cons third rest => simp [sources, bind, Except.bind, CoreSQL.unsupported] at success
      | nil =>
        simp only [sources, bind, Except.bind, pure, Except.pure, CoreSQL.unsupported] at success
        repeat' (split at success)
        all_goals try contradiction
        all_goals exact joinQueryBound_noDeclaredCollation _ _ _ _ (by assumption)

end SQLeanite.CoreSQLReadText
