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

private theorem joinColumn_noCollation (context : CoreSQL.JoinContext) (column : ResultColumn)
    (references : List CoreJoin.ColumnRef)
    (success : CoreSQL.joinResultColumn context column = .ok references) :
    NoExplicitCollation column.expr := by
  fun_cases CoreSQL.joinResultColumn context column <;>
    simp_all [CoreSQL.joinResultColumn, CoreSQL.unsupported]
  all_goals intro fuel; cases fuel <;> rfl

theorem joinProjection_noCollation (context : CoreSQL.JoinContext)
    (columns : List ResultColumn) (references : List CoreJoin.ColumnRef)
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

theorem joinQuery_noCollation (select : Select) (leftTable rightTable : String)
    (left right : Core.Schema) (query : CoreJoin.Query)
    (success : CoreSQL.joinQuery select leftTable rightTable left right = .ok query) :
    ∀ column ∈ select.columns.toList, NoExplicitCollation column.expr := by
  unfold CoreSQL.joinQuery at success
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
        all_goals exact joinProjection_noCollation _ _ _ (by assumption)

end SQLeanite.CoreSQLReadText
