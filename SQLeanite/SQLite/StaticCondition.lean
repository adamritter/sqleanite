import SQLeanite.SQLite.Scalar
import SQLeanite.SQLite.FunctionSignatures

namespace SQLeanite.SQLite.StaticCondition

/-- Name/arity validation precedes code generation, including expressions whose
values will never be evaluated. Shared with ignored aggregate ordering. -/
def resolutionForbidden (expression : Expr) : Bool :=
  match expression with
  | .call name arguments star =>
      if name == "__sqlean_declared_collation" || name == "__sqlean_bound_value" then
        star || !(match arguments.toList with | [_, .literal (.text _) _] => true | _ => false)
      else
      let name := SQLite.Scalar.scalarFunctionName name
      star || arguments.size > SQLite.Limits.maxFunctionArgs ||
        !(if (SQLite.Scalar.booleanKeyword? expression).isSome then true
          else if name == "__sqlean_between" then arguments.size == 3
          else if name.startsWith "cast_" then arguments.size == 1
          else if SQLite.Probability.recognizesName name then (SQLite.Probability.input? name arguments).isSome
          else SQLite.FunctionSignatures.scalar name arguments.size)
  | .literal .. | .column .. | .unary .. | .binary .. | .collate .. | .isNull .. | .inList .. | .case_ .. => false
  | _ => true

theorem resolutionForbidden_declared (argument : Expr) (collation : String) :
    resolutionForbidden (ExprCollation.declared argument collation) = false := rfl

/-- Errors raised when SQLite emits a value/comparison operation. This check
is independent of whether the Core implements a function's value semantics. -/
def codegenForbidden : Expr → Bool
  | .literal (.real _) (some source) => source.toLower.startsWith "0x"
  | .unary .neg argument => Scalar.minimumHexLiteral argument
  | .case_ base branches _ => base.any fun base =>
      branches.any (fun branch => (ExprCollation.binaryKind? base branch.1).isNone)
  | .inList argument values _ _ => !values.isEmpty && (ExprCollation.kind? argument).isNone
  | .binary operation left right =>
      [.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains operation &&
        !([.is, .isNot].contains operation && (Scalar.isTruthKeyword? right).isSome) &&
        (ExprCollation.binaryKind? left right).isNone
  | .call "__sqlean_between" arguments false =>
      match arguments.toList with
      | [argument, lower, upper] =>
          (ExprCollation.binaryKind? argument lower).isNone || (ExprCollation.binaryKind? argument upper).isNone
      | _ => true
  | .call name arguments _ =>
      ["min", "max", "nullif"].contains (Scalar.scalarFunctionName name) &&
        (ExprCollation.argumentsKind? arguments).isNone
  | _ => false

/-- The scalar AND/OR simplifier omits code for statically decided subtrees.
Name resolution always inspects the original prepared tree separately. This
transformation is used only to validate operations that would be generated. -/
def generatedFuel : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
      let generate := generatedFuel fuel
      match expression with
      | .binary operation left right =>
          let ordinary := Expr.binary operation (generate left) (generate right)
          if operation == .and || operation == .or then
            match Scalar.staticTruth expression with
            | some truth => .literal (.integer (if truth then 1 else 0))
            | none => ordinary
          else ordinary
      | .unary operation argument => .unary operation (generate argument)
      | .call name arguments star => .call name (arguments.map generate) star
      | .isNull argument negated => .isNull (generate argument) negated
      | .inList argument values negated affinity =>
          .inList (generate argument) (values.map generate) negated affinity
      | .collate argument name => .collate (generate argument) name
      | .case_ base branches otherwise => .case_ (base.map generate)
          (branches.map (fun (condition, result) => (generate condition, generate result))) (otherwise.map generate)
      | .inSubquery argument sql negated => .inSubquery (generate argument) sql negated
      | _ => expression

def codegenAdmitted (expression : Expr) (outer : Bool := false) : Bool :=
  !(if outer then expression else generatedFuel expression.height expression).any codegenForbidden

/-- A leading false term stops runtime testing. An earlier unknown term prevents
compile-time replacement, even if a later term is false. -/
def staticTerms? : List Expr → Option Bool
  | [] => some true
  | expression :: rest => match Scalar.staticTruth expression with
    | some false => some false
    | some true => staticTerms? rest
    | none => none

theorem testTerm_static (lookup : Option String → String → Except String Value)
    (affinity : Expr → Option Affinity) (constant : Expr → Bool)
    (expression : Expr) (truth : Bool) (known : Scalar.staticTruth expression = some truth) :
    Scalar.testFuelWithConstants lookup affinity constant expression.height true expression = .ok truth := by
  have positive := expression.height_positive
  cases size : expression.height with
  | zero => omega
  | succ fuel =>
      cases truth <;>
        simp [Scalar.testFuelWithConstants, Scalar.branchFuelWithConstants, Scalar.testEvaluatedFuel, known, pure, Except.pure]

theorem staticTerms_correct (lookup : Option String → String → Except String Value)
    (affinity : Expr → Option Affinity) (constant : Expr → Bool)
    (expressions : List Expr) (truth : Bool) (known : staticTerms? expressions = some truth) :
    Scalar.testTermsWithConstants lookup affinity constant expressions = .ok truth := by
  induction expressions with
  | nil =>
      simp only [staticTerms?, Option.some.injEq] at known
      subst truth
      rfl
  | cons expression rest ih =>
      cases first : Scalar.staticTruth expression with
      | none => simp [staticTerms?, first] at known
      | some value =>
          have evaluated := testTerm_static lookup affinity constant expression value first
          cases value with
          | false =>
              have result : truth = false := by simpa [staticTerms?, first] using known.symm
              subst truth
              simp [Scalar.testTermsWithConstants, evaluated, bind, Except.bind, pure, Except.pure]
          | true =>
              have tail := ih (by simpa [staticTerms?, first] using known)
              simp [Scalar.testTermsWithConstants, evaluated, tail, bind, Except.bind]

/-- An ordered logical decision keeps every unknown atom pending. A result
is known only when evaluation can stop before reaching any pending atom. -/
inductive Decision where
  | known (value : Bool)
  | pending (expression : Expr)
  | not (argument : Decision)
  | and (left right : Decision)
  | or (left right : Decision)

def Decision.result? : Decision → Option Bool
  | .known value => some value
  | .pending _ => none
  | .not argument => (! ·) <$> argument.result?
  | .and left right => left.result?.bind (fun value => if value then right.result? else some false)
  | .or left right => left.result?.bind (fun value => if value then some true else right.result?)

def Decision.run (atom : Expr → Except String Truth) : Decision → Except String Truth
  | .known value => .ok (if value then .true else .false)
  | .pending expression => atom expression
  | .not argument => Truth.not <$> argument.run atom
  | .and left right => do
      let first ← left.run atom
      if first == .false then return .false
      return Truth.and first (← right.run atom)
  | .or left right => do
      let first ← left.run atom
      if first == .true then return .true
      return Truth.or first (← right.run atom)

/-- Predicate branches need one truth outcome. An unknown left operand of
AND cannot lead to a true result, so a true-branch test stops before the RHS.
This differs from computing the complete three-valued scalar AND value. -/
def Decision.test (atom : Expr → Except String Truth) : Bool → Decision → Except String Bool
  | wanted, .known value => .ok (value == wanted)
  | wanted, .pending expression => do
      return (← atom expression) == (if wanted then .true else .false)
  | wanted, .not argument => argument.test atom (!wanted)
  | true, .and left right => do
      if ← left.test atom true then right.test atom true else return false
  | false, .and left right => do
      if ← left.test atom false then return true else right.test atom false
  | true, .or left right => do
      if ← left.test atom true then return true else right.test atom true
  | false, .or left right => do
      if ← left.test atom false then right.test atom false else return false

/-- Atomic predicates can provide their own true/false branch emission.
BETWEEN uses this to share its tested value and skip an unnecessary bound. -/
def Decision.testWith (atom : Expr → Bool → Except String Bool) : Bool → Decision → Except String Bool
  | wanted, .known value => .ok (value == wanted)
  | wanted, .pending expression => atom expression wanted
  | wanted, .not argument => argument.testWith atom (!wanted)
  | true, .and left right => do
      if ← left.testWith atom true then right.testWith atom true else return false
  | false, .and left right => do
      if ← left.testWith atom false then return true else right.testWith atom false
  | true, .or left right => do
      if ← left.testWith atom true then return true else right.testWith atom true
  | false, .or left right => do
      if ← left.testWith atom false then right.testWith atom false else return false

/-- Supplying scalar atoms recovers the previous decision test exactly. -/
theorem Decision.testWith_scalar (decision : Decision) (atom : Expr → Except String Truth)
    (wanted : Bool) :
    decision.testWith (fun expression requested => do
      return (← atom expression) == (if requested then .true else .false)) wanted =
      decision.test atom wanted := by
  induction decision generalizing wanted with
  | known value => rfl
  | pending expression => rfl
  | not argument ih => exact ih (!wanted)
  | and left right leftIH rightIH =>
      cases wanted <;> simp only [Decision.testWith, Decision.test, leftIH, rightIH]
  | or left right leftIH rightIH =>
      cases wanted <;> simp only [Decision.testWith, Decision.test, leftIH, rightIH]

theorem Decision.test_and_stops (atom : Expr → Except String Truth) (left right : Decision)
    (stopped : left.test atom true = .ok false) :
    (Decision.and left right).test atom true = .ok false := by
  simp [Decision.test, stopped, bind, Except.bind, pure, Except.pure]

theorem Decision.result_correct (decision : Decision) (value : Bool)
    (known : decision.result? = some value) (atom : Expr → Except String Truth) :
    decision.run atom = .ok (if value then .true else .false) := by
  induction decision generalizing value with
  | known result =>
      simp only [Decision.result?, Option.some.injEq] at known
      subst value
      rfl
  | pending expression => simp [Decision.result?] at known
  | not argument ih =>
      cases result : argument.result? with
      | none => simp [Decision.result?, result] at known
      | some truth =>
          have evaluated := ih truth result
          cases truth <;>
            simp [Decision.result?, result] at known <;> subst value <;>
            simp [Decision.run, evaluated, Functor.map, Except.map, Truth.not]
  | and left right leftIH rightIH =>
      cases first : left.result? with
      | none => simp [Decision.result?, first] at known
      | some truth =>
          have evaluated := leftIH truth first
          cases truth with
          | false =>
              simp [Decision.result?, first] at known
              subst value
              simp [Decision.run, evaluated, bind, Except.bind, pure, Except.pure]
          | true =>
              have remaining : right.result? = some value := by simpa [Decision.result?, first] using known
              have tail := rightIH value remaining
              cases value <;> simp [Decision.run, evaluated, tail, bind, Except.bind, pure, Except.pure, Truth.and]
  | or left right leftIH rightIH =>
      cases first : left.result? with
      | none => simp [Decision.result?, first] at known
      | some truth =>
          have evaluated := leftIH truth first
          cases truth with
          | false =>
              have remaining : right.result? = some value := by simpa [Decision.result?, first] using known
              have tail := rightIH value remaining
              cases value <;> simp [Decision.run, evaluated, tail, bind, Except.bind, pure, Except.pure, Truth.or]
          | true =>
              simp [Decision.result?, first] at known
              subst value
              simp [Decision.run, evaluated, bind, Except.bind, pure, Except.pure]

def decisionFuel : Nat → Expr → Decision
  | 0, expression => .pending expression
  | fuel + 1, expression =>
      let decide := decisionFuel fuel
      match expression with
      | .literal (.integer value) _ => .known (value != 0)
      | .unary .not argument => .not (decide argument)
      | .binary .and left right => .and (decide left) (decide right)
      | .binary .or left right => .or (decide left) (decide right)
      | _ => match Scalar.booleanKeyword? expression with
          | some truth => .known truth
          | none => .pending expression

def conditionDecision : List Expr → Decision
  | [] => .known true
  | expression :: rest => .and (decisionFuel expression.height expression) (conditionDecision rest)

/-- Outer-ON expressions carry EP_OuterON, disabling SQLite's symmetric
constant flags. Their runtime decision still short-circuits from left to right. -/
def classify (outer : Bool) (prepared : Expr) : Option Bool :=
  if outer then (conditionDecision (Scalar.conditionTerms prepared)).result?
  else staticTerms? (Scalar.conditionTerms prepared)

end SQLeanite.SQLite.StaticCondition
