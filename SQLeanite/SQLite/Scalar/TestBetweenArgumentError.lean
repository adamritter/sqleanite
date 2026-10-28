import SQLeanite.SQLite.Scalar.TypedValues

namespace SQLeanite.SQLite.Scalar

/-- IN keeps actual representations while retaining its original common
comparison affinity, NULL behavior and list evaluation order. -/
def membershipTyped (kind : Collation.Kind) (affinity : Affinity) (left : ScalarValue) :
    List ScalarValue → Bool → Truth
  | [], sawNull => if sawNull then .unknown else .false
  | value :: values, sawNull =>
      let equal := comparisonTypedWith kind .eq
        { left with value := applyComparisonAffinity affinity left.value }
        { value with value := applyComparisonAffinity affinity value.value }
      if equal == .integer 1 then .true
      else membershipTyped kind affinity left values (sawNull || isNull value.value)


def linearMembershipTyped (evaluate : Expr → Except String ScalarValue) (kind : Collation.Kind)
    (affinity : Affinity) (left : ScalarValue) : List Expr → Bool → Except String Truth
  | [], sawNull => .ok (if sawNull then .unknown else .false)
  | expression :: rest, sawNull => do
      let value ← evaluate expression
      let equal := comparisonTypedWith kind .eq
        { left with value := applyComparisonAffinity affinity left.value }
        { value with value := applyComparisonAffinity affinity value.value }
      if equal == .integer 1 then return .true
      else linearMembershipTyped evaluate kind affinity left rest (sawNull || isNull value.value)


def evalInListTyped (evaluate : Expr → Except String ScalarValue) (operandAffinity : Expr → Option Affinity)
    (constant : Expr → Bool) (argument : Expr) (values : Array Expr) (negated applyLeftAffinity : Bool) :
    Except String Value := do
  if values.isEmpty then return boolValue negated
  let kind ← ExprCollation.require (ExprCollation.kind? argument)
  let affinity := if applyLeftAffinity then (operandAffinity argument).getD .blob else .blob
  let truth ← if values.size > 2 && values.all constant then do
      let values ← values.toList.mapM evaluate
      let left ← evaluate argument
      pure (membershipTyped kind affinity left values (isNull left.value))
    else do
      let left ← evaluate argument
      linearMembershipTyped evaluate kind affinity left values.toList (isNull left.value)
  return (if negated then truth.not else truth).toValue


theorem evalInListTyped_empty (evaluate : Expr → Except String ScalarValue)
    (affinity : Expr → Option Affinity) (constant : Expr → Bool) (argument : Expr)
    (negated applyLeftAffinity : Bool) :
    evalInListTyped evaluate affinity constant argument #[] negated applyLeftAffinity = .ok (boolValue negated) := by
  simp [evalInListTyped, pure, Except.pure]


def evalBetweenTyped (evaluate : Expr → Except String ScalarValue)
    (affinity : Expr → Option Affinity) (argument lower upper : Expr) : Except String Value := do
  let value ← evaluate argument
  let minimum ← evaluate lower
  let maximum ← evaluate upper
  binary .and (expressionComparisonTypedWith affinity .ge argument lower value minimum)
    (expressionComparisonTypedWith affinity .le argument upper value maximum)


def testBetweenTyped (evaluate : Expr → Except String ScalarValue)
    (affinity : Expr → Option Affinity) (argument lower upper : Expr)
    (wanted : Bool) : Except String Bool := do
  let value ← evaluate argument
  let minimum ← evaluate lower
  let first := Numeric.truth (expressionComparisonTypedWith affinity .ge argument lower value minimum)
  if wanted && first != .true then return false
  if !wanted && first == .false then return true
  let maximum ← evaluate upper
  return Numeric.truth (expressionComparisonTypedWith affinity .le argument upper value maximum) ==
    (if wanted then .true else .false)


theorem testBetweenTyped_argument_error (evaluate : Expr → Except String ScalarValue)
    (affinity : Expr → Option Affinity) (argument lower upper : Expr) (wanted : Bool) (message : String)
    (failed : evaluate argument = .error message) :
    testBetweenTyped evaluate affinity argument lower upper wanted = .error message := by
  simp [testBetweenTyped, failed, bind, Except.bind]


def testEvaluatedTypedFuel (evaluate : Expr → Except String ScalarValue)
    (operandAffinity : Expr → Option Affinity) (transparentWrappers : Bool) :
    Nat → Bool → Expr → Except String Bool
  | 0, _, _ => .error "row predicate depth exhausted"
  | fuel + 1, wanted, expression => do
      if let some truth := staticTruth expression then
        return truth == wanted
      if transparentWrappers then
        if let .collate argument _ := expression then
          return ← testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel wanted argument
        if let .call name arguments false := expression then
          if let some argument := Probability.input? name arguments then
            return ← testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel wanted argument
      match expression with
      | .call "__sqlean_between" arguments false =>
          match arguments.toList with
          | [argument, lower, upper] => testBetweenTyped evaluate operandAffinity argument lower upper wanted
          | _ => .error "invalid BETWEEN operands"
      | .unary .not arg => testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel (!wanted) arg
      | .binary .and left right =>
          if wanted then
            if ← testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel true left then testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel true right
            else return false
          else
            if ← testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel false left then return true
            else testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel false right
      | .binary .or left right =>
          if wanted then
            if ← testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel true left then return true
            else testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel true right
          else
            if ← testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel false left then testEvaluatedTypedFuel evaluate operandAffinity transparentWrappers fuel false right
            else return false
      | _ => return Numeric.truth (← evaluate expression).value ==
          (if wanted then .true else .false)


def branchesNativeTyped (evaluate : Expr → Except String ScalarValue) (test : Expr → Except String Bool)
    (affinity : Expr → Option Affinity) (base : Option (Expr × ScalarValue))
    (otherwise : Option Expr) : List (Expr × Expr) → Except String ScalarValue
  | [] => match otherwise with | none => .ok (plainScalar .null) | some expression => evaluate expression
  | (condition,result) :: rest => do
      let selected ← match base with
        | none => test condition
        | some (expression,value) => do
            pure (expressionComparisonTypedWith affinity .eq expression condition value (← evaluate condition) == .integer 1)
      if selected then evaluate result else branchesNativeTyped evaluate test affinity base otherwise rest

inductive QueryKind where
  | scalar | exists | membership
  deriving Repr, BEq, DecidableEq

/-- Query callbacks distinguish row existence and set membership from a scalar
value. IN's left operand has already been evaluated exactly once. -/
structure QueryRequest where
  kind : QueryKind
  source : String
  value : Value := .null
  typedValue : Option ScalarValue := none
  affinity : Option Affinity := none
  collation : Option String := none
  defaultCollation : Option String := none
  negated : Bool := false

def evalTypedQueryFuelWithBuiltin (lookup : Option String → String → Except String ScalarValue)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool)
    (query : QueryRequest → Except String ScalarValue)
    (evaluateBuiltin : String → Array ScalarValue → Except String ScalarValue) :
    Nat → Expr → Except String ScalarValue
  | 0,_ => .error "scalar expression depth exhausted"
  | fuel+1,e =>
    let eval := evalTypedQueryFuelWithBuiltin lookup operandAffinity constant query evaluateBuiltin fuel
    let raw := fun expression => (·.value) <$> eval expression
    let test := fun condition =>
      testEvaluatedTypedFuel eval operandAffinity false condition.height true condition
    match e with
    | .literal value _ => .ok (plainScalar value)
    | .column qualifier name => lookup qualifier name
    | .scalarSubquery sql => query { kind := .scalar, source := sql }
    | .existsSubquery sql => query { kind := .exists, source := sql }
    | .inSubquery argument sql negated => do
        let value ← eval argument
        query {
          kind := .membership
          source := sql
          value := value.value
          typedValue := if value.encodedText.isSome then some value else none
          affinity := operandAffinity argument
          collation := ExprCollation.name argument
          defaultCollation := ExprCollation.effectiveName argument
          negated := negated }
    | .collate argument _ => eval argument
    | .unary .plus argument => eval argument
    | .unary .neg argument =>
        match negatedLiteral? argument with
        | some value => .ok (plainScalar value)
        | none => (fun value => plainScalar (unary .neg value.value)) <$> eval argument
    | .unary op argument => (fun value => plainScalar (unary op value.value)) <$> eval argument
    | .binary .arrow left right => do
        let left ← raw left
        let right ← raw right
        JsonText.arrow left right
    | .binary .concat left right => do
        let encoding := ((ExprCollation.encodingHint left).orElse (fun _ => ExprCollation.encodingHint right)).getD 1
        concatTyped encoding (← eval left) (← eval right)
    | .binary op left right => do
        if op == .and || op == .or then
          if let some truth := staticTruth e then return plainScalar (boolValue truth)
        let typedA ← eval left
        let a := typedA.value
        if op == .is || op == .isNot then
          if let some truth := isTruthKeyword? right then return plainScalar (isTruth a truth (op == .isNot))
        let typedB ← eval right
        let b := typedB.value
        if [.eq,.ne,.lt,.le,.gt,.ge,.is,.isNot].contains op then
          return plainScalar (expressionComparisonTypedWith operandAffinity op left right typedA typedB)
        plainScalar <$> binary op a b
    | .isNull argument negated => do return plainScalar (boolValue (Text.isNull (← raw argument) != negated))
    | .inList argument values negated applyLeftAffinity =>
        plainScalar <$> evalInListTyped eval operandAffinity constant argument values negated applyLeftAffinity
    | .call name args true =>
        if args.isEmpty then
          match Version.value? (scalarFunctionName name) with
          | some value => .ok (plainScalar value)
          | none => if DateTime.names.contains (scalarFunctionName name) then
              evaluateBuiltin (scalarFunctionName name) #[]
            else .error "unsupported constant expression"
        else .error "unsupported constant expression"
    | .call name args false =>
        let n := scalarFunctionName name
        if let some truth := booleanKeyword? e then .ok (plainScalar (boolValue truth))
        else if n == "__sqlean_bound_value" || n == "__sqlean_declared_collation" then
          match args.toList with
          | [argument, .literal (.text _) _] => eval argument
          | [argument, .literal (.text _) _, .literal (.integer subtype) _] => do
              let value ← eval argument
              return { value with subtype := UInt8.ofNat subtype.toNat }
          | _ => .error "invalid bound-column annotation"
        else if n == "__sqlean_between" then
          match args.toList with
          | [argument,lower,upper] => plainScalar <$> evalBetweenTyped eval operandAffinity argument lower upper
          | _ => .error "invalid BETWEEN operands"
        else if let some argument := Probability.input? name args then eval argument
        else if n == "coalesce" || n == "ifnull" then firstNonNullTyped eval args.toList
        else if n == "iif" || n == "if" then conditionalTyped eval test args.toList
        else if ["min","max","nullif"].contains n then do
          let kind ← ExprCollation.require (ExprCollation.encodedArgumentsKind? args)
          let values ← args.mapM eval
          match n,values.toList with
          | "nullif",[a,b] => return if compareTyped kind a b == .eq then plainScalar .null else a
          | "min",first :: rest => return minmaxTyped kind false first rest
          | "max",first :: rest => return minmaxTyped kind true first rest
          | _,_ => evaluateBuiltin n values
        else do evaluateBuiltin n (← args.mapM eval)
    | .case_ base cases otherwise => do
        let base ← base.mapM (fun e => do return (e,← eval e))
        branchesNativeTyped eval test operandAffinity base otherwise cases.toList
    | _ => .error "unsupported constant expression"

/-- Existing scalar callers use the same builtins as before. Schema
programs can supply a context that rejects host-dependent calls at evaluation. -/
def evalTypedQueryFuelWithConstants (lookup : Option String → String → Except String ScalarValue)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool)
    (query : QueryRequest → Except String ScalarValue) : Nat → Expr → Except String ScalarValue :=
  evalTypedQueryFuelWithBuiltin lookup operandAffinity constant query builtinTyped

def evalTypedWithBuiltin (lookup : Option String → String → Except String ScalarValue)
    (operandAffinity : Expr → Option Affinity)
    (evaluateBuiltin : String → Array ScalarValue → Except String ScalarValue)
    (expression : Expr) : Except String ScalarValue :=
  let expression := prepare expression
  evalTypedQueryFuelWithBuiltin lookup operandAffinity constantExpression
    (fun _ => .error "unsupported constant expression") evaluateBuiltin expression.height expression

/-- Existing scalar callers retain a closed evaluator. Query-aware contexts
supply a pure callback, invoked only when the scalar branch is evaluated. -/
def evalTypedFuelWithConstants (lookup : Option String → String → Except String ScalarValue)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool) :
    Nat → Expr → Except String ScalarValue :=
  evalTypedQueryFuelWithConstants lookup operandAffinity constant
    (fun _ => .error "unsupported constant expression")

def evalTypedQueryWith (lookup : Option String → String → Except String ScalarValue)
    (operandAffinity : Expr → Option Affinity) (query : QueryRequest → Except String ScalarValue)
    (e : Expr) : Except String ScalarValue :=
  let expression := prepare e
  evalTypedQueryFuelWithConstants lookup operandAffinity constantExpression query expression.height expression

theorem evalTypedQueryFuelWithConstants_subquery
    (lookup : Option String → String → Except String ScalarValue)
    (affinity : Expr → Option Affinity) (constant : Expr → Bool)
    (query : QueryRequest → Except String ScalarValue) (fuel : Nat) (sql : String) :
    evalTypedQueryFuelWithConstants lookup affinity constant query (fuel + 1) (.scalarSubquery sql) = query { kind := .scalar, source := sql } := rfl

def evalFuelWithConstants (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool) :
    Nat → Expr → Except String Value := fun fuel expression =>
  (·.value) <$> evalTypedFuelWithConstants
    (fun qualifier name => plainScalar <$> lookup qualifier name) operandAffinity constant fuel expression

/-- Runtime slots carry subtype metadata; physical column readers wrap stored
values with subtype zero before entering this evaluator. -/
def evalTypedWith (lookup : Option String → String → Except String ScalarValue)
    (operandAffinity : Expr → Option Affinity) (e : Expr) : Except String ScalarValue :=
  let expression := prepare e
  evalTypedFuelWithConstants lookup operandAffinity constantExpression expression.height expression

/-- HAVING branches may inspect metadata retained by aggregate result slots. -/
def testBranchTypedWith (lookup : Option String → String → Except String ScalarValue)
    (operandAffinity : Expr → Option Affinity) : Nat → Bool → Expr → Except String Bool :=
  testEvaluatedTypedFuel (evalTypedWith lookup operandAffinity) operandAffinity false

def evalFuelWith (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) : Nat → Expr → Except String Value :=
  evalFuelWithConstants lookup operandAffinity constantExpression

def evalFuel : Nat → Expr → Except String Value :=
  evalFuelWith (fun _ _ => .error "unsupported constant expression") expressionAffinity

def eval (e : Expr) : Except String Value :=
  let expression := prepare e
  evalFuel expression.height expression

/-- The same evaluator with explicit column and affinity inputs. Admission and
name resolution are checked independently before any row is evaluated. -/
def evalWithConstants (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool)
    (e : Expr) : Except String Value :=
  let expression := prepare e
  evalFuelWithConstants lookup operandAffinity constant expression.height expression

def evalWith (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (e : Expr) : Except String Value :=
  evalWithConstants lookup operandAffinity constantExpression e

/-- Public WHERE/HAVING predicate evaluation shares the same branch rules
used by searched CASE and iif conditions. -/
def branchFuelWithConstants (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool) (transparentWrappers : Bool) :
    Nat → Bool → Expr → Except String Bool :=
  testEvaluatedFuel (evalWithConstants lookup operandAffinity constant) operandAffinity transparentWrappers

/-- WHERE planning exposes the underlying hinted/collated condition. -/
def testFuelWithConstants (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool) :
    Nat → Bool → Expr → Except String Bool :=
  branchFuelWithConstants lookup operandAffinity constant true

/-- HAVING and FILTER branch directly on their AST. A hint or COLLATE wrapper
therefore evaluates its operand as a scalar before testing truth. -/
def testBranchFuelWith (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) : Nat → Bool → Expr → Except String Bool :=
  branchFuelWithConstants lookup operandAffinity constantExpression false

def testFuelWith (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) : Nat → Bool → Expr → Except String Bool :=
  testFuelWithConstants lookup operandAffinity constantExpression

/-- where.c splits top-level AND into independent constraints before branch
code generation. Parenthesized AND has the same AST and is split too. -/
def conditionTerms : Expr → List Expr
  | .binary .and left right => conditionTerms left ++ conditionTerms right
  | expression => [expression]

def testTermsWithConstants (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool) : List Expr → Except String Bool
  | [] => .ok true
  | expression :: rest => do
      if ← testFuelWithConstants lookup operandAffinity constant expression.height true expression then
        testTermsWithConstants lookup operandAffinity constant rest
      else return false


def testTermsTypedWithConstants (lookup : Option String → String → Except String ScalarValue)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool) : List Expr → Except String Bool
  | [] => .ok true
  | expression :: rest => do
      let evaluate := fun expression =>
        evalTypedQueryFuelWithConstants lookup operandAffinity constant
          (fun _ => .error "unsupported constant expression") expression.height expression
      if ← testEvaluatedTypedFuel evaluate operandAffinity true expression.height true expression then
        testTermsTypedWithConstants lookup operandAffinity constant rest
      else return false

def testTermsWith (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) : List Expr → Except String Bool :=
  testTermsWithConstants lookup operandAffinity constantExpression

def testWhere (expression : Expr) : Except String Bool :=
  testTermsWith (fun _ _ => .error "unbound column") expressionAffinity (conditionTerms (prepare expression))

theorem evalWith_column (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (qualifier : Option String) (name : String) :
    evalWith lookup operandAffinity (.column qualifier name) = lookup qualifier name := by
  cases found : lookup qualifier name <;>
    simp [evalWith, evalWithConstants, evalFuelWithConstants, evalTypedFuelWithConstants, evalTypedQueryFuelWithConstants, evalTypedQueryFuelWithBuiltin,
      prepare, prepareFuel, Expr.height, found, plainScalar, JsonText.plain]

theorem evalWith_literal (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (value : Value) :
    evalWith lookup operandAffinity (.literal value) = .ok value := rfl

/-- The oversized negated hexadecimal literal is rejected before evaluation. -/
theorem forbidden_negated_minimum_hex (source : String)
    (hex : source.toLower.startsWith "0x" = true) :
    forbidden (.unary .neg (.literal (.integer Numeric.minInt) (some source))) = true := by
  simp [forbidden, minimumHexLiteral, hex]

theorem negatedLiteral_decimal_minimum (value : Float) (source : String)
    (magnitude : (value == 9223372036854775808.0) = true)
    (integerToken : (source.toInt? == some 9223372036854775808) = true) :
    negatedLiteral? (.literal (.real value) (some source)) =
      some (.integer Numeric.minInt) := by
  simp [negatedLiteral?, magnitude, integerToken]

/-- Reading a literal itself uses its value, irrespective of source spelling. -/

theorem evalWith_literal_spelling (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (value : Value) (spelling : Option String) :
    evalWith lookup operandAffinity (.literal value spelling) = .ok value := rfl

theorem checkedInteger_exact {i : Int} (fallback : Unit → Float)
    (lower : Numeric.minInt ≤ i) (upper : i ≤ Numeric.maxInt) :
    checkedInteger i fallback = .integer i := by
  simp [checkedInteger, (Numeric.fits_iff i).mpr ⟨lower, upper⟩]

theorem add_integer_exact (a b : Int)
    (lower : Numeric.minInt ≤ a + b) (upper : a + b ≤ Numeric.maxInt) :
    arithmetic .add (.integer a) (.integer b) = .integer (a + b) := by
  simp only [arithmetic, Numeric.arithmetic]
  exact checkedInteger_exact _ lower upper

theorem divide_integer_zero (a : Int) :
    arithmetic .div (.integer a) (.integer 0) = .null := by
  simp [arithmetic, Numeric.arithmetic]

theorem arithmetic_null_left (op : BinaryOp) (v : Value) :
    arithmetic op .null v = .null := rfl

theorem arithmetic_null_right (op : BinaryOp) (v : Value) :
    arithmetic op v .null = .null := by cases v <;> rfl

theorem shift_left_large {value amount : Int} (nonnegative : 0 ≤ amount)
    (large : 64 ≤ amount.natAbs) : shift true value amount = 0 := by
  simp [shift, Int.not_lt.mpr nonnegative, large]

theorem evalTyped_unary_plus (lookup : Option String → String → Except String ScalarValue)
    (affinity : Expr → Option Affinity) (constant : Expr → Bool) (fuel : Nat) (arg : Expr) :
    evalTypedFuelWithConstants lookup affinity constant (fuel+1) (.unary .plus arg) =
      evalTypedFuelWithConstants lookup affinity constant fuel arg := rfl

theorem evalTyped_collate (lookup : Option String → String → Except String ScalarValue)
    (affinity : Expr → Option Affinity) (constant : Expr → Bool) (fuel : Nat)
    (arg : Expr) (name : String) :
    evalTypedFuelWithConstants lookup affinity constant (fuel+1) (.collate arg name) =
      evalTypedFuelWithConstants lookup affinity constant fuel arg := rfl

theorem evalTypedWith_column (lookup : Option String → String → Except String ScalarValue)
    (affinity : Expr → Option Affinity) (qualifier : Option String) (name : String) :
    evalTypedWith lookup affinity (.column qualifier name) = lookup qualifier name := rfl

end SQLeanite.SQLite.Scalar
