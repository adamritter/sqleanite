import SQLeanite.SQLite.FunctionSignatures
import SQLeanite.SQLite.Probability
import SQLeanite.SQLite.Scalar.RealResult
import SQLeanite.SQLite.TextEncoding

namespace SQLeanite.SQLite.Scalar

def prepareFuel : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    let prepare := prepareFuel fuel
    match e with
    | .unary op arg => .unary op (prepare arg)
    | .binary op left right =>
        let a := prepare left
        let b := prepare right
        match op, b with
        | .is, .literal .null _ => prepareNullTest a false
        | .isNot, .literal .null _ => prepareNullTest a true
        | _, _ =>
          if op == .and && (parserFalse a || parserFalse b) &&
              !(hasFunction a || hasFunction b) then .literal (.integer 0)
          else .binary op a b
    | .call name args star =>
        let ignoredOrder := if name == "__sqlean_aggregate_order" && !star then
            match args.toList with
            | aggregate@(.call _ inputs false) :: _ :: _ => if inputs.isEmpty then some aggregate else none
            | _ => none
          else none
        match ignoredOrder with
        | some aggregate => prepare aggregate
        | none => .call name (args.map prepare)
            (star && !(["jsonb_extract", "jsonb_remove", "json_extract", "json_remove", "json_array", "jsonb_array", "json_object", "jsonb_object", "json_replace", "jsonb_replace", "json_insert", "jsonb_insert", "json_set", "jsonb_set", "json_array_insert", "jsonb_array_insert"].contains name.toLower && args.isEmpty))
    | .isNull arg negated => prepareNullTest (prepare arg) negated
    | .inList arg values negated affinity =>
        let argument := prepare arg
        if values.isEmpty then
          let result : Expr := .literal (.integer (if negated then 1 else 0))
          if hasFunction argument then
            .binary (if negated then .or else .and) result argument
          else result
        else
          let choices := values.map prepare
          match choices.toList with
          | [choice] =>
            if constantExpression choice && affinity then
              let equality := Expr.binary .eq argument (.unary .plus choice)
              if negated then .unary .not equality else equality
            else .inList argument choices negated affinity
          | _ => .inList argument choices negated affinity
    | .collate arg name => .collate (prepare arg) name
    | .case_ base branches otherwise => .case_ (base.map prepare)
        (branches.map fun pair => (prepare pair.1, prepare pair.2)) (otherwise.map prepare)
    | .inSubquery arg sql negated => .inSubquery (prepare arg) sql negated
    | _ => e

def prepare (expression : Expr) : Expr := prepareFuel expression.height expression

/-- DISTINCT is syntactically permitted on scalar calls but does not change
scalar evaluation. Internal CAST markers cannot be introduced by wrapping a
user-supplied function name in DISTINCT. -/
def scalarFunctionName (name : String) : String :=
  let base := aggregateFunctionName name
  if isDistinctAggregateName name && base.startsWith "cast_" then name.toLower
  else base

/-- A directly negated minimum hex literal is a preparation error in SQLite.
Unary plus is skipped; COLLATE and arithmetic form ordinary runtime operands. -/
def minimumHexLiteral : Expr → Bool
  | .literal (.integer value) (some source) =>
      value == Numeric.minInt && source.toLower.startsWith "0x"
  | .unary .plus expression => minimumHexLiteral expression
  | _ => false

/-- Admission is a syntax traversal, independent of evaluation success. In
particular, dead branches cannot hide column references or unsupported SQL. -/
def forbidden : Expr → Bool
  | .literal (.real _) (some source) => source.toLower.startsWith "0x"
  | .unary .neg expression => minimumHexLiteral expression
  | .literal _ _ | .unary _ _ | .isNull _ _ | .collate .. => false
  | .case_ base branches _ => base.any fun base =>
      branches.any fun branch => (ExprCollation.binaryKind? base branch.1).isNone
  | .inList argument values _ _ => !values.isEmpty && (ExprCollation.kind? argument).isNone
  | .binary op left right =>
      op == .match ||
        ([.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains op &&
          !(([.is, .isNot].contains op) && (isTruthKeyword? right).isSome) &&
          (ExprCollation.binaryKind? left right).isNone)
  | .call name args star =>
      let n := scalarFunctionName name
      (star && !Version.recognizes n && !DateTime.names.contains n) || args.size > Limits.maxFunctionArgs ||
        (["min", "max", "nullif"].contains n && (ExprCollation.argumentsKind? args).isNone) || !(if (booleanKeyword? (.call name args star)).isSome then true
        else if n == "__sqlean_encoded" then
          match args.toList with
          | [.literal (.text function) _,.literal (.integer encoding) _,_] =>
              ["context","input","stored","hex","octet_length","cast_blob","cast_text"].contains function && (encoding == 2 || encoding == 3)
          | _ => false
        else if n == "__sqlean_bound_value" || n == "__sqlean_declared_collation" then
          match args.toList with
          | [_, .literal (.text _) _] => true
          | _ => false
        else if n == "__sqlean_between" then
          match args.toList with
          | [argument, lower, upper] => (ExprCollation.binaryKind? argument lower).isSome &&
              (ExprCollation.binaryKind? argument upper).isSome
          | _ => false
        else if Probability.recognizesName n then (Probability.input? n args).isSome
        else if n == "format" || n == "printf" then true
        else if Math.accepts n args.size then true
        else if Version.recognizes n then args.isEmpty
        else if DateTime.names.contains n then true
        else if n == "timediff" then args.size == 2
        else if n == "coalesce" then args.size ≥ 2
        else if n == "ifnull" || n == "nullif" then args.size == 2
        else if n == "iif" || n == "if" then args.size ≥ 2
        else if ["char", "jsonb_extract", "jsonb_remove", "json_extract", "json_remove", "json_array", "jsonb_array", "json_object", "jsonb_object", "json_replace", "jsonb_replace", "json_insert", "jsonb_insert", "json_set", "jsonb_set", "json_array_insert", "jsonb_array_insert"].contains n then true
        else if n == "concat" then args.size ≥ 1
        else if ["concat_ws", "min", "max"].contains n then args.size ≥ 2
        else if ["substr", "substring"].contains n then args.size == 2 || args.size == 3
        else if ["trim", "ltrim", "rtrim", "unhex", "round", "json_valid", "json_type", "json_array_length", "json_pretty"].contains n then
          args.size == 1 || args.size == 2
        else if n == "like" then args.size == 2 || args.size == 3
        else if n == "instr" || n == "glob" || n == "->>" || n == "jsonb_patch" || n == "->" || n == "json_patch" then args.size == 2
        else if n == "replace" then args.size == 3
        else if n.startsWith "cast_" ||
          ["typeof", "abs", "length", "octet_length", "lower", "upper",
           "hex", "unicode", "quote", "unistr", "unistr_quote", "zeroblob", "sign", "json_error_position", "jsonb", "json", "subtype", "json_quote"].contains n
        then args.size == 1 else false)
  | _ => true

theorem forbidden_tooManyArguments (name : String) (args : Array Expr) (star : Bool)
    (tooMany : Limits.maxFunctionArgs < args.size) :
    forbidden (.call name args star) = true := by
  simp [forbidden, tooMany]

def admitted (e : Expr) : Bool := !(prepare e).any forbidden

/-- Preserve the spelling of the first invalid JSON call while visiting
all expression branches before evaluation. DISTINCT is a syntax marker. -/
def admissionErrorFuel : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, expression =>
      let check := admissionErrorFuel fuel
      match expression with
      | .call name arguments star =>
          let function := scalarFunctionName name
          let wrongArity := if Version.recognizes function then !arguments.isEmpty
            else if ["timediff", "->>", "jsonb_patch", "->", "json_patch", "json_group_object", "jsonb_group_object"].contains function then arguments.size != 2
            else if ["json_error_position", "jsonb", "json", "subtype", "json_quote", "json_group_array", "jsonb_group_array"].contains function then arguments.size != 1
            else arguments.size != 1 && arguments.size != 2
          if ["__sqlean_raise_ignore","__sqlean_raise_abort","__sqlean_raise_fail","__sqlean_raise_rollback"].contains function then
            some "RAISE() may only be used within a trigger-program"
          else if (Version.recognizes function || ["timediff", "json_valid", "json_type", "json_array_length", "json_error_position", "jsonb", "json_pretty", "->>", "jsonb_patch", "json", "subtype", "->", "json_patch", "json_quote", "json_group_array", "jsonb_group_array", "json_group_object", "jsonb_group_object"].contains function) &&
              ((star && !Version.recognizes function) || wrongArity) then
            let spelling := if isDistinctAggregateName name then
                (name.drop distinctAggregatePrefix.length).toString else name
            some s!"wrong number of arguments to function {spelling}()"
          else arguments.toList.findSome? check
      | .unary _ argument | .isNull argument _ | .collate argument _ |
          .inSubquery argument _ _ => check argument
      | .binary _ left right => (check left).orElse (fun _ => check right)
      | .inList argument values _ _ => (check argument).orElse
          (fun _ => values.toList.findSome? check)
      | .case_ base branches otherwise =>
          (base.bind check).orElse (fun _ =>
            (branches.toList.findSome? (fun pair => (check pair.1).orElse (fun _ => check pair.2))).orElse
              (fun _ => otherwise.bind check))
      | _ => none

def functionError : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, expression =>
      let visit := functionError fuel
      match expression with
      | .call "__sqlean_encoded" #[.literal (.text _) _,.literal (.integer _) _,argument] false => visit argument
      | .call "__sqlean_bound_value" #[argument, .literal (.text _) _] false |
          .call "__sqlean_declared_collation" #[argument, .literal (.text _) _] false => visit argument
      | .call name arguments _ =>
          let function := SQLite.Scalar.scalarFunctionName name
          let spelling := if isDistinctAggregateName name then
              (name.drop distinctAggregatePrefix.length).toString else name
          let overloads := SQLite.FunctionSignatures.entries.filter (fun entry => entry.1 == function)
          if ["__sqlean_raise_ignore","__sqlean_raise_abort","__sqlean_raise_fail","__sqlean_raise_rollback"].contains function then
            some "RAISE() may only be used within a trigger-program"
          else if (SQLite.Scalar.booleanKeyword? expression).isSome ||
              (SQLite.Scalar.quotedIdentifier? expression).isSome || function.startsWith "cast_" ||
              function == "__sqlean_between" then arguments.toList.findSome? visit
          else if overloads.isEmpty then some s!"no such function: {spelling}"
          else if !overloads.any (fun entry => SQLite.FunctionSignatures.matchesArity entry.2.2 arguments.size) then
            some s!"wrong number of arguments to function {spelling}()"
          else arguments.toList.findSome? visit
      | .unary _ argument | .isNull argument _ | .collate argument _ => visit argument
      | .binary _ left right => (visit left).orElse (fun _ => visit right)
      | .inList argument values _ _ => (visit argument).orElse (fun _ => values.toList.findSome? visit)
      | .case_ base branches otherwise =>
          (base.bind visit).orElse (fun _ =>
            (branches.toList.findSome? (fun (condition,result) => (visit condition).orElse (fun _ => visit result))).orElse
              (fun _ => otherwise.bind visit))
      | _ => none

theorem functionError_boundValue (fuel : Nat) (argument : Expr) (declared : String) :
    functionError (fuel + 1) (.call "__sqlean_bound_value"
      #[argument, .literal (.text declared)] false) = functionError fuel argument := rfl

def admissionError (expression : Expr) : Option String :=
  let expression := prepare expression
  admissionErrorFuel expression.height expression

/-- Aggregate calls in scalar-only contexts fail at name resolution, even
when the statement would visit no input row. MIN/MAX have scalar overloads. -/
def aggregateMisuseFuel : Nat → Expr → Option String
  | 0, _ => none
  | fuel+1, expression =>
      let check := aggregateMisuseFuel fuel
      match expression with
      | .call name arguments star =>
          let function := scalarFunctionName name
          let aggregate := ["count", "sum", "avg", "total", "min", "max", "group_concat", "string_agg",
            "median", "percentile", "percentile_cont", "percentile_disc", "json_group_array", "jsonb_group_array", "json_group_object", "jsonb_group_object"].contains function &&
              !(["min", "max"].contains function && arguments.size ≥ 2 && !star)
          if aggregate then
            let spelling := if isDistinctAggregateName name then
                (name.drop distinctAggregatePrefix.length).toString else name
            let valid := FunctionSignatures.entries.any (fun entry =>
              entry.1 == function && !entry.2.1 && FunctionSignatures.matchesArity entry.2.2 arguments.size)
            if !valid || (star && function != "count") then
              some s!"wrong number of arguments to function {spelling}()"
            else some s!"misuse of aggregate function {spelling}()"
          else arguments.toList.findSome? check
      | .unary _ argument | .isNull argument _ | .collate argument _ |
          .inSubquery argument _ _ => check argument
      | .binary _ left right => (check left).orElse (fun _ => check right)
      | .inList argument values _ _ => (check argument).orElse (fun _ => values.toList.findSome? check)
      | .case_ base branches otherwise =>
          (base.bind check).orElse (fun _ =>
            (branches.toList.findSome? (fun pair => (check pair.1).orElse (fun _ => check pair.2))).orElse
              (fun _ => otherwise.bind check))
      | _ => none

def aggregateMisuse (expression : Expr) : Option String :=
  let expression := prepare expression
  aggregateMisuseFuel expression.height expression

/-- Preserve quoted-token diagnostics before name binding discards that
syntax marker. The resolver supplies its actual visible column set. -/
def nameErrorFuel (bound : Option String → String → Bool) : Nat → Expr → Option String
  | 0, _ => none
  | fuel+1, expression =>
      let check := nameErrorFuel bound fuel
      if let some name := quotedIdentifier? expression then
        if bound none name then none
        else some ("no such column: \"" ++ name ++ "\" - should this be a string literal in single-quotes?")
      else match expression with
      | .column qualifier name =>
          if bound qualifier name then none
          else some ("no such column: " ++ (qualifier.map (· ++ ".") |>.getD "") ++ name)
      | .call _ arguments _ => arguments.toList.findSome? check
      | .unary _ argument | .isNull argument _ | .collate argument _ |
          .inSubquery argument _ _ => check argument
      | .binary _ left right => (check left).orElse (fun _ => check right)
      | .inList argument values _ _ => (check argument).orElse (fun _ => values.toList.findSome? check)
      | .case_ base branches otherwise =>
          (base.bind check).orElse (fun _ =>
            (branches.toList.findSome? (fun pair => (check pair.1).orElse (fun _ => check pair.2))).orElse
              (fun _ => otherwise.bind check))
      | _ => none

def nameError (bound : Option String → String → Bool) (expression : Expr) : Option String :=
  let expression := prepare expression
  nameErrorFuel bound expression.height expression

/-- SQLite's resolver carries a diagnostic independently of the walk's
abort flag. Function callbacks walk their arguments and return WRC_Prune even
after an argument error. Name lookup can abort; ordinary nodes abort when an
earlier callback already recorded an error. See resolve.c and walker.c. -/
structure ResolutionDiagnostic where
  message : Option String := none
  aborted : Bool := false

def resolutionList (visit : Expr → Option String → ResolutionDiagnostic) :
    Option String → List Expr → ResolutionDiagnostic
  | message, [] => { message }
  | message, first :: rest =>
      let result := visit first message
      if result.aborted then result else resolutionList visit result.message rest

def resolutionErrorFuel (bound : Option String → String → Bool) :
    Nat → Expr → Option String → ResolutionDiagnostic
  | 0, _, message => { message }
  | fuel+1, expression, message =>
      let visit := resolutionErrorFuel bound fuel
      if (quotedIdentifier? expression).isSome then
        match nameErrorFuel bound 1 expression with
        | some failure => { message := some failure, aborted := true }
        | none => { message }
      else match expression with
      | .column .. =>
          match nameErrorFuel bound 1 expression with
          | some failure => { message := some failure, aborted := true }
          | none => { message }
      | .call name arguments _ =>
          if name.startsWith "cast_" || name == "__sqlean_between" then
            if message.isSome then { message, aborted := true }
            else resolutionList visit message arguments.toList
          else
            let initial := (admissionErrorFuel 1 expression).orElse (fun _ => message)
            let result := resolutionList visit initial arguments.toList
            { message := result.message }
      | _ =>
          if message.isSome then { message, aborted := true }
          else match expression with
          | .unary _ argument | .isNull argument _ | .collate argument _ |
              .inSubquery argument _ _ => visit argument message
          | .binary _ left right => resolutionList visit message [left, right]
          | .inList argument values _ _ => resolutionList visit message (argument :: values.toList)
          | .case_ base branches otherwise =>
              resolutionList visit message (base.toList ++
                branches.toList.flatMap (fun pair => [pair.1, pair.2]) ++ otherwise.toList)
          | _ => { message }

def resolutionError (bound : Option String → String → Bool) (expression : Expr) : Option String :=
  let expression := prepare expression
  (resolutionErrorFuel bound expression.height expression none).message

theorem resolutionErrorFuel_call_arguments (bound : Option String → String → Bool)
    (fuel : Nat) (name : String) (arguments : Array Expr) (star : Bool) (message : Option String)
    (ordinary : quotedIdentifier? (.call name arguments star) = none)
    (notOperator : (name.startsWith "cast_" || name == "__sqlean_between") = false) :
    resolutionErrorFuel bound (fuel+1) (.call name arguments star) message =
      { message := (resolutionList (resolutionErrorFuel bound fuel)
          ((admissionErrorFuel 1 (.call name arguments star)).orElse (fun _ => message))
          arguments.toList).message } := by
  simp [resolutionErrorFuel, ordinary, notOperator]

theorem resolutionErrorFuel_pending_literal (bound : Option String → String → Bool)
    (fuel : Nat) (value : Value) (source : Option String) (message : String) :
    resolutionErrorFuel bound (fuel+1) (.literal value source) (some message) =
      { message := some message, aborted := true } := by
  simp [resolutionErrorFuel, quotedIdentifier?]

theorem nameError_collapsed (bound : Option String → String → Bool) (expression : Expr)
    (collapsed : prepare expression = .literal (.integer 0)) : nameError bound expression = none := by
  simp [nameError, collapsed, nameErrorFuel, quotedIdentifier?, Expr.height]

theorem admissionErrorFuel_binary_left (fuel : Nat) (operation : BinaryOp)
    (left right : Expr) (message : String)
    (failed : admissionErrorFuel fuel left = some message) :
    admissionErrorFuel (fuel+1) (.binary operation left right) = some message := by
  simp [admissionErrorFuel, failed]

/-- expr.c's EP_IsTrue/EP_IsFalse and sqlite3ExprSimplifiedAndOr. Only
nonnegative 32-bit integer literals acquire these flags; +0, -0, 0.0 and
numeric strings do not. This preserves SQLite's observable error suppression. -/
def staticTruth : Expr → Option Bool
  | expression@(.call ..) => booleanKeyword? expression
  | .literal (.integer i) => if 0 ≤ i && i ≤ 2147483647 then some (i != 0) else none
  | .binary .and a b =>
      match staticTruth a, staticTruth b with
      | some false, _ | _, some false => some false
      | some true, some true => some true
      | _, _ => none
  | .binary .or a b =>
      match staticTruth a, staticTruth b with
      | some true, _ | _, some true => some true
      | some false, some false => some false
      | _, _ => none
  | _ => none

def firstNonNull (eval : Expr → Except String Value) : List Expr → Except String Value
  | [] => .ok .null
  | x :: xs => do
      let v ← eval x
      if isNull v then firstNonNull eval xs else return v

def conditional (eval : Expr → Except String Value) (test : Expr → Except String Bool) : List Expr → Except String Value
  | [] => .ok .null
  | [last] => eval last
  | condition :: result :: rest => do
      if ← test condition then eval result else conditional eval test rest

def branches (eval : Expr → Except String Value) (test : Expr → Except String Bool)
    (equal : Expr → Expr → Value → Value → Value) (base : Option (Expr × Value))
    (otherwise : Option Expr) : List (Expr × Expr) → Except String Value
  | [] => match otherwise with | none => .ok .null | some e => eval e
  | (condition, result) :: rest => do
      let selected ← match base with
        | none => test condition
        | some (expression, b) => do
            pure (equal expression condition b (← eval condition) == .integer 1)
      if selected then eval result else branches eval test equal base otherwise rest

def membership (collation : Collation.Kind) (affinity : Affinity) (left : Value) : List Value → Bool → Truth
  | [], sawNull => if sawNull then .unknown else .false
  | value :: values, sawNull =>
      let equal := comparisonWith collation .eq (applyComparisonAffinity affinity left)
        (applyComparisonAffinity affinity value)
      if equal == .integer 1 then .true
      else membership collation affinity left values (sawNull || isNull value)

def linearMembership (eval : Expr → Except String Value) (collation : Collation.Kind) (affinity : Affinity)
    (left : Value) : List Expr → Bool → Except String Truth
  | [], sawNull => .ok (if sawNull then .unknown else .false)
  | expression :: expressions, sawNull => do
      let value ← eval expression
      let equal := comparisonWith collation .eq (applyComparisonAffinity affinity left)
        (applyComparisonAffinity affinity value)
      if equal == .integer 1 then return .true
      else linearMembership eval collation affinity left expressions (sawNull || isNull value)

def evalInList (eval : Expr → Except String Value) (operandAffinity : Expr → Option Affinity)
    (constant : Expr → Bool) (argument : Expr) (values : Array Expr) (negated applyLeftAffinity : Bool) :
    Except String Value := do
  if values.isEmpty then return boolValue negated
  let collation ← ExprCollation.require (ExprCollation.kind? argument)
  let affinity := if applyLeftAffinity then (operandAffinity argument).getD .blob else .blob
  let truth ← if values.size > 2 && values.all constant then do
      let right ← values.toList.mapM eval
      let left ← eval argument
      pure (membership collation affinity left right (isNull left))
    else do
      let left ← eval argument
      linearMembership eval collation affinity left values.toList (isNull left)
  return (if negated then truth.not else truth).toValue

theorem evalInList_empty (eval : Expr → Except String Value)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool) (argument : Expr)
    (negated applyLeftAffinity : Bool) :
    evalInList eval operandAffinity constant argument #[] negated applyLeftAffinity =
      .ok (boolValue negated) := by
  simp [evalInList, pure, Except.pure]

/-- Scalar min returns the last equal argument; max keeps the first. NULL
propagates and numeric storage classes remain unchanged. -/
def minmaxWith (kind : Collation.Kind) (maximum : Bool) (first : Value) (rest : List Value) : Value :=
  if isNull first || rest.any isNull then .null
  else rest.foldl (fun best value =>
    let order := ExprCollation.compare kind best value
    if (if maximum then order == .lt else order != .lt) then value else best) first

/-- Code-generation negation of a numeric literal preserves REAL negative
zero and the decimal spelling of the signed INTEGER minimum. Unary plus is
transparent here, while other expression forms use runtime subtraction. -/
def negatedLiteral? : Expr → Option Value
  | .literal (.real value) spelling =>
      if value == 9223372036854775808.0 && spelling.any (fun source => source.toInt? == some 9223372036854775808) then
        some (.integer Numeric.minInt)
      else some (realResult (-value))
  | .unary .plus expression => negatedLiteral? expression
  | _ => none

/-- BETWEEN evaluates its tested value once, then uses the original operands'
affinity and collation independently for the lower and upper comparisons. -/
def evalBetween (evaluate : Expr → Except String Value)
    (operandAffinity : Expr → Option Affinity) (argument lower upper : Expr) : Except String Value := do
  let value ← evaluate argument
  let minimum ← evaluate lower
  let maximum ← evaluate upper
  binary .and (expressionComparisonWith operandAffinity .ge argument lower value minimum)
    (expressionComparisonWith operandAffinity .le argument upper value maximum)

/-- Branch emission shares the tested value while retaining SQL's distinct
true/false/NULL outcomes and the short-circuit order of the two comparisons. -/
def testBetween (evaluate : Expr → Except String Value)
    (operandAffinity : Expr → Option Affinity) (argument lower upper : Expr)
    (wanted : Bool) : Except String Bool := do
  let value ← evaluate argument
  let minimum ← evaluate lower
  let first := Numeric.truth (expressionComparisonWith operandAffinity .ge argument lower value minimum)
  if wanted && first != .true then return false
  if !wanted && first == .false then return true
  let maximum ← evaluate upper
  return Numeric.truth (expressionComparisonWith operandAffinity .le argument upper value maximum) ==
    (if wanted then .true else .false)

theorem evalBetween_argument_error (evaluate : Expr → Except String Value)
    (affinity : Expr → Option Affinity) (argument lower upper : Expr) (message : String)
    (failed : evaluate argument = .error message) :
    evalBetween evaluate affinity argument lower upper = .error message := by
  simp [evalBetween, failed, bind, Except.bind]

end SQLeanite.SQLite.Scalar
