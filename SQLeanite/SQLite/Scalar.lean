import SQLeanite.Syntax
import SQLeanite.SQLite.Numeric
import SQLeanite.SQLite.Type
import SQLeanite.SQLite.Text
import SQLeanite.SQLite.UnicodeEscape
import SQLeanite.SQLite.Pattern
import SQLeanite.SQLite.ExprCollation
import SQLeanite.SQLite.Probability

/-!
Pure SQLite scalar operations. Arithmetic/bit operations follow vdbe.c;
CAST follows vdbemem.c; the small built-in set follows func.c. The evaluator
uses the parsed expression tree instead of pretending to be a complete VDBE.
Column affinity is supplied by the row context; explicit expression collations
use the pinned built-in byte comparators.
-/
namespace SQLeanite.SQLite.Scalar

def realResult (r : Float) : Value := if r.isNaN then .null else .real r

/-- Overflow retries the operation in binary64 using the original operands,
as OP_Add/Subtract/Multiply do (not by rounding the exact integer result). -/
def checkedInteger (i : Int) (fallback : Unit → Float) : Value :=
  if Numeric.fits i then .integer i else realResult (fallback ())

def floating (op : BinaryOp) (left right : Value) : Value :=
  let a := Numeric.real left
  let b := Numeric.real right
  match op with
  | .add => realResult (a + b)
  | .sub => realResult (a - b)
  | .mul => realResult (a * b)
  | .div => if b == 0.0 then .null else realResult (a / b)
  | .mod =>
      let divisor := Numeric.integer right
      if divisor == 0 then .null
      else .real (Float.ofInt ((Numeric.integer left).tmod divisor))
  | _ => .null

def arithmetic (op : BinaryOp) (left right : Value) : Value :=
  match left, right with
  | .null, _ | _, .null => .null
  | _, _ =>
    match Numeric.arithmetic left, Numeric.arithmetic right with
    | .integer a, .integer b =>
      match op with
      | .add => checkedInteger (a + b) (fun _ => Numeric.real left + Numeric.real right)
      | .sub => checkedInteger (a - b) (fun _ => Numeric.real left - Numeric.real right)
      | .mul => checkedInteger (a * b) (fun _ => Numeric.real left * Numeric.real right)
      | .div => if b == 0 then .null else
          checkedInteger (a.tdiv b) (fun _ => Numeric.real left / Numeric.real right)
      | .mod => if b == 0 then .null else .integer (a.tmod b)
      | _ => .null
    | _, _ => floating op left right

/-- C's shift opcodes reverse direction for a negative count and saturate
counts >= 64, rather than using the hardware's count modulo 64. -/
def shift (leftward : Bool) (value amount : Int) : Int :=
  let leftward := if amount < 0 then !leftward else leftward
  let count := amount.natAbs
  if count ≥ 64 then if !leftward && value < 0 then -1 else 0
  else
    let word := Int64.ofInt value
    if leftward then (word <<< Int64.ofInt (Int.ofNat count)).toInt
    else (word >>> Int64.ofInt (Int.ofNat count)).toInt

def bitwise (op : BinaryOp) (left right : Value) : Value :=
  match left, right with
  | .null, _ | _, .null => .null
  | _, _ =>
    let a := Numeric.integer left
    let b := Numeric.integer right
    .integer (match op with
      | .bitAnd => ((Int64.ofInt a) &&& (Int64.ofInt b)).toInt
      | .bitOr => ((Int64.ofInt a) ||| (Int64.ofInt b)).toInt
      | .shiftLeft => shift true a b
      | .shiftRight => shift false a b
      | _ => 0)

def boolValue (b : Bool) : Value := .integer (if b then 1 else 0)

def isNull : Value → Bool | .null => true | _ => false

/-- Keep the original keyword spelling through name binding. These private
parser markers are certified only against bare TRUE/FALSE source tokens. -/
def booleanKeyword? : Expr → Option Bool
  | .call name arguments star =>
      if arguments.isEmpty && !star then
        if name == "__sqlean_boolean_true" then some true
        else if name == "__sqlean_boolean_false" then some false else none
      else none
  | _ => none

def booleanName (truth : Bool) : String := if truth then "true" else "false"

/-- Quoted tokens are identifiers in the pinned DQS-disabled configuration.
The parser's private marker must never be interpreted as an ordinary function. -/
def quotedIdentifier? : Expr → Option String
  | .call name arguments star =>
      if name == "lean_dqs" && !star then
        match arguments.toList with
        | [.literal (.text identifier)] => some identifier
        | _ => none
      else none
  | _ => none

def bindNamesFuel (hasColumn : String → Bool) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
      if let some truth := booleanKeyword? expression then
        if hasColumn (booleanName truth) then .column none (booleanName truth) else expression
      else if let some name := quotedIdentifier? expression then .column none name
      else
        let bind := bindNamesFuel hasColumn fuel
        match expression with
        | .unary op arg => .unary op (bind arg)
        | .binary op left right => .binary op (bind left) (bind right)
        | .call name args star => .call name (args.map bind) star
        | .isNull arg negated => .isNull (bind arg) negated
        | .inList arg values negated affinity => .inList (bind arg) (values.map bind) negated affinity
        | .case_ base branches otherwise => .case_ (base.map bind)
            (branches.map fun (condition, result) => (bind condition, bind result)) (otherwise.map bind)
        | .collate arg name => .collate (bind arg) name
        | .inSubquery arg sql negated => .inSubquery (bind arg) sql negated
        | _ => expression

def bindNames (hasColumn : String → Bool) (expression : Expr) : Expr :=
  bindNamesFuel hasColumn expression.height expression

/-- IS TRUE/FALSE tests truth without column affinity and always returns an
integer, including for NULL. IS NOT complements that two-valued result. -/
def isTruth (value : Value) (expected negated : Bool) : Value :=
  boolValue ((Numeric.truth value == (if expected then .true else .false)) != negated)

theorem isTruth_null (expected negated : Bool) :
    isTruth .null expected negated = boolValue negated := by
  cases expected <;> cases negated <;> rfl

theorem bindBooleanKeywords_shadowed (hasColumn : String → Bool) (truth : Bool)
    (bound : hasColumn (booleanName truth) = true) :
    bindNames hasColumn
      (.call (if truth then "__sqlean_boolean_true" else "__sqlean_boolean_false") #[] false) =
      .column none (booleanName truth) := by
  cases truth <;> simp_all [bindNames, bindNamesFuel, booleanKeyword?, booleanName,
    Expr.height, exprListHeight]

theorem bindNames_quoted (hasColumn : String → Bool) (name : String) :
    bindNames hasColumn (.call "lean_dqs" #[.literal (.text name)] false) =
      .column none name := by
  simp [bindNames, bindNamesFuel, booleanKeyword?, quotedIdentifier?, Expr.height, exprListHeight]

/-- Strict String extraction for callers that explicitly need valid UTF-8.
SQL TEXT conversions use Text.fromBytes and retain invalid byte sequences. -/
def text := SQLite.Text.toText

def comparisonWith (collation : Collation.Kind) (op : BinaryOp) (a b : Value) : Value :=
  if op == .is then boolValue (ExprCollation.compare collation a b == .eq)
  else if op == .isNot then boolValue (ExprCollation.compare collation a b != .eq)
  else if isNull a || isNull b then .null
  else
    let order := ExprCollation.compare collation a b
    boolValue (match op with
      | .eq => order == .eq | .ne => order != .eq
      | .lt => order == .lt | .le => order != .gt
      | .gt => order == .gt | .ge => order != .lt
      | _ => false)

def comparison := comparisonWith .binary

def unary (op : UnaryOp) (v : Value) : Value :=
  match op with
  | .plus => v
  | .neg => arithmetic .sub (.integer 0) v
  | .not => (Numeric.truth v).not.toValue
  | .bitNot => if isNull v then .null else .integer (~~~(Int64.ofInt (Numeric.integer v))).toInt

def binary (op : BinaryOp) (a b : Value) : Except String Value :=
  match op with
  | .add | .sub | .mul | .div | .mod => .ok (arithmetic op a b)
  | .bitAnd | .bitOr | .shiftLeft | .shiftRight => .ok (bitwise op a b)
  | .eq | .ne | .lt | .le | .gt | .ge | .is | .isNot => .ok (comparison op a b)
  | .and => .ok ((Numeric.truth a).and (Numeric.truth b)).toValue
  | .or => .ok ((Numeric.truth a).or (Numeric.truth b)).toValue
  | .like => Pattern.evaluate false b a
  | .glob => Pattern.evaluate true b a
  | .concat => do
      if isNull a || isNull b then return .null
      Text.append a b
  | _ => .error "unsupported scalar operator"

abbrev Affinity := SQLite.Affinity

/-- sqlite3AffinityType's precedence, including FLOATING POINT => INTEGER. -/
def affinity := SQLite.typeAffinity

def cast (typeName : String) (v : Value) : Except String Value := do
  if isNull v then return .null
  match affinity typeName with
  | .integer => return .integer (Numeric.integer v)
  | .real => return realResult (Numeric.real v)
  | .numeric => return Numeric.numerify v
  | .text => return Text.fromBytes (Text.bytes v)
  | .blob => return .blob (Text.bytes v)

/-- CAST is the constant-expression form that carries affinity. Unary plus
and other operators erase it, just as sqlite3ExprAffinity specifies. -/
def expressionAffinity : Expr → Option Affinity
  | .collate expression _ => expressionAffinity expression
  | .call name _ false =>
      if name.toLower.startsWith "cast_" then some (affinity (name.drop 5).toString) else none
  | _ => none

def numericAffinity : Affinity → Bool
  | .integer | .real | .numeric => true
  | _ => false

def comparisonAffinity (a b : Option Affinity) : Affinity :=
  match a, b with
  | some a, some b => if numericAffinity a || numericAffinity b then .numeric else .blob
  | some a, none | none, some a => a
  | none, none => .blob

/-- Comparison affinity is lossless: malformed text and BLOBs stay in their
original storage classes, in contrast to the forced CAST conversions. -/
def applyComparisonAffinity (aff : Affinity) (v : Value) : Value :=
  if numericAffinity aff then
    match v with
    | .text _ | .textBytes _ =>
        if (Numeric.parsePrefix (Numeric.numericText v)).completeToNul then Numeric.arithmetic v else v
    | _ => v
  else if aff == .text then
    match v with
    | .integer _ | .real _ => .text (toString v)
    | _ => v
  else v

def expressionComparisonWith (operandAffinity : Expr → Option Affinity)
    (op : BinaryOp) (left right : Expr) (a b : Value) : Value :=
  let aff := comparisonAffinity (operandAffinity left) (operandAffinity right)
  comparisonWith ((ExprCollation.binaryKind? left right).getD .binary) op
    (applyComparisonAffinity aff a) (applyComparisonAffinity aff b)

def expressionComparison := expressionComparisonWith expressionAffinity

def typeOf : Value → String
  | .null => "null" | .integer _ => "integer" | .real _ => "real"
  | .text _ | .textBytes _ => "text" | .blob _ => "blob"

/-- roundFunc clamps sqlite3_value_int64 precision before its floating branch. -/
def roundPrecision (places : Value) : Nat :=
  (max 0 (min 30 (Numeric.integer places))).toNat

theorem roundPrecision_le (places : Value) : roundPrecision places ≤ 30 := by
  unfold roundPrecision
  have h : max 0 (min 30 (Numeric.integer places)) ≤ 30 := by omega
  omega

/-- SQLite roundFunc, including half-away-from-zero integral rounding and
its fixed-decimal printf/parse path. Large magnitudes have no fractional bits. -/
def roundValue (value places : Value) : Value :=
  if isNull value || isNull places then .null
  else
    let n := roundPrecision places
    let r := Numeric.real value
    realResult (if r < -4503599627370496.0 || r > 4503599627370496.0 then r
      else if n == 0 then Float.ofInt (Numeric.realToInteger (r + (if r < 0.0 then -0.5 else 0.5)))
      else Numeric.realPrefix (FloatCodec.renderFixed r n))

theorem roundValue_null_left (places : Value) : roundValue .null places = .null := by
  simp [roundValue, isNull]

theorem roundValue_null_right (value : Value) : roundValue value .null = .null := by
  simp [roundValue, isNull]

def builtin (name : String) (args : Array Value) : Except String Value := do
  if name.startsWith "cast_" && args.size == 1 then
    return ← cast (name.drop 5).toString args[0]!
  match name, args.toList with
  | "like", [pattern, input] => Pattern.evaluate false pattern input
  | "like", [pattern, input, escape] => Pattern.evaluate false pattern input (some escape)
  | "glob", [pattern, input] => Pattern.evaluate true pattern input
  | "round", [v] => return roundValue v (.integer 0)
  | "round", [v, places] => return roundValue v places
  | "typeof", [v] => return .text (typeOf v)
  | "abs", [.integer i] =>
      if i == Numeric.minInt then throw "integer overflow"
      return .integer i.natAbs
  | "abs", [v] =>
      if isNull v then return .null
      let r := Numeric.real v
      return realResult (if r < 0.0 then -r else r)
  | "length", [v] =>
      match v with
      | .null => return .null
      | .blob bytes => return .integer bytes.size
      | _ => return .integer (Text.characterSpans (Text.bytes v)).length
  | "octet_length", [v] =>
      match v with
      | .null => return .null
      | .blob bytes => return .integer bytes.size
      | _ => return .integer (Text.bytes v).size
  | "lower", [v] | "upper", [v] =>
      Text.asciiCase (name == "upper") v
  | "nullif", [a, b] => return if a == b then .null else a
  | "hex", [v] => SQLite.Text.hex v
  | "unhex", [v] => SQLite.Text.unhex v (.text "")
  | "unhex", [v, ignored] => SQLite.Text.unhex v ignored
  | "substr", [v, start] | "substring", [v, start] =>
      SQLite.Text.substr v start (.integer 1000000000)
  | "substr", [v, start, count] | "substring", [v, start, count] =>
      SQLite.Text.substr v start count
  | "instr", [haystack, needle] => SQLite.Text.instr haystack needle
  | "trim", [v] => SQLite.Text.trim true true v (.text " ")
  | "ltrim", [v] => SQLite.Text.trim true false v (.text " ")
  | "rtrim", [v] => SQLite.Text.trim false true v (.text " ")
  | "trim", [v, chars] => SQLite.Text.trim true true v chars
  | "ltrim", [v, chars] => SQLite.Text.trim true false v chars
  | "rtrim", [v, chars] => SQLite.Text.trim false true v chars
  | "replace", [v, pattern, replacement] => SQLite.Text.replace v pattern replacement
  | "concat", values => SQLite.Text.concat "" values
  | "concat_ws", separator :: values => SQLite.Text.concatWs separator values
  | "unicode", [v] => SQLite.Text.unicode v
  | "char", values => SQLite.Text.charValue values
  | "quote", [v] => SQLite.Text.quote v
  | "unistr", [v] => SQLite.UnicodeEscape.unistr v
  | "unistr_quote", [v] => SQLite.UnicodeEscape.quote v
  | "zeroblob", [v] => SQLite.Text.zeroblob v
  | "sign", [v] => return SQLite.Text.sign v
  | "min", first :: rest => return SQLite.Text.minmax false first rest
  | "max", first :: rest => return SQLite.Text.minmax true first rest
  | _, _ => throw s!"unsupported scalar function or arity: {name}/{args.size}"

/-- SQLite's parse-time AND fold (expr.c sqlite3ExprAnd) is distinct from
later truth-code simplification. Literal zero may erase an unbound column,
but EP_HasFunc prevents erasing a function call and its errors. CAST is an
operator even though our surface AST encodes it as a named call.
Track the parser's EP_HasFunc propagation. sqlite3ExprAddCollateToken
constructs a new COLLATE node without propagating that flag from its child. -/
def hasFunctionFuel : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expression =>
      let has := hasFunctionFuel fuel
      match expression with
      | .collate .. => false
      | .call name args _ =>
          (!name.toLower.startsWith "cast_" && (booleanKeyword? expression).isNone &&
            (quotedIdentifier? expression).isNone) || args.any has
      | .unary _ arg | .isNull arg _ => has arg
      | .binary _ left right => has left || has right
      | .inList arg values _ _ => has arg || values.any has
      | .case_ base branches otherwise => base.any has ||
          branches.any (fun (condition, result) => has condition || has result) || otherwise.any has
      | .scalarSubquery .. | .inSubquery .. | .existsSubquery .. => true
      | _ => false

def hasFunction (expression : Expr) : Bool := hasFunctionFuel expression.height expression

theorem hasFunction_collate (expression : Expr) (name : String) :
    hasFunction (.collate expression name) = false := rfl

def parserFalse : Expr → Bool
  | .literal (.integer 0) => true
  | _ => false

/-- Every currently admitted scalar builtin is deterministic. An IN list
without row references is materialized first when it has more than two terms;
shorter or row-dependent lists use SQLite's comparison chain. -/
def constantExpression (expression : Expr) : Bool :=
  !expression.any (fun e => match e with
    | .column .. | .scalarSubquery .. | .inSubquery .. | .existsSubquery .. => true
    | _ => false)

def prepareFuel : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    let prepare := prepareFuel fuel
    match e with
    | .unary op arg => .unary op (prepare arg)
    | .binary op left right =>
        let a := prepare left
        let b := prepare right
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
        | none => .call name (args.map prepare) star
    | .isNull arg negated => .isNull (prepare arg) negated
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
      [.match, .arrow, .arrowText].contains op ||
        ([.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains op &&
          !(([.is, .isNot].contains op) && (booleanKeyword? right).isSome) &&
          (ExprCollation.binaryKind? left right).isNone)
  | .call name args star =>
      let n := scalarFunctionName name
      star || args.size > Limits.maxFunctionArgs ||
        (["min", "max", "nullif"].contains n && (ExprCollation.argumentsKind? args).isNone) || !(if (booleanKeyword? (.call name args star)).isSome then true
        else if Probability.recognizesName n then (Probability.input? n args).isSome
        else if n == "coalesce" then args.size ≥ 2
        else if n == "ifnull" || n == "nullif" then args.size == 2
        else if n == "iif" || n == "if" then args.size ≥ 2
        else if n == "char" then true
        else if n == "concat" then args.size ≥ 1
        else if ["concat_ws", "min", "max"].contains n then args.size ≥ 2
        else if ["substr", "substring"].contains n then args.size == 2 || args.size == 3
        else if ["trim", "ltrim", "rtrim", "unhex", "round"].contains n then
          args.size == 1 || args.size == 2
        else if n == "like" then args.size == 2 || args.size == 3
        else if n == "instr" || n == "glob" then args.size == 2
        else if n == "replace" then args.size == 3
        else if n.startsWith "cast_" ||
          ["typeof", "abs", "length", "octet_length", "lower", "upper",
           "hex", "unicode", "quote", "unistr", "unistr_quote", "zeroblob", "sign"].contains n
        then args.size == 1 else false)
  | _ => true

theorem forbidden_tooManyArguments (name : String) (args : Array Expr) (star : Bool)
    (tooMany : Limits.maxFunctionArgs < args.size) :
    forbidden (.call name args star) = true := by
  simp [forbidden, tooMany]

def admitted (e : Expr) : Bool := !(prepare e).any forbidden

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

def conditional (eval : Expr → Except String Value) : List Expr → Except String Value
  | [] => .ok .null
  | [last] => eval last
  | condition :: result :: rest => do
      if Numeric.truth (← eval condition) == .true then eval result else conditional eval rest

def branches (eval : Expr → Except String Value)
    (equal : Expr → Expr → Value → Value → Value) (base : Option (Expr × Value))
    (otherwise : Option Expr) : List (Expr × Expr) → Except String Value
  | [] => match otherwise with | none => .ok .null | some e => eval e
  | (condition, result) :: rest => do
      let v ← eval condition
      let selected : Bool := match base with
        | none => Numeric.truth v == .true
        | some (expression, b) =>
            equal expression condition b v == .integer 1
      if selected then eval result else branches eval equal base otherwise rest

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

/-- Fuel is supplied by the existing structural expression height. Recursing
through CASE/function arrays is total, with no unbounded interpreter binding. -/
def evalFuelWithConstants (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool) : Nat → Expr → Except String Value
  | 0, _ => .error "scalar expression depth exhausted"
  | fuel + 1, e =>
    let eval := evalFuelWithConstants lookup operandAffinity constant fuel
    match e with
    | .literal v _ => .ok v
    | .column qualifier name => lookup qualifier name
    | .collate argument _ => eval argument
    -- expr.c TK_UMINUS emits a negated REAL literal directly. OP_Subtract
    -- is used for other operands; only the literal case preserves -0.0.
    | .unary .neg argument =>
        match negatedLiteral? argument with
        | some value => .ok value
        | none => unary .neg <$> eval argument
    | .unary op arg => unary op <$> eval arg
    | .binary op a b => do
        if op == .and || op == .or then
          if let some truth := staticTruth e then return boolValue truth
        let left ← eval a
        if op == .is || op == .isNot then
          if let some truth := booleanKeyword? b then return isTruth left truth (op == .isNot)
        let right ← eval b
        if [.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains op then
          return expressionComparisonWith operandAffinity op a b left right
        binary op left right
    | .isNull arg negated => do return boolValue (isNull (← eval arg) != negated)
    | .inList argument values negated applyLeftAffinity =>
        evalInList eval operandAffinity constant argument values negated applyLeftAffinity
    | .call name args false =>
        let n := scalarFunctionName name
        if let some truth := booleanKeyword? e then .ok (boolValue truth)
        else if let some argument := Probability.input? name args then eval argument
        else if n == "coalesce" || n == "ifnull" then firstNonNull eval args.toList
        else if n == "iif" || n == "if" then conditional eval args.toList
        else if ["min", "max", "nullif"].contains n then do
          let kind ← ExprCollation.require (ExprCollation.argumentsKind? args)
          let values ← args.mapM eval
          match n, values.toList with
          | "nullif", [a, b] => return if ExprCollation.compare kind a b == .eq then .null else a
          | "min", first :: rest => return minmaxWith kind false first rest
          | "max", first :: rest => return minmaxWith kind true first rest
          | _, _ => builtin n values
        else do builtin n (← args.mapM eval)
    | .case_ base cases otherwise => do
        let b ← base.mapM (fun e => do return (e, ← eval e))
        branches eval (expressionComparisonWith operandAffinity .eq) b otherwise cases.toList
    | _ => .error "unsupported constant expression"

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

/-- WHERE branches use SQL three-valued truth but need only one truth outcome.
Testing false is distinct from testing not-true: NULL matches neither. This
preserves short-circuiting under NOT, AND and OR, including NULL operands. -/
def branchFuelWithConstants (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (constant : Expr → Bool) (transparentWrappers : Bool) :
    Nat → Bool → Expr → Except String Bool
  | 0, _, _ => .error "row predicate depth exhausted"
  | fuel + 1, wanted, expression => do
      if let some truth := staticTruth expression then
        return truth == wanted
      if transparentWrappers then
        if let .collate argument _ := expression then
          return ← branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel wanted argument
        if let .call name arguments false := expression then
          if let some argument := Probability.input? name arguments then
            return ← branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel wanted argument
      match expression with
      | .unary .not arg => branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel (!wanted) arg
      | .binary .and left right =>
          if wanted then
            if ← branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel true left then branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel true right
            else return false
          else
            if ← branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel false left then return true
            else branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel false right
      | .binary .or left right =>
          if wanted then
            if ← branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel true left then return true
            else branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel true right
          else
            if ← branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel false left then branchFuelWithConstants lookup operandAffinity constant transparentWrappers fuel false right
            else return false
      | _ => return Numeric.truth (← evalWithConstants lookup operandAffinity constant expression) ==
          (if wanted then .true else .false)

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

def testTermsWith (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) : List Expr → Except String Bool :=
  testTermsWithConstants lookup operandAffinity constantExpression

def testWhere (expression : Expr) : Except String Bool :=
  testTermsWith (fun _ _ => .error "unbound column") expressionAffinity (conditionTerms (prepare expression))

theorem evalWith_column (lookup : Option String → String → Except String Value)
    (operandAffinity : Expr → Option Affinity) (qualifier : Option String) (name : String) :
    evalWith lookup operandAffinity (.column qualifier name) = lookup qualifier name := rfl

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

end SQLeanite.SQLite.Scalar
