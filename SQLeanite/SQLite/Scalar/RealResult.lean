import SQLeanite.SQLite.CastType
import SQLeanite.SQLite.DateDifference
import SQLeanite.SQLite.ExprCollation
import SQLeanite.SQLite.JsonConstruct
import SQLeanite.SQLite.JsonInsert
import SQLeanite.SQLite.JsonPosition
import SQLeanite.SQLite.Math
import SQLeanite.SQLite.Pattern
import SQLeanite.SQLite.TextEncoding
import SQLeanite.SQLite.Version
import SQLeanite.Syntax.TableConstraintDef

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

/-- IS resolves its right Boolean keyword through COLLATE wrappers. Unary
plus and function calls remain ordinary comparison operands. -/
def isTruthKeyword? (expression : Expr) : Option Bool :=
  booleanKeyword? (ExprCollation.strip expression)

theorem isTruthKeyword_collate (expression : Expr) (name : String) :
    isTruthKeyword? (.collate expression name) = isTruthKeyword? expression := rfl

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
  | .arrow => (·.value) <$> JsonText.arrow a b
  | .arrowText => JsonArrow.evaluate a b
  | .like => Pattern.evaluate false b a
  | .glob => Pattern.evaluate true b a
  | .concat => do
      if isNull a || isNull b then return .null
      Text.append a b
  | _ => .error "unsupported scalar operator"

abbrev Affinity := SQLite.Affinity

/-- sqlite3AffinityType's precedence, including FLOATING POINT => INTEGER. -/
def affinity := SQLite.CastType.affinity

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
  | .call "__sqlean_declared_collation" #[expression, .literal (.text _) _] false => expressionAffinity expression
  | .call "__sqlean_bound_value" #[_, .literal (.text declared) _] false => some (affinity declared)
  | .call "__sqlean_bound_value" #[_, .literal (.text declared) _, .literal (.integer _) _] false => some (affinity declared)
  | .call "__sqlean_encoded" #[.literal (.text function) _,_,argument] false =>
      if function == "input" || function == "context" then expressionAffinity argument
      else if function.startsWith "cast_" then some (affinity (function.drop 5).toString) else none
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

def builtin (name : String) (args : Array Value) : Except String Value :=
  match Version.value? name, args.isEmpty with
  | some value, true => .ok value
  | _, _ => do
    if name.startsWith "cast_" && args.size == 1 then
      return ← cast (name.drop 5).toString args[0]!
    if let some value := Math.evaluate? name args.toList then return value
    if let some result := DateTime.evaluate? name args.toList then return ← result
    match name, args.toList with
    | "__sqlean_bound_value", [value,.text _] |
        "__sqlean_bound_value", [value,.text _,.integer _] => pure value
    | "timediff", [left, right] => DateDifference.evaluate left right
    | "json_insert", values => (·.value) <$> JsonInsert.evaluate .insert false (values.map JsonText.plain)
    | "jsonb_insert", values => (·.value) <$> JsonInsert.evaluate .insert true (values.map JsonText.plain)
    | "json_set", values => (·.value) <$> JsonInsert.evaluate .set false (values.map JsonText.plain)
    | "jsonb_set", values => (·.value) <$> JsonInsert.evaluate .set true (values.map JsonText.plain)
    | "json_array_insert", values => (·.value) <$> JsonInsert.evaluate .arrayInsert false (values.map JsonText.plain)
    | "jsonb_array_insert", values => (·.value) <$> JsonInsert.evaluate .arrayInsert true (values.map JsonText.plain)
    | "json_replace", values => (·.value) <$> JsonReplace.evaluate false (values.map JsonText.plain)
    | "jsonb_replace", values => (·.value) <$> JsonReplace.evaluate true (values.map JsonText.plain)
    | "json_quote", [value] => (·.value) <$> JsonConstruct.quote (JsonText.plain value)
    | "json_array", values => (·.value) <$> JsonConstruct.array false (values.map JsonText.plain)
    | "jsonb_array", values => (·.value) <$> JsonConstruct.array true (values.map JsonText.plain)
    | "json_object", values => (·.value) <$> JsonConstruct.object false (values.map JsonText.plain)
    | "jsonb_object", values => (·.value) <$> JsonConstruct.object true (values.map JsonText.plain)
    | "json", [value] => (·.value) <$> JsonText.evaluate value
    | "json_extract", arguments => (·.value) <$> JsonText.extract arguments
    | "json_remove", arguments => (·.value) <$> JsonText.remove arguments
    | "json_patch", [target, patch] => (·.value) <$> JsonText.patch target patch
    | "->", [value, path] => (·.value) <$> JsonText.arrow value path
    | "subtype", [_] => pure (.integer 0)
    | "->>", [value, path] => JsonArrow.evaluate value path
    | "jsonb_patch", [target, patch] => JsonPatch.evaluate target patch
    | "jsonb_remove", values => JsonRemove.evaluate values
    | "jsonb_extract", values => JsonExtract.evaluate values
    | "json_pretty", [value] => JsonPretty.evaluate value
    | "json_pretty", [value, indent] => JsonPretty.evaluate value (some indent)
    | "jsonb", [value] => JsonBinary.evaluate value
    | "json_type", [value] => JsonAccess.evaluateType value
    | "json_type", [value, path] => JsonAccess.evaluateType value (some path)
    | "json_array_length", [value] => JsonAccess.evaluateLength value
    | "json_array_length", [value, path] => JsonAccess.evaluateLength value (some path)
    | "json_error_position", [value] => pure (JsonPosition.evaluate value)
    | "json_valid", [value] => JsonValid.evaluate value
    | "json_valid", [value, flags] => JsonValid.evaluate value (some flags)
    | "format", values | "printf", values => Format.evaluate values
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

theorem builtin_version : builtin "sqlite_version" #[] = .ok (.text Version.number) := rfl

theorem builtin_source : builtin "sqlite_source_id" #[] = .ok (.text Version.source) := rfl

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
          (!name.toLower.startsWith "cast_" && name != "__sqlean_between" && name != "__sqlean_declared_collation" && (booleanKeyword? expression).isNone &&
            (quotedIdentifier? expression).isNone) || args.any has
      | .unary _ arg | .isNull arg _ => has arg
      | .binary .arrow _ _ | .binary .arrowText _ _ => true
      | .binary _ left right => has left || has right
      | .inList arg values _ _ => has arg || values.any has
      | .case_ base branches otherwise => base.any has ||
          branches.any (fun (condition, result) => has condition || has result) || otherwise.any has
      -- Select-body function flags do not propagate through Expr.x.pSelect.
      | .inSubquery arg _ _ => has arg
      | .scalarSubquery .. | .existsSubquery .. => false
      | _ => false

def hasFunction (expression : Expr) : Bool := hasFunctionFuel expression.height expression

theorem hasFunction_scalarSubquery (sql : String) :
    hasFunction (.scalarSubquery sql) = false := rfl

theorem hasFunction_existsSubquery (sql : String) :
    hasFunction (.existsSubquery sql) = false := rfl

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

/-- parse.y folds ISNULL/NOTNULL on non-NULL literal tokens, skipping only
unary plus and minus. NULL, Boolean names, COLLATE and computed expressions do
not acquire this parser-time constant flag. No value evaluation occurs here. -/
def parserNonNullLiteral : Expr → Bool
  | .literal (.integer _) _ | .literal (.real _) _ | .literal (.text _) _ |
      .literal (.textBytes _) _ | .literal (.blob _) _ => true
  | .unary .plus argument | .unary .neg argument => parserNonNullLiteral argument
  | _ => false

def prepareNullTest (argument : Expr) (negated : Bool) : Expr :=
  if parserNonNullLiteral argument then .literal (.integer (if negated then 1 else 0))
  else .isNull argument negated

theorem prepareNullTest_token (argument : Expr) (negated : Bool)
    (known : parserNonNullLiteral argument = true) :
    prepareNullTest argument negated = .literal (.integer (if negated then 1 else 0)) := by
  simp [prepareNullTest, known]

theorem parserNonNullLiteral_collate (argument : Expr) (name : String) :
    parserNonNullLiteral (.collate argument name) = false := rfl

end SQLeanite.SQLite.Scalar
