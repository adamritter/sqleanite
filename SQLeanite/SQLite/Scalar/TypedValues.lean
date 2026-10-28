import SQLeanite.SQLite.Scalar.PrepareFuel
import SQLeanite.SQLite.TextEncoding

namespace SQLeanite.SQLite.Scalar

theorem testBetween_argument_error (evaluate : Expr → Except String Value)
    (affinity : Expr → Option Affinity) (argument lower upper : Expr) (wanted : Bool) (message : String)
    (failed : evaluate argument = .error message) :
    testBetween evaluate affinity argument lower upper wanted = .error message := by
  simp [testBetween, failed, bind, Except.bind]

/-- WHERE branches use SQL three-valued truth but need only one truth outcome.
Testing false is distinct from testing not-true: NULL matches neither. This
preserves short-circuiting under NOT, AND and OR, including NULL operands. -/
def testEvaluatedFuel (evaluate : Expr → Except String Value)
    (operandAffinity : Expr → Option Affinity) (transparentWrappers : Bool) :
    Nat → Bool → Expr → Except String Bool
  | 0, _, _ => .error "row predicate depth exhausted"
  | fuel + 1, wanted, expression => do
      if let some truth := staticTruth expression then
        return truth == wanted
      if transparentWrappers then
        if let .collate argument _ := expression then
          return ← testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel wanted argument
        if let .call name arguments false := expression then
          if let some argument := Probability.input? name arguments then
            return ← testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel wanted argument
      match expression with
      | .call "__sqlean_between" arguments false =>
          match arguments.toList with
          | [argument, lower, upper] => testBetween evaluate operandAffinity argument lower upper wanted
          | _ => .error "invalid BETWEEN operands"
      | .unary .not arg => testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel (!wanted) arg
      | .binary .and left right =>
          if wanted then
            if ← testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel true left then testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel true right
            else return false
          else
            if ← testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel false left then return true
            else testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel false right
      | .binary .or left right =>
          if wanted then
            if ← testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel true left then return true
            else testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel true right
          else
            if ← testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel false left then testEvaluatedFuel evaluate operandAffinity transparentWrappers fuel false right
            else return false
      | _ => return Numeric.truth (← evaluate expression) ==
          (if wanted then .true else .false)

/-- Fuel is supplied by the existing structural expression height. Recursing
through CASE/function arrays is total, with no unbounded interpreter binding. -/
def plainScalar := JsonText.plain


/-- Actual representation bytes for a native-encoding operation. BLOBs are
already byte strings; numeric inputs stringify in the connection encoding. -/
def nativeBytes (encoding : Nat) (input : ScalarValue) : Array UInt8 :=
  match input.value with
  | .blob bytes => bytes
  | _ => if input.textEncoding == encoding then
      input.encodedText.getD (TextEncoding.toStorage encoding (Text.bytes input.value))
    else TextEncoding.toStorage encoding (Text.bytes input.value)


/-- BINARY uses the actual native bytes when TEXT retains a noncanonical
representation. Other collations and storage classes keep their old comparator. -/
def compareTyped (kind : Collation.Kind) (left right : ScalarValue) : Ordering :=
  let encoding := match kind with | .binary16le => 2 | .binary16be => 3 | _ => 1
  let textual := fun value => match value with | .text _ | .textBytes _ => true | _ => false
  if encoding != 1 && textual left.value && textual right.value then
    compare (nativeBytes encoding left).toList (nativeBytes encoding right).toList
  else ExprCollation.compare kind left.value right.value


theorem compareTyped_binary (left right : ScalarValue) :
    compareTyped .binary left right = ExprCollation.compare .binary left.value right.value := rfl


def comparisonTypedWith (kind : Collation.Kind) (op : BinaryOp) (a b : ScalarValue) : Value :=
  if op == .is then boolValue (compareTyped kind a b == .eq)
  else if op == .isNot then boolValue (compareTyped kind a b != .eq)
  else if isNull a.value || isNull b.value then .null
  else
    let order := compareTyped kind a b
    boolValue (match op with
      | .eq => order == .eq | .ne => order != .eq
      | .lt => order == .lt | .le => order != .gt
      | .gt => order == .gt | .ge => order != .lt
      | _ => false)


def expressionComparisonTypedWith (operandAffinity : Expr → Option Affinity)
    (op : BinaryOp) (left right : Expr) (a b : ScalarValue) : Value :=
  let affinity := comparisonAffinity (operandAffinity left) (operandAffinity right)
  comparisonTypedWith ((ExprCollation.binaryKind? left right).getD .binary) op
    { a with value := applyComparisonAffinity affinity a.value }
    { b with value := applyComparisonAffinity affinity b.value }


/-- OP_Concat concatenates native bytes before any UTF-8 observation. Keep
those bytes even when their decoding cannot be reversed. -/
def concatTyped (encoding : Nat) (left right : ScalarValue) : Except String ScalarValue := do
  if encoding != 2 && encoding != 3 then
    return plainScalar (← binary .concat left.value right.value)
  if isNull left.value || isNull right.value then return plainScalar .null
  let bytes := nativeBytes encoding left ++ nativeBytes encoding right
  discard <| Text.checkedBytes bytes
  return {
    value := ← Text.checkedBytes (TextEncoding.fromStorage encoding bytes)
    textEncoding := encoding
    encodedText := some bytes }


theorem concatTyped_utf8 (left right : ScalarValue) :
    concatTyped 1 left right = (plainScalar <$> binary .concat left.value right.value) := by
  simp [concatTyped]

def builtinTyped (name : String) (arguments : Array ScalarValue) : Except String ScalarValue := do
  let values : Array Value := arguments.map (·.value)
  match name,values.toList with
  | "__sqlean_encoded",[.text function,.integer encoding,value] => do
      let input := arguments[2]?.getD (plainScalar value)
      let databaseEncoding := encoding.toNat
      let textual := match value with | .text _ | .textBytes _ => true | _ => false
      if function == "stored" then
        let .blob bytes := value | throw "invalid stored TEXT representation"
        return {
          value := ← Text.checkedBytes (TextEncoding.fromStorage databaseEncoding bytes)
          textEncoding := databaseEncoding
          encodedText := some bytes }
      if function == "context" then
        return if textual then { input with
          textEncoding := databaseEncoding
          encodedText := if input.textEncoding == databaseEncoding then input.encodedText else none } else input
      if function == "input" then
        return if textual then { input with textEncoding := databaseEncoding } else input
      let runtimeEncoding := if textual then input.textEncoding else 1
      if function == "hex" then
        let bytes := match value with
          | .blob bytes => bytes
          | _ => input.encodedText.getD (TextEncoding.toStorage runtimeEncoding (Text.bytes value))
        return { value := ← Text.hex (.blob bytes), textEncoding := databaseEncoding }
      if function == "octet_length" then
        if Text.isNull value then return plainScalar .null
        let bytes := match value with
          | .blob bytes => bytes
          | _ => input.encodedText.getD (TextEncoding.toStorage
              (if textual then runtimeEncoding else databaseEncoding) (Text.bytes value))
        return plainScalar (.integer bytes.size)
      if function == "cast_text" then
        let raw := match value with
          | .blob bytes => some (bytes.extract 0 (bytes.size / 2 * 2))
          | .text _ | .textBytes _ => if input.textEncoding == databaseEncoding then input.encodedText else none
          | _ => none
        let converted ← TextEncoding.builtin function databaseEncoding value
        return {
          value := converted
          subtype := input.subtype
          textEncoding := databaseEncoding
          encodedText := raw }
      if function == "cast_blob" then
        if Text.isNull value then return plainScalar .null
        let bytes := match value with
          | .blob bytes => bytes
          | _ => if input.textEncoding == databaseEncoding then
              input.encodedText.getD (TextEncoding.toStorage databaseEncoding (Text.bytes value))
            else TextEncoding.toStorage databaseEncoding (Text.bytes value)
        return plainScalar (.blob bytes)
      throw "invalid encoded scalar operation"
  | "json_insert",_ => JsonInsert.evaluate .insert false arguments.toList
  | "jsonb_insert",_ => JsonInsert.evaluate .insert true arguments.toList
  | "json_set",_ => JsonInsert.evaluate .set false arguments.toList
  | "jsonb_set",_ => JsonInsert.evaluate .set true arguments.toList
  | "json_array_insert",_ => JsonInsert.evaluate .arrayInsert false arguments.toList
  | "jsonb_array_insert",_ => JsonInsert.evaluate .arrayInsert true arguments.toList
  | "json_replace",_ => JsonReplace.evaluate false arguments.toList
  | "jsonb_replace",_ => JsonReplace.evaluate true arguments.toList
  | "json_quote",[_] => JsonConstruct.quote (arguments[0]?.getD (JsonText.plain .null))
  | "json_array",_ => JsonConstruct.array false arguments.toList
  | "jsonb_array",_ => JsonConstruct.array true arguments.toList
  | "json_object",_ => JsonConstruct.object false arguments.toList
  | "jsonb_object",_ => JsonConstruct.object true arguments.toList
  | "json",[value] => JsonText.evaluate value
  | "json_extract",values => JsonText.extract values
  | "->",[value,path] => JsonText.arrow value path
  | "json_remove",values => JsonText.remove values
  | "json_patch",[target,patch] => JsonText.patch target patch
  | "subtype",[_] => return plainScalar (.integer (arguments[0]?.map (·.subtype.toNat) |>.getD 0))
  | _,_ =>
      let value ← Scalar.builtin name values
      return ⟨value, if name == "cast_text" then arguments[0]?.map (·.subtype) |>.getD 0 else 0,1,none⟩


theorem builtinTyped_stored_representation (encoding : Nat) (bytes : Array UInt8) (value : Value)
    (checked : Text.checkedBytes (TextEncoding.fromStorage encoding bytes) = .ok value) :
    builtinTyped "__sqlean_encoded" #[plainScalar (.text "stored"),plainScalar (.integer encoding),plainScalar (.blob bytes)] =
      .ok { value, textEncoding := encoding, encodedText := some bytes } := by
  simp [builtinTyped, plainScalar, JsonText.plain, checked, bind, Except.bind, pure, Except.pure]

def firstNonNullTyped (eval : Expr → Except String ScalarValue) : List Expr → Except String ScalarValue
  | [] => .ok (plainScalar .null)
  | x :: xs => do
      let v ← eval x
      if Text.isNull v.value then firstNonNullTyped eval xs else return v

def conditionalTyped (eval : Expr → Except String ScalarValue) (test : Expr → Except String Bool) :
    List Expr → Except String ScalarValue
  | [] => .ok (plainScalar .null)
  | [last] => eval last
  | condition :: result :: rest => do
      if ← test condition then eval result else conditionalTyped eval test rest

def branchesTyped (eval : Expr → Except String ScalarValue) (test : Expr → Except String Bool)
    (equal : Expr → Expr → Value → Value → Value) (base : Option (Expr × Value))
    (otherwise : Option Expr) : List (Expr × Expr) → Except String ScalarValue
  | [] => match otherwise with | none => .ok (plainScalar .null) | some e => eval e
  | (condition,result) :: rest => do
      let selected ← match base with
        | none => test condition
        | some (expression,b) => do
            pure (equal expression condition b (← eval condition).value == .integer 1)
      if selected then eval result else branchesTyped eval test equal base otherwise rest

def minmaxTyped (kind : Collation.Kind) (largest : Bool) (first : ScalarValue)
    (rest : List ScalarValue) : ScalarValue :=
  if (first :: rest).any (fun value => Text.isNull value.value) then plainScalar .null
  else rest.foldl (fun best value =>
    let ordering := compareTyped kind best value
    if (if largest then ordering == .lt else ordering != .lt) then value else best) first



end SQLeanite.SQLite.Scalar
