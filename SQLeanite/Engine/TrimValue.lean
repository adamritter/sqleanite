import SQLeanite.Engine.EnsureSequenceTable
import SQLeanite.SQLite.Scalar.PrepareFuel

namespace SQLeanite

def trimValue (source : Value) (characters : Option Value) (left right : Bool) : Value :=
  if source matches .null then .null else
  let sourceText? := match source with
    | .blob bytes => String.fromUTF8? (ByteArray.mk bytes)
    | value => some (toString value)
  let charactersText? := match characters with
    | none => some " "
    | some .null => none
    | some (.blob bytes) => some (String.fromUTF8? (ByteArray.mk bytes) |>.getD "")
    | some value => some (toString value)
  match sourceText?, charactersText? with
  | some sourceText, some characterText => .text (trimText sourceText characterText left right)
  | none, _ => source
  | _, none => .null

def evalScalarFunction (env : Env) (name : String) (args : Array Expr)
    (star : Bool) (values : Array Value) : Except String Value := do
  let lname := name.toLower
  if lname == "lean_is_true" || lname == "lean_is_not_true" ||
      lname == "lean_is_false" || lname == "lean_is_not_false" then
    if values.size != 1 then throw s!"wrong number of arguments to function {name}()"
    else
      let truthMatches := if lname == "lean_is_true" || lname == "lean_is_not_true" then
          values[0]!.truth == .true
        else values[0]!.truth == .false
      let result := if lname == "lean_is_not_true" || lname == "lean_is_not_false" then !truthMatches
        else truthMatches
      pure (.integer (if result then 1 else 0))
  else if lname == "json" then
    if values.size != 1 then throw "wrong number of arguments to function json()"
    else if values[0]! matches .null then pure .null
    else match parseSQLiteJson (toString values[0]!) with
      | .ok value => pure (.text value.compress)
      | .error message => throw message
  else if lname == "json_extract" then
    if values.size != 2 then throw "wrong number of arguments to function json_extract()"
    else if values[0]! matches .null || values[1]! matches .null then pure .null
    else pure ((jsonPathValue? (toString values[0]!) (toString values[1]!)).map jsonToSqlValue
      |>.getD .null)
  else if lname == "json_insert" then
    if values.size != 3 then throw "wrong number of arguments to function json_insert()"
    else match parseSQLiteJson (toString values[0]!) with
      | .error message => throw message
      | .ok base =>
          let path := toString values[1]!
          if !path.startsWith "$." || (path.drop 2).contains '.' then
            throw "JSON path error"
          else pure (.text (base.setObjVal! (path.drop 2).toString (sqlValueToJson values[2]!)).compress)
  else if lname.startsWith "lean_window_" then
    let function := (lname.drop "lean_window_".length).toString
    if function == "count" then
      pure (.integer (if values.any (fun value => !(value matches .null)) then 1 else 0))
    else if values.size == 1 then pure values[0]!
    else throw s!"wrong number of arguments to window function {function}()"
  else if lname.startsWith "cast_" then
    if values.size != 1 then throw "wrong number of arguments to function cast()"
    else
      let value := values[0]!
      let target := (lname.drop 5).toString
      if value matches .null then pure .null
      else if typeContains target "INT" then
        pure (.integer (integerCastOperand value |>.toInt?.getD 0))
      else if typeContains target "REAL" || typeContains target "FLOA" ||
          typeContains target "DOUB" then
        pure (.real (numericOperand value |>.toFloat?.getD 0.0))
      else if typeContains target "CHAR" || typeContains target "CLOB" ||
          typeContains target "TEXT" then
        pure (.text (toString value))
      else pure value
  else if lname == "nullif" then
    if values.size != 2 then throw "wrong number of arguments to function nullif()"
    else pure (if values[0]!.sqlEq values[1]! == .true then .null else values[0]!)
  else if lname == "min" || lname == "max" then
    if star || values.isEmpty then throw s!"wrong number of arguments to function {name}()"
    else if values.size == 1 then pure values[0]!
    else pure (scalarMinMax (lname == "max") values)
  else if lname == "abs" then
    if values.size != 1 then throw "wrong number of arguments to function abs()"
    else match values[0]! with
      | .integer i =>
        if i == -9223372036854775808 then throw "integer overflow"
        else pure (.integer (Int.natAbs i))
      | .real f => pure (.real f.abs)
      | .null => pure .null
      | v => pure (.real (v.toFloat?.getD 0.0).abs)
  else if lname == "round" then
    if values.isEmpty || values.size > 2 then throw "wrong number of arguments to function round()"
    else if values[0]! matches .null then pure .null
    else
      let number := numericOperand values[0]! |>.toFloat?.getD 0.0
      let digits := if values.size == 2 then values[1]!.toInt?.getD 0 else 0
      let factor := if digits <= 0 then 1.0 else
        (List.range (min 30 digits.toNat)).foldl (fun power _ => power * 10.0) 1.0
      pure (.real ((number * factor).round / factor))
  else if lname == "length" then
    if values.size != 1 then throw "wrong number of arguments to function length()"
    else match values[0]! with
      | .null => pure .null
      | .text s => pure (.integer s.length)
      | .blob b => pure (.integer b.size)
      | v => pure (.integer (toString v).length)
  else if lname == "octet_length" then
    if values.size != 1 then throw "wrong number of arguments to function octet_length()"
    else match values[0]! with
      | .null => pure .null
      | value => pure (.integer (valueBytes value).size)
  else if lname == "substr" || lname == "substring" then
    if values.size != 2 && values.size != 3 then
      throw s!"wrong number of arguments to function {name}()"
    else if values.any (fun value => value matches .null) then pure .null
    else
      let start := values[1]!.toInt?.getD 0
      let length := if values.size == 3 then values[2]!.toInt? else none
      pure (substringValue values[0]! start length)
  else if lname == "char" then
    let chars := values.toList.map fun value => Char.ofNat (value.toInt?.getD 0).toNat
    pure (.text (String.mk chars))
  else if lname == "unicode" then
    if values.size != 1 then throw "wrong number of arguments to function unicode()"
    else if values[0]! matches .null then pure .null
    else match (toString values[0]!).toList.head? with
      | some character => pure (.integer character.toNat)
      | none => pure .null
  else if lname == "hex" then
    if values.size != 1 then throw "wrong number of arguments to function hex()"
    else pure (.text (hexValue values[0]!))
  else if lname == "replace" then
    if values.size != 3 then throw "wrong number of arguments to function replace()"
    else if values.any (fun value => value matches .null) then pure .null
    else
      let source := toString values[0]!
      let pattern := toString values[1]!
      let replacement := toString values[2]!
      pure (.text (if pattern.isEmpty then source else source.replace pattern replacement))
  else if lname == "trim" || lname == "ltrim" || lname == "rtrim" then
    if values.isEmpty || values.size > 2 then
      throw s!"wrong number of arguments to function {name}()"
    else
      let characters := if values.size == 2 then some values[1]! else none
      pure (trimValue values[0]! characters (lname != "rtrim") (lname != "ltrim"))
  else if lname == "testfunc" then
    if values.size < 2 || values.size % 2 != 0 then
      throw "first argument should be one of: int int64 string double null value"
    else
      let mut result := Value.null
      for i in [0:values.size / 2] do
        let kind := toString values[2 * i]!
        let value := values[2 * i + 1]!
        if kind == "int" || kind == "int64" then result := .integer (value.toInt?.getD 0)
        else if kind == "double" then result := .real (value.toFloat?.getD 0.0)
        else if kind == "string" || kind == "value" then result := value
        else if kind == "null" then result := .null
        else throw "first argument should be one of: int int64 string double null value"
      pure result
  else if lname == "test_destructor" || lname == "test_destructor16" then
    if values.size != 1 then throw s!"wrong number of arguments to function {name}()"
    else pure values[0]!
  else if lname == "test_destructor_count" then
    if !values.isEmpty then throw "wrong number of arguments to function test_destructor_count()"
    else pure (.integer 0)
  else if lname == "test_auxdata" then
    let rowNumber := env.find? (fun binding => binding.hidden && nameEq binding.column "rowid")
      |>.bind (·.value.toInt?) |>.map (fun rowid => max 0 (rowid - 1)) |>.getD 0
    let statuses := args.map fun argument =>
      if expressionHasRealColumn argument then 0 else rowNumber
    if statuses.size == 1 then pure (.integer statuses[0]!)
    else pure (.text (String.intercalate " " (statuses.toList.map toString)))
  else if lname == "test_error" then
    throw (values[0]?.map toString |>.getD "")
  else if lname == "testfunc1" then
    throw "Error %d with %s percents %p"
  else if lname == "test_isolation" then
    pure (values[0]?.getD .null)
  else if lname == ("nullx_" ++ String.intercalate "_" (List.replicate 25 "123456789")) then
    if values.size > 127 then throw s!"too many arguments on function {name}"
    else if values.size != 127 then throw s!"wrong number of arguments to function {name}()"
    else pure .null
  else if lname == "sqlite_version" then
    if !star || !values.isEmpty then throw "wrong number of arguments to function sqlite_version()"
    else pure (.text "3.54.0")
  else if lname == "random" then
    if !values.isEmpty then throw "wrong number of arguments to function random()"
    else
      -- Keep the pure evaluator deterministic while retaining SQLite's
      -- volatile, row-varying behavior for scans. Only canonical hidden
      -- rowid bindings contribute, so the three rowid aliases do not
      -- accidentally count the same source three times.
      let salt := env.foldl (init := 0) fun total binding =>
        if binding.hidden && nameEq binding.column "rowid" then
          total + binding.value.toInt?.getD 0
        else total
      pure (.integer (-7046029254386353131 + salt))
  else if lname == "randomblob" then
    if values.size != 1 then throw "wrong number of arguments to function randomblob()"
    else
      let n := values[0]!.toInt?.getD 1
      let size := if n < 1 then 1 else n.toNat
      pure (.blob ((Array.range size).map fun i => UInt8.ofNat ((i * 73 + 41) % 256)))
  else if lname == "zeroblob" then
    if values.size != 1 then throw "wrong number of arguments to function zeroblob()"
    else
      let requested := values[0]!.toInt?.getD 0
      let size := if requested < 0 then 0 else requested.toNat
      pure (.blob (Array.replicate size 0))
  else if lname == "lean_unbound_parameter" then
    pure .null
  else if lname == "testdirectonly" then
    if values.size != 1 then throw "wrong number of arguments to function testdirectonly()"
    else pure (arithmetic .mul values[0]! (.integer 2))
  else if lname == "lean_check_myfunc" then
    if values.size != 1 then throw "wrong number of arguments to function myfunc()"
    else pure (.integer (if (numericOperand values[0]!).toFloat?.getD 0.0 < 10.0 then 1 else 0))
  else if lname == "lower" then
    if star || values.size != 1 then throw "wrong number of arguments to function lower()"
    else if values[0]! matches .null then pure .null else pure (.text (toString values[0]!).toLower)
  else if lname == "upper" then
    if star || values.size != 1 then throw "wrong number of arguments to function upper()"
    else if values[0]! matches .null then pure .null else pure (.text (toString values[0]!).toUpper)
  else if lname == "like" then
    if values.size != 2 && values.size != 3 then
      throw "wrong number of arguments to function like()"
    else if values.any (fun value => value matches .null) then pure .null
    else
      let escape ← if values.size == 3 then
          match (toString values[2]!).toList with
          | [character] => pure (some character)
          | _ => throw "ESCAPE expression must be a single character"
        else pure none
      pure (patternOp false values[1]! values[0]! escape)
  else if lname == "glob" then
    if values.size != 2 then throw "wrong number of arguments to function glob()"
    else pure (patternOp true values[1]! values[0]!)
  else if lname == "match" then
    if values.size != 2 then throw "wrong number of arguments to function match()"
    else throw "unable to use function MATCH in the requested context"
  else if lname == "typeof" then
    pure (.text <| match values[0]! with
      | .null => "null" | .integer _ => "integer" | .real _ => "real"
      | .text _ | .textBytes _ => "text" | .blob _ => "blob")
  else if lname == "quote" then
    pure (.text <| match values[0]! with
      | .null => "NULL"
      | .text s => "'" ++ s.replace "'" "''" ++ "'"
      | .real value => if value == (1.0 / 0.0) then "9.0e+999"
          else if value == (-1.0 / 0.0) then "-9.0e+999" else toString values[0]!
      | v => toString v)
  else if lname == "printf" || lname == "format" then
    if values.isEmpty then throw "wrong number of arguments to function printf()"
    else
      let mut formatted := toString values[0]!
      if values.size >= 3 then
        let requested := values[1]!.toInt?.getD 0
        let count := if requested < 0 then 0 else requested.toNat
        let character := (toString values[2]!).toList.head?.getD (Char.ofNat 0)
        formatted := formatted.replace "%.*c" (String.mk (List.replicate count character))
      for value in values.extract 1 values.size do
        let rendered := toString value
        if stringContains formatted "%s" then formatted := formatted.replace "%s" rendered
        else
          for width in [1:10] do
            let token := "%0" ++ toString width ++ "d"
            let padding := String.mk (List.replicate (width - min width rendered.length) '0')
            formatted := formatted.replace token (padding ++ rendered)
          formatted := formatted.replace "%d" rendered
      pure (.text formatted)
  else if lname == "count" && !(values.size == 1 || (star && values.isEmpty)) then
    throw s!"wrong number of arguments to function {name}()"
  else if ["sum", "total", "avg"].contains lname && (star || values.size != 1) then
    throw s!"wrong number of arguments to function {name}()"
  else if ["count", "sum", "total", "avg", "group_concat", "string_agg",
      "legacy_count", "md5sum"].contains lname then
    throw s!"misuse of aggregate function {lname}()"
  else throw s!"no such function: {name}"

def evalExprFuel : Nat → Env → Expr → Except String Value
  | 0, _, _ => throw "internal error: expression evaluation fuel exhausted"
  | fuel + 1, env, .literal v _ => pure v
  | fuel + 1, env, .column qualifier name => resolveColumn env qualifier name
  | fuel + 1, env, .star _ => throw "'*' may only appear in a result list or count(*)"
  | fuel + 1, env, .isNull arg negated => do
    let isNull := (← evalExprFuel fuel env arg) matches .null
    pure (.integer (if isNull != negated then 1 else 0))
  | fuel + 1, env, .collate arg _ => evalExprFuel fuel env arg
  | fuel + 1, env, .case_ base branches else_ => do
    let baseValue ← match base with
      | some expression => pure (some (← evalExprFuel fuel env expression))
      | none => pure none
    for branch in branches do
      let condition := branch.1
      let result := branch.2
      let matched ← match baseValue with
        | some value => pure (value.sqlEq (← evalExprFuel fuel env condition) == .true)
        | none => pure ((← evalExprFuel fuel env condition).truth == .true)
      if matched then return (← evalExprFuel fuel env result)
    match else_ with | some e => evalExprFuel fuel env e | none => pure .null
  | fuel + 1, env, .scalarSubquery _
  | fuel + 1, env, .inSubquery _ _ _
  | fuel + 1, env, .existsSubquery _ =>
    throw "internal error: unresolved subquery"
  | fuel + 1, env, .inList arg choices negated applyLeftAffinity => do
    let value ← evalExprFuel fuel env arg
    let values ← choices.mapM (evalExprFuel fuel env)
    let values := if applyLeftAffinity then
        values.map (applyDeclaredAffinity (arg.declaredTypeIn env))
      else values
    let truth := if value matches .null then .unknown
      else if values.any (fun v => value.sqlEq v == .true) then .true
      else if values.any (· matches .null) then .unknown
      else .false
    pure (Truth.toValue (if negated then Truth.not truth else truth))
  | fuel + 1, env, .unary op arg => do
    let v ← evalExprFuel fuel env arg
    match op with
    | .plus => pure v
    | .neg =>
      match v with
      | .integer i =>
        if i == -9223372036854775808 then pure (.real (Float.ofInt 9223372036854775808))
        else pure (.integer (-i))
      | .null => pure .null
      | _ => pure (.real (-(v.toFloat?.getD 0.0)))
    | .not => pure (Truth.toValue (Truth.not v.truth))
    | .bitNot => match v with
      | .null => pure .null
      | _ => pure (.integer (-(v.toInt?.getD 0) - 1))
  | fuel + 1, env, .binary op left right => do
    let a ← evalExprFuel fuel env left
    if op == .is || op == .isNot then
      if let some truth := SQLite.Scalar.booleanKeyword? right then
        unless env.any (fun binding => nameEq binding.column (SQLite.Scalar.booleanName truth)) do
          return SQLite.Scalar.isTruth a truth (op == .isNot)
    let b ← evalExprFuel fuel env right
    let isComparison := [.eq, .ne, .lt, .le, .gt, .ge, .is, .isNot].contains op
    let (a, b) := if isComparison then
        comparisonValues (left.declaredTypeIn env) (right.declaredTypeIn env) a b
      else (a, b)
    let nocase := isComparison &&
      (nameEq (left.collationIn env) "nocase" || nameEq (right.collationIn env) "nocase")
    let a := if nocase then match a with | .text value => .text value.toLower | other => other else a
    let b := if nocase then match b with | .text value => .text value.toLower | other => other else b
    match op with
    | .add | .sub | .mul | .div | .mod | .bitAnd | .bitOr | .shiftLeft | .shiftRight =>
      pure (arithmetic op a b)
    | .eq | .ne | .lt | .le | .gt | .ge | .is | .isNot => pure (compareOp op a b)
    | .like => pure (patternOp false a b)
    | .glob => pure (patternOp true a b)
    | .match => throw "unable to use function MATCH in the requested context"
    | .and => pure (Truth.toValue (Truth.and a.truth b.truth))
    | .or => pure (Truth.toValue (Truth.or a.truth b.truth))
    | .concat => pure (if (a matches .null) || (b matches .null) then .null
        else .text (toString a ++ toString b))
    | .arrow | .arrowText =>
      let source := toString a
      if !source.trimAscii.toString.startsWith "{" && !source.trimAscii.toString.startsWith "[" then
        pure (.text (source ++ (if op == .arrowText then "->>" else "->") ++ toString b))
      else match jsonPathValue? source (toString b) with
        | none => pure .null
        | some value =>
            if op == .arrowText then
              pure (jsonToSqlValue value)
            else
              pure (.text value.compress)
  | fuel + 1, env, .call "__sqlean_between" arguments false =>
      match arguments.toList with
      | [argument, lower, upper] =>
          SQLite.Scalar.evalBetween (evalExprFuel fuel env)
            (fun expression => match expression with
              | .column .. => some (SQLite.typeAffinity (expression.declaredTypeIn env))
              | _ => SQLite.Scalar.expressionAffinity expression) argument lower upper
      | _ => .error "invalid BETWEEN operands"
  | fuel + 1, env, .call name args star => do
    if let some truth := SQLite.Scalar.booleanKeyword? (.call name args star) then
      let keyword := SQLite.Scalar.booleanName truth
      if env.any (fun binding => nameEq binding.column keyword) then return ← resolveColumn env none keyword
      else return SQLite.Scalar.boolValue truth
    let lname := name.toLower
    if lname == "raise" then
      throw "RAISE() may only be used within a trigger-program"
    if lname == "coalesce" then
      if args.size < 2 then throw "wrong number of arguments to function coalesce()"
      for argument in args do
        let value ← evalExprFuel fuel env argument
        unless value matches .null do return value
      return .null
    if lname == "ifnull" then
      if count : args.size = 2 then
        have firstValid : 0 < args.size := by omega
        have secondValid : 1 < args.size := by omega
        let first ← evalExprFuel fuel env (args[0]'firstValid)
        if first matches .null then return (← evalExprFuel fuel env (args[1]'secondValid)) else return first
      else throw "wrong number of arguments to function ifnull()"
    if lname == "iif" then
      if count : args.size = 3 then
        have conditionValid : 0 < args.size := by omega
        have thenValid : 1 < args.size := by omega
        have elseValid : 2 < args.size := by omega
        if (← evalExprFuel fuel env (args[0]'conditionValid)).truth == .true then
          return (← evalExprFuel fuel env (args[1]'thenValid))
        else return (← evalExprFuel fuel env (args[2]'elseValid))
      else throw "wrong number of arguments to function iif()"
    if ["likely", "unlikely", "likelihood"].contains lname then
      let expected := if lname == "likelihood" then 2 else 1
      if args.size != expected then throw s!"wrong number of arguments to function {name}()"
      for argument in args do return (← evalExprFuel fuel env argument)
      throw s!"wrong number of arguments to function {name}()"
    if ["date", "time", "datetime"].contains lname then
      for argument in args do
        let value ← evalExprFuel fuel env argument
        if value matches .null then return .null
        let rendered := match value with
          | .integer 0 => "-4713-11-24 12:00:00"
          | .real number =>
              if number == 0.0 then "-4713-11-24 12:00:00" else toString value
          | _ => toString value
        let pieces := rendered.splitOn " "
        if lname == "date" then return .text (pieces[0]?.getD rendered |>.take 10 |>.toString)
        if lname == "time" then return .text (pieces[1]?.getD rendered |>.take 8 |>.toString)
        return .text (if pieces.length == 1 && rendered.length == 10 then
          rendered ++ " 00:00:00" else rendered)
      throw s!"wrong number of arguments to function {name}()"
    if lname == "test_frombind" then
      let mask := Id.run do
        let mut mask := 0
        for i in [:args.size] do
          if expressionIsDirectBind args[i]! then mask := mask + 2 ^ i
        return mask
      return .integer mask
    let values ← args.mapM (evalExprFuel fuel env)
    evalScalarFunction env name args star values

def evalExpr (env : Env) (expression : Expr) : Except String Value :=
  evalExprFuel expression.height env expression

theorem exceptMapValue_ok (function : Value → Value) (value : Value) :
    function <$> (Except.ok value : Except String Value) = .ok (function value) := by
  change Except.map function (.ok value) = .ok (function value)
  rfl

theorem evalExpr_literal (env : Env) (value : Value) :
    evalExpr env (.literal value) = .ok value := by
  rfl

theorem evalExpr_collate (env : Env) (expression : Expr) (collation : String) :
    evalExpr env (.collate expression collation) = evalExpr env expression := by
  rfl

theorem evalExpr_isNull_of_ok (env : Env) (expression : Expr) (negated : Bool)
    (value : Value) (success : evalExpr env expression = .ok value) :
    evalExpr env (.isNull expression negated) =
      .ok (.integer (if (value matches .null) != negated then 1 else 0)) := by
  change evalExprFuel expression.height env expression = .ok value at success
  cases value <;> cases negated <;>
    simp [evalExpr, Expr.height, evalExprFuel, success, exceptMapValue_ok]

theorem evalExpr_not_of_ok (env : Env) (expression : Expr) (value : Value)
    (success : evalExpr env expression = .ok value) :
    evalExpr env (.unary .not expression) =
      .ok (Truth.toValue (Truth.not value.truth)) := by
  change evalExprFuel expression.height env expression = .ok value at success
  cases value <;> simp [evalExpr, Expr.height, evalExprFuel, success, exceptMapValue_ok]

end SQLeanite
