import SQLeanite.Engine.SqliteNameFoldChar

namespace SQLeanite

def ensureSequenceTable (db : Database) : Database :=
  if (findTable? db "sqlite_sequence").isSome then db
  else { db with tables := db.tables ++ [sqliteSequenceTable] }

def recordAutoincrement (db : Database) (table : Table) (rowid : Int) : Database :=
  if !table.usesAutoincrement then db
  else
    let state := ensureSequenceTable db
    let sequence := (findTable? state "sqlite_sequence").getD sqliteSequenceTable
    let index := sequence.rows.findIdx? fun row =>
      row.values[0]?.any (fun value => match value with
        | .text name => nameEq name (unqualifiedName table.name)
        | _ => false)
    let candidate := max 0 rowid
    let updated := match index with
      | some position =>
        let old := sequence.rows[position]!
        let high := max (old.values[1]?.bind Value.toInt? |>.getD 0) candidate
        let row : StoredRow :=
          { old with values := #[.text (unqualifiedName table.name), .integer high] }
        let rows := sequence.rows.set! position row
        let rowStore := (RowStore.checked rows sequence.columns.size).toOption.getD sequence.rowStore
        { sequence with rowStore }
      | none =>
        let row := StoredRow.mk sequence.nextRowid
          #[.text (unqualifiedName table.name), .integer candidate]
        let rows := sequence.rows.push row
        let rowStore := (RowStore.checked rows sequence.columns.size).toOption.getD sequence.rowStore
        let withRows := { sequence with rowStore }
        { withRows with nextRowid := sequence.nextRowid + 1 }
    replaceTable state updated

def removeAutoincrementRecord (db : Database) (tableName : String) : Database :=
  match findTable? db "sqlite_sequence" with
  | none => db
  | some sequence => replaceTable db (sequence.retainRows fun row =>
      !row.values[0]?.any (fun value => match value with
        | .text name => nameEq name (unqualifiedName tableName)
        | _ => false))

def applySequenceHighWater (db : Database) : Database :=
  match findTable? db "sqlite_sequence" with
  | none => db
  | some sequence =>
    sequence.rows.foldl (init := db) fun state row =>
      match row.values[0]?, row.values[1]?.bind Value.toInt? with
      | Option.some (Value.text name), Option.some high =>
        match findTable? state name with
        | some table =>
          if table.usesAutoincrement then
            replaceTable state { table with nextRowid := max table.nextRowid (high + 1) }
          else state
        | none => state
      | _, _ => state

def resolveColumn (env : Env) (qualifier : Option String) (name : String) : Except String Value := do
  let found := env.filter fun b =>
    nameEq b.column name && qualifier.all b.matchesQualifier
  if found.isEmpty then throw s!"no such column: {qualifier.map (· ++ ".") |>.getD ""}{name}"
  else
    let nearestDepth := found.foldl (fun depth b => min depth b.depth) found[0]!.depth
    let nearest := found.filter fun b => b.depth == nearestDepth
    let visible := nearest.filter fun b => !b.hidden
    let candidates := if visible.isEmpty then nearest else visible
    if candidates.size > 1 then
      throw s!"ambiguous column name: {qualifier.map (· ++ ".") |>.getD ""}{name}"
    else pure candidates[0]!.value

def optionOr (value : Option α) (error : String) : Except String α :=
  match value with | some x => .ok x | none => .error error

def finiteReal (value : Float) : Value :=
  if value.isNaN then .null else .real value

def integerShiftLeft (value amount : Int) : Value :=
  if amount >= 64 then .integer 0
  else .integer (((Int64.ofInt value) <<< (Int64.ofInt amount)).toInt)

def integerShiftRight (value amount : Int) : Value :=
  if amount >= 64 then .integer (if value < 0 then -1 else 0)
  else .integer (((Int64.ofInt value) >>> (Int64.ofInt amount)).toInt)

def integerBinary (op : BinaryOp) (a b : Int) : Value :=
  match op with
  | .add =>
    let result := a + b
    if inSigned64Range result then .integer result else finiteReal (Float.ofInt a + Float.ofInt b)
  | .sub =>
    let result := a - b
    if inSigned64Range result then .integer result else finiteReal (Float.ofInt a - Float.ofInt b)
  | .mul =>
    let result := a * b
    if inSigned64Range result then .integer result else finiteReal (Float.ofInt a * Float.ofInt b)
  | .div => if b == 0 then .null
    else if a == -9223372036854775808 && b == -1 then finiteReal (Float.ofInt a / Float.ofInt b)
    else .integer (a / b)
  | .mod => if b == 0 then .null else .integer (a % b)
  | .bitAnd => .integer (Int.ofNat (a.toNat &&& b.toNat))
  | .bitOr => .integer (Int.ofNat (a.toNat ||| b.toNat))
  | .shiftLeft => if b < 0 then integerShiftRight a (-b) else integerShiftLeft a b
  | .shiftRight => if b < 0 then integerShiftLeft a (-b) else integerShiftRight a b
  | _ => .null

theorem integerBinary_shiftLeft_negative (value amount : Int) (negative : amount < 0) :
    integerBinary .shiftLeft value amount = integerBinary .shiftRight value (-amount) := by
  have nonnegative : ¬-amount < 0 := by omega
  simp only [integerBinary, if_pos negative, if_neg nonnegative]

def numericOperand : Value → Value
  | .text source => match parseInteger64? source with
    | some integer => .integer integer
    | none => parseDecimal? source.trimAscii.toString |>.map Value.real |>.getD (.integer 0)
  | .blob _ => .integer 0
  | value => value

def integerCastOperand : Value → Value
  | .text source =>
    let chars := source.trimAscii.toString.toList
    let (sign, digits) := match chars with
      | '-' :: rest => ("-", rest)
      | '+' :: rest => ("", rest)
      | _ => ("", chars)
    let digitPrefix := String.mk (digits.takeWhile Char.isDigit)
    if digitPrefix.isEmpty then .integer 0
    else (sign ++ digitPrefix).toInt?.map Value.integer |>.getD (.integer 0)
  | value => numericOperand value

def aggregateNumericOperand : Value → Value
  | .text source => match parseInteger64? source with
    | some integer => .integer integer
    | none => parseDecimal? source.trimAscii.toString |>.map Value.real |>.getD (.real 0.0)
  | .blob _ => .real 0.0
  | value => value

def arithmetic (op : BinaryOp) (a b : Value) : Value :=
  match numericOperand a, numericOperand b with
  | .null, _ | _, .null => .null
  | .integer x, .integer y => integerBinary op x y
  | _, _ =>
    match a.toFloat?, b.toFloat? with
    | some x, some y =>
      match op with
      | .add => finiteReal (x + y)
      | .sub => finiteReal (x - y)
      | .mul => finiteReal (x * y)
      | .div => if y == 0.0 then .null else finiteReal (x / y)
      | .mod =>
        let divisor := y.toInt64.toInt
        if divisor == 0 then .null else finiteReal (Float.ofInt (x.toInt64.toInt % divisor))
      | _ => .null
    | _, _ => .integer 0

def compareOp (op : BinaryOp) (a b : Value) : Value :=
  let result :=
    match op with
    | .eq => a.sqlEq b
    | .ne => Truth.not (a.sqlEq b)
    | .lt => a.sqlLt b
    | .le => Truth.or (a.sqlLt b) (a.sqlEq b)
    | .gt => b.sqlLt a
    | .ge => Truth.or (b.sqlLt a) (a.sqlEq b)
    | .is => if (a matches .null) && (b matches .null) then .true
      else if (a matches .null) || (b matches .null) then .false else a.sqlEq b
    | .isNot => if (a matches .null) && (b matches .null) then .false
      else if (a matches .null) || (b matches .null) then .true else Truth.not (a.sqlEq b)
    | _ => .unknown
  result.toValue

def Expr.collationIn (env : Env) : Expr → String
  | .collate _ name => name
  | .column qualifier name =>
    env.find? (fun binding => nameEq binding.column name && qualifier.all (fun q =>
      nameEq q binding.alias || nameEq q binding.table)) |>.map (·.collation) |>.getD "binary"
  | _ => "binary"

def Expr.declaredTypeIn (env : Env) : Expr → String
  | .collate argument _ => argument.declaredTypeIn env
  | .call name _ _ => if name.toLower.startsWith "cast_" then (name.drop 5).toString.toUpper else ""
  | .column qualifier name =>
    env.find? (fun binding => nameEq binding.column name && qualifier.all (fun q =>
      nameEq q binding.alias || nameEq q binding.table)) |>.map (·.declaredType) |>.getD ""
  | _ => ""

def applyDeclaredAffinity (declaredType : String) (value : Value) : Value :=
  ({ name := "", declaredType } : Column).applyAffinity value

def comparisonValues (leftType rightType : String) (left right : Value) : Value × Value :=
  if hasNumericAffinity leftType && !hasNumericAffinity rightType then
    (left, applyDeclaredAffinity leftType right)
  else if hasNumericAffinity rightType && !hasNumericAffinity leftType then
    (applyDeclaredAffinity rightType left, right)
  else if hasTextAffinity leftType && hasNoAffinity rightType then
    (left, applyDeclaredAffinity leftType right)
  else if hasTextAffinity rightType && hasNoAffinity leftType then
    (applyDeclaredAffinity rightType left, right)
  else (left, right)

def globClassScanFuel : Nat → List Char → Char → Bool → Bool → Bool →
    Option (Bool × List Char)
  | 0, _, _, _, _, _ => none
  | fuel + 1, pattern, actual, negated, first, matched =>
    match pattern with
    | [] => none
    | ']' :: rest =>
      if first then globClassScanFuel fuel rest actual negated false (matched || actual == ']')
      else some ((if negated then !matched else matched), rest)
    | lower :: '-' :: upper :: rest =>
      if upper == ']' then
        globClassScanFuel fuel ('-' :: upper :: rest) actual negated false
          (matched || actual == lower)
      else
        globClassScanFuel fuel rest actual negated false
          (matched || (lower.val <= actual.val && actual.val <= upper.val))
    | expected :: rest =>
      globClassScanFuel fuel rest actual negated false (matched || actual == expected)

def globClassScan (pattern : List Char) (actual : Char)
    (negated first matched : Bool) : Option (Bool × List Char) :=
  globClassScanFuel (pattern.length + 1) pattern actual negated first matched

def globClass (pattern : List Char) (actual : Char) : Option (Bool × List Char) :=
  match pattern with
  | '^' :: rest => globClassScan rest actual true true false
  | rest => globClassScan rest actual false true false

def likeCharsFuel : Nat → List Char → List Char → Bool → Option Char → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, pattern, text, caseSensitive, escape =>
    match pattern, text with
    | [], [] => true
    | [], _ => false
    | escaped :: rest, chars => if escape == some escaped then
        match rest, chars with
        | expected :: patternTail, actual :: textTail =>
          (if caseSensitive then expected == actual else expected.toLower == actual.toLower) &&
            likeCharsFuel fuel patternTail textTail caseSensitive escape
        | _, _ => false
      else if escaped == '%' then
        likeCharsFuel fuel rest chars caseSensitive escape || match chars with
          | [] => false
          | _ :: tail => likeCharsFuel fuel pattern tail caseSensitive escape
      else if escaped == '_' then match chars with
        | _ :: tail => likeCharsFuel fuel rest tail caseSensitive escape
        | [] => false
      else if escaped == '*' && caseSensitive then
        likeCharsFuel fuel rest chars true escape || match chars with
          | [] => false
          | _ :: tail => likeCharsFuel fuel pattern tail true escape
      else if escaped == '?' && caseSensitive then match chars with
        | _ :: tail => likeCharsFuel fuel rest tail true escape
        | [] => false
      else if escaped == '[' && caseSensitive then match chars with
        | actual :: tail => match globClass rest actual with
          | some (true, patternTail) => likeCharsFuel fuel patternTail tail true escape
          | _ => false
        | [] => false
      else match chars with
        | actual :: tail =>
          (if caseSensitive then escaped == actual else escaped.toLower == actual.toLower) &&
            likeCharsFuel fuel rest tail caseSensitive escape
        | [] => false

def likeChars (pattern text : List Char) (caseSensitive : Bool)
    (escape : Option Char := none) : Bool :=
  likeCharsFuel (pattern.length + text.length + 1) pattern text caseSensitive escape

def patternOp (glob : Bool) (value pattern : Value) (escape : Option Char := none) : Value :=
  if value matches .null then .null
  else if pattern matches .null then .null
  else
    .integer (if likeChars (toString pattern).toList (toString value).toList glob escape then 1 else 0)

def json5IdentStart (character : Char) : Bool :=
  character.isAlpha || character == '_' || character == '$' || character.val ≥ 128

def json5IdentRest (character : Char) : Bool :=
  json5IdentStart character || character.isDigit

def takeJsonStringChars : List Char → List Char × List Char
  | [] => ([], [])
  | '\\' :: escaped :: rest =>
    let (body, suffix) := takeJsonStringChars rest
    ('\\' :: escaped :: body, suffix)
  | '"' :: rest => (['"'], rest)
  | character :: rest =>
    let (body, suffix) := takeJsonStringChars rest
    (character :: body, suffix)

def quoteJson5ObjectKeysCharsFuel : Nat → List Char → List Char
  | 0, _ => []
  | _, [] => []
  | fuel + 1, '"' :: rest =>
    let (quoted, suffix) := takeJsonStringChars rest
    '"' :: (quoted ++ quoteJson5ObjectKeysCharsFuel fuel suffix)
  | fuel + 1, character :: rest =>
    if json5IdentStart character then
      let identifierTail := rest.takeWhile json5IdentRest
      let suffix := rest.dropWhile json5IdentRest
      let spacing := suffix.takeWhile Char.isWhitespace
      match suffix.dropWhile Char.isWhitespace with
      | ':' :: afterColon =>
        '"' :: character :: (identifierTail ++ ('"' :: spacing ++
          (':' :: quoteJson5ObjectKeysCharsFuel fuel afterColon)))
      | _ => character :: (identifierTail ++ quoteJson5ObjectKeysCharsFuel fuel suffix)
    else character :: quoteJson5ObjectKeysCharsFuel fuel rest

def quoteJson5ObjectKeysChars (characters : List Char) : List Char :=
  quoteJson5ObjectKeysCharsFuel (characters.length + 1) characters

def quoteJson5ObjectKeys (source : String) : String :=
  String.mk (quoteJson5ObjectKeysChars source.toList)

def parseSQLiteJson (source : String) : Except String Lean.Json :=
  match Lean.Json.parse source with
  | .ok value => pure value
  | .error _ => Lean.Json.parse (quoteJson5ObjectKeys source)

def jsonToSqlValue : Lean.Json → Value
  | .null => .null
  | .bool value => .integer (if value then 1 else 0)
  | .num value =>
      let rendered := toString value
      match rendered.toInt? with
      | some integer => .integer integer
      | none => .real (parseDecimal? rendered |>.getD 0.0)
  | .str value => .text value
  | value => .text value.compress

def sqlValueToJson : Value → Lean.Json
  | .null => .null
  | .integer value => .num value
  | .real value => (Lean.Json.parse (toString value)).toOption.getD .null
  | .text value => (parseSQLiteJson value).toOption.getD (.str value)
  | .textBytes value => .str (toString (Value.textBytes value))
  | .blob value => .str (toString (Value.blob value))

def jsonPathValue? (source path : String) : Option Lean.Json := do
  let mut value ← (parseSQLiteJson source).toOption
  let path := if path.startsWith "$." then (path.drop 2).toString else path
  for component in path.splitOn "." do
    value ← (value.getObjVal? component).toOption
  pure value

def joinColumnMatches (left right : Env) (column : String) : Except String Bool := do
  let leftBinding ← optionOr
    (left.toList.reverse.find? fun binding => !binding.hidden && nameEq binding.column column)
    s!"no such column: {column}"
  let rightBinding ← optionOr
    (right.find? fun binding => !binding.hidden && nameEq binding.column column)
    s!"no such column: {column}"
  let (leftValue, rightValue) := comparisonValues leftBinding.declaredType
    rightBinding.declaredType leftBinding.value rightBinding.value
  let normalize := fun value => if nameEq leftBinding.collation "nocase" then
      match value with | .text text => Value.text text.toLower | other => other
    else value
  pure ((normalize leftValue).sqlEq (normalize rightValue) == .true)

def scalarMinMax (wantMax : Bool) (args : Array Value) : Value :=
  if args.any (· matches .null) then .null
  else args.foldl (init := args[0]?.getD .null) fun best v =>
    let ord := v.compare best
    if (wantMax && ord == .gt) || (!wantMax && ord == .lt) then v else best

def substringBounds (size : Nat) (start : Int) (length : Option Int) : Nat × Nat := Id.run do
  let total := Int.ofNat size
  let mut first := start
  let mut count := length.getD total
  if first < 0 then
    first := first + total
    if first < 0 then
      count := count + first
      first := 0
  else if first > 0 then first := first - 1
  else if count > 0 then count := count - 1
  if count < 0 then
    count := -count
    if count <= first then first := first - count
    else
      count := first
      first := 0
  first := max 0 (min first total)
  count := max 0 (min count (total - first))
  return (first.toNat, count.toNat)

def substringValue (value : Value) (start : Int) (length : Option Int) : Value :=
  match value with
  | .null => .null
  | .blob bytes =>
      let bounds := substringBounds bytes.size start length
      .blob (bytes.extract bounds.1 (bounds.1 + bounds.2))
  | value =>
      let chars := (toString value).toList
      let bounds := substringBounds chars.length start length
      .text (String.mk (chars.drop bounds.1 |>.take bounds.2))

def valueBytes : Value → ByteArray
  | .blob bytes => ByteArray.mk bytes
  | value => (toString value).toUTF8

def byteHex (byte : UInt8) : String :=
  let digit (value : Nat) :=
    Char.ofNat (if value < 10 then '0'.toNat + value else 'A'.toNat + value - 10)
  String.mk [digit (byte.toNat / 16), digit (byte.toNat % 16)]

def hexValue (value : Value) : String :=
  String.join ((valueBytes value).toList.map byteHex)

def expressionHasRealColumn (expression : Expr) : Bool :=
  expression.any fun
    | .column none "?" => false
    | .column _ _ => true
    | _ => false

def expressionIsDirectBind : Expr → Bool
  | .column none "?" => true
  | .call name _ _ => nameEq name "lean_unbound_parameter"
  | _ => false

def Expr.callsDirectOnly (expression : Expr) : Bool :=
  expression.any fun
    | .call name _ _ => nameEq name "testdirectonly"
    | _ => false

def Select.callsDirectOnlyFuel : Nat → Select → Bool
  | 0, _ => false
  | fuel + 1, query =>
    query.columns.any (fun column => column.expr.callsDirectOnly) ||
      query.valueRows.any (fun rows => rows.any (fun row => row.any Expr.callsDirectOnly)) ||
      query.where_.any Expr.callsDirectOnly || query.groupBy.any Expr.callsDirectOnly ||
      query.having.any Expr.callsDirectOnly ||
      query.orderBy.any (fun term => term.expr.callsDirectOnly) ||
      query.compounds.any (fun compound => callsDirectOnlyFuel fuel compound.2)

def Select.callsDirectOnly (query : Select) : Bool :=
  query.callsDirectOnlyFuel query.compoundHeight

def Statement.callsDirectOnly : Statement → Bool
  | .insert _ _ rows _ => rows.any (·.any Expr.callsDirectOnly)
  | .insertSelect _ _ query _ | .select query => query.callsDirectOnly
  | .delete _ _ where_ returning =>
      where_.any Expr.callsDirectOnly || returning.any (fun result => result.expr.callsDirectOnly)
  | .update _ _ assignments where_ _ =>
      assignments.any (fun assignment => assignment.2.callsDirectOnly) ||
        where_.any Expr.callsDirectOnly
  | .withRecursive _ _ seed step _ body _ =>
      seed.callsDirectOnly || step.callsDirectOnly || body.callsDirectOnly
  | .withCte _ _ source body _ => source.callsDirectOnly || body.callsDirectOnly
  | .values rows => rows.any (·.any Expr.callsDirectOnly)
  | _ => false

def trimText (source characters : String) (left right : Bool) : String :=
  let unwanted := characters.toList
  let chars := source.toList
  let chars := if left then chars.dropWhile unwanted.contains else chars
  let chars := if right then chars.reverse.dropWhile unwanted.contains |>.reverse else chars
  String.mk chars

end SQLeanite
