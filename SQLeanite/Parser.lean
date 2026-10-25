import SQLeanite.Lexer
import SQLeanite.SQLite.Limits
import SQLeanite.SQLite.RowAssignment

namespace SQLeanite

structure ParserState where
  tokens : Array Token
  pos : Nat := 0

abbrev ParserM := StateT ParserState (Except String)

private def nextTokenAt (tokens : Array Token) (pos : Nat) : Nat × Token := Id.run do
  for offset in [:tokens.size - pos] do
    let current := pos + offset
    match tokens[current]? with
    | some (.space _) => continue
    | some token => return (current, token)
    | none => return (current, .eof)
  return (pos + (tokens.size - pos), .eof)

theorem nextTokenAt_past_end (tokens : Array Token) (pos : Nat)
    (pastEnd : tokens.size ≤ pos) : nextTokenAt tokens pos = (pos, .eof) := by
  simp [nextTokenAt, Nat.sub_eq_zero_of_le pastEnd] <;> rfl

private def peek : ParserM Token := do
  let st ← get
  pure (nextTokenAt st.tokens st.pos).2

private def advance : ParserM Token := do
  let st ← get
  let (pos, tok) := nextTokenAt st.tokens st.pos
  set { st with pos := pos + 1 }
  pure tok

private def currentTokenPos : ParserM Nat := do
  let st ← get
  pure (nextTokenAt st.tokens st.pos).1

private def tokenSource (start stop : Nat) : ParserM String := do
  let st ← get
  pure (String.join ((st.tokens.extract start stop).toList.map Token.render)).trimAscii.toString

private def keywordEq (s kw : String) : Bool := s.toLower == kw

private def isKeyword (tok : Token) (kw : String) : Bool :=
  match tok with
  | .ident s => keywordEq s kw
  | _ => false

private def syntaxError : Token → String
  | .eof => "incomplete input"
  | token => s!"near \"{token.render}\": syntax error"

private def acceptKeyword (kw : String) : ParserM Bool := do
  if isKeyword (← peek) kw then advance *> pure true else pure false

private def expectKeyword (kw : String) : ParserM Unit := do
  unless ← acceptKeyword kw do
    throw (syntaxError (← peek))

private def isSymbol (tok : Token) (s : String) : Bool :=
  match tok with
  | .symbol x => x == s
  | _ => false

private def acceptSymbol (s : String) : ParserM Bool := do
  if isSymbol (← peek) s then advance *> pure true else pure false

private def expectSymbol (s : String) : ParserM Unit := do
  unless ← acceptSymbol s do throw (syntaxError (← peek))

private def expectIdent : ParserM String := do
  match ← advance with
  | .ident s | .quotedIdent s _ | .string s => pure s
  | tok => throw (syntaxError tok)

private def expectAlias : ParserM String := do
  match ← advance with
  | .ident s | .quotedIdent s _ | .string s => pure s
  | tok => throw (syntaxError tok)

private def parseQualifiedName : ParserM (Option String × String) := do
  let first ← expectIdent
  if ← acceptSymbol "." then pure (some first, ← expectIdent)
  else pure (none, first)

private def expectDisplayedName : ParserM (String × String) := do
  match ← advance with
  | .ident name => pure (name, name)
  | .quotedIdent name source => pure (name, source)
  | .string name => pure (name, "'" ++ name.replace "'" "''" ++ "'")
  | token => throw (syntaxError token)

private def captureSubquery : ParserM String := do
  let start ← currentTokenPos
  let mut depth := 0
  let mut done := false
  while !done do
    match ← peek with
    | .eof => throw "incomplete input"
    | .symbol ")" =>
      if depth == 0 then done := true
      else depth := depth - 1; discard <| advance
    | .symbol "(" =>
      depth := depth + 1
      discard <| advance
    | _ => discard <| advance
  let stop ← currentTokenPos
  let source ← tokenSource start stop
  expectSymbol ")"
  pure source

private def parseNullOrder : ParserM (Option Bool) := do
  if ← acceptKeyword "nulls" then
    if ← acceptKeyword "first" then return some true
    expectKeyword "last"
    return some false
  return none


private def binaryInfo : Token → Option (BinaryOp × Nat)
  | .ident s =>
    if keywordEq s "or" then some (.or, 1)
    else if keywordEq s "and" then some (.and, 2)
    else if keywordEq s "like" then some (.like, 3)
    else if keywordEq s "glob" then some (.glob, 3)
    else if keywordEq s "match" then some (.match, 3)
    else none
  | .symbol "=" | .symbol "==" => some (.eq, 3)
  | .symbol "!=" | .symbol "<>" => some (.ne, 3)
  | .symbol "<" => some (.lt, 4)
  | .symbol "<=" => some (.le, 4)
  | .symbol ">" => some (.gt, 4)
  | .symbol ">=" => some (.ge, 4)
  | .symbol "|" => some (.bitOr, 5)
  | .symbol "&" => some (.bitAnd, 5)
  | .symbol "<<" => some (.shiftLeft, 5)
  | .symbol ">>" => some (.shiftRight, 5)
  | .symbol "||" => some (.concat, 8)
  | .symbol "->" => some (.arrow, 8)
  | .symbol "->>" => some (.arrowText, 8)
  | .symbol "+" => some (.add, 6)
  | .symbol "-" => some (.sub, 6)
  | .symbol "*" => some (.mul, 7)
  | .symbol "/" => some (.div, 7)
  | .symbol "%" => some (.mod, 7)
  | _ => none

private def hexNibble? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' <= c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def decodeBlobChars : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
      let high ← hexNibble? high
      let low ← hexNibble? low
      return UInt8.ofNat (high * 16 + low) :: (← decodeBlobChars rest)
  | _ => none

private def decodeBlob? (source : String) : Option (Array UInt8) :=
  (decodeBlobChars source.toList).map List.toArray

mutual
  private def parseExprFuel : Nat → (minPrec : Nat := 0) → ParserM Expr
    | 0, _ => throw "parser stack overflow"
    | fuel + 1, minPrec => do
      let mut lhs ← parseUnaryFuel fuel
      let mut looping := true
      while looping do
        if (← acceptKeyword "collate") then
          lhs := .collate lhs (← expectIdent)
        else if minPrec <= 3 && isKeyword (← peek) "between" then
          discard <| advance
          let lower ← parseExprFuel fuel 3
          expectKeyword "and"
          let upper ← parseExprFuel fuel 4
          lhs := .binary .and (.binary .ge lhs lower) (.binary .le lhs upper)
        else if minPrec <= 3 && isKeyword (← peek) "not" then
          discard <| advance
          if ← acceptKeyword "between" then
            let lower ← parseExprFuel fuel 3
            expectKeyword "and"
            let upper ← parseExprFuel fuel 4
            lhs := .unary .not (.binary .and (.binary .ge lhs lower) (.binary .le lhs upper))
          else if ← acceptKeyword "like" then
            let pattern ← parseExprFuel fuel 4
            let comparison ← if ← acceptKeyword "escape" then
                pure (.call "like" #[pattern, lhs, ← parseExprFuel fuel 4] false)
              else pure (.binary .like lhs pattern)
            lhs := .unary .not comparison
          else if ← acceptKeyword "glob" then
            lhs := .unary .not (.binary .glob lhs (← parseExprFuel fuel 4))
          else if ← acceptKeyword "match" then
            lhs := .unary .not (.binary .match lhs (← parseExprFuel fuel 4))
          else if ← acceptKeyword "null" then
            lhs := .isNull lhs true
          else if ← acceptKeyword "in" then
            expectSymbol "("
            if isKeyword (← peek) "select" then
              lhs := .unary .not (.inSubquery lhs (← captureSubquery))
            else
              let mut values := #[]
              unless ← acceptSymbol ")" do
                values := values.push (← parseExprFuel fuel)
                while ← acceptSymbol "," do values := values.push (← parseExprFuel fuel)
                expectSymbol ")"
              lhs := .inList lhs values true
          else throw (syntaxError (← peek))
        else if minPrec <= 3 && isKeyword (← peek) "in" then
          discard <| advance
          if ← acceptSymbol "(" then
            if isKeyword (← peek) "select" then lhs := .inSubquery lhs (← captureSubquery)
            else
              let mut values := #[]
              unless ← acceptSymbol ")" do
                values := values.push (← parseExprFuel fuel)
                while ← acceptSymbol "," do values := values.push (← parseExprFuel fuel)
                expectSymbol ")"
              lhs := .inList lhs values
          else
            let table ← expectIdent
            lhs := .inSubquery lhs ("SELECT * FROM " ++ table)
        else if minPrec <= 3 && isKeyword (← peek) "is" then
          discard <| advance
          let negated ← acceptKeyword "not"
          if ← acceptKeyword "distinct" then
            expectKeyword "from"
            let rhs ← parseExprFuel fuel 4
            lhs := .binary (if negated then .is else .isNot) lhs rhs
          else
            let rhs ← parseExprFuel fuel 4
            lhs := match rhs with
              | .literal .null => .isNull lhs negated
              | _ => .binary (if negated then .isNot else .is) lhs rhs
        else if minPrec <= 3 && isKeyword (← peek) "isnull" then
          discard <| advance
          lhs := .isNull lhs false
        else if minPrec <= 3 && isKeyword (← peek) "notnull" then
          discard <| advance
          lhs := .isNull lhs true
        else
          match binaryInfo (← peek) with
          | some (op, prec) =>
            if prec < minPrec then looping := false
            else
              discard <| advance
              let rhs ← parseExprFuel fuel (prec + 1)
              if op == .like && (← acceptKeyword "escape") then
                lhs := .call "like" #[rhs, lhs, ← parseExprFuel fuel (prec + 1)] false
              else lhs := .binary op lhs rhs
          | none => looping := false
      pure lhs

  private def parseUnaryFuel : Nat → ParserM Expr
    | 0 => throw "parser stack overflow"
    | fuel + 1 => do
      if ← acceptSymbol "+" then pure (.unary .plus (← parseUnaryFuel fuel))
      else if ← acceptSymbol "-" then
        -- The negative Int64 endpoint is the one signed literal whose
        -- unsigned magnitude does not fit in a positive Int64.
        match ← peek with
        | .integer i source =>
          if i == 9223372036854775808 then
            discard <| advance
            pure (.literal (.integer (-9223372036854775808))
              (some ("-" ++ SQLite.NumericLiteral.normalize (source.getD (toString i)))))
          else pure (.unary .neg (← parseUnaryFuel fuel))
        | _ => pure (.unary .neg (← parseUnaryFuel fuel))
      else if ← acceptSymbol "~" then pure (.unary .bitNot (← parseUnaryFuel fuel))
      else if ← acceptKeyword "not" then pure (.unary .not (← parseExprFuel fuel 3))
      else parsePrimaryFuel fuel

  private def parseCallFuel (fuel : Nat) (name : String) : ParserM Expr := do
    let call ← if ← acceptSymbol "*" then
      expectSymbol ")"
      pure (.call name #[] true)
    else
      let distinct ← acceptKeyword "distinct"
      if !distinct then discard <| acceptKeyword "all"
      let mut args := #[]
      let mut ordering := #[]
      unless ← acceptSymbol ")" do
        unless isKeyword (← peek) "order" do
          args := args.push (← parseExprFuel fuel)
          while ← acceptSymbol "," do args := args.push (← parseExprFuel fuel)
        if ← acceptKeyword "order" then
          expectKeyword "by"
          let mut more := true
          while more do
            let expression ← parseExprFuel fuel
            let descending ← acceptKeyword "desc"
            if !descending then discard <| acceptKeyword "asc"
            let nullsFirst ← parseNullOrder
            ordering := ordering.push (AggregateOrder.encode { expr := expression, descending, nullsFirst })
            unless ordering.size ≤ SQLite.Limits.maxColumns do throw "too many terms in ORDER BY clause"
            more ← acceptSymbol ","
        expectSymbol ")"
      unless args.size ≤ SQLite.Limits.maxFunctionArgs do
        throw s!"too many arguments on function {name}"
      let call := Expr.call (if distinct then distinctAggregateName name else name) args false
      pure (if ordering.isEmpty then call else .call "__sqlean_aggregate_order" (#[call] ++ ordering) false)
    let call ← if ← acceptKeyword "filter" then do
        expectSymbol "("
        expectKeyword "where"
        let condition ← parseExprFuel fuel
        expectSymbol ")"
        pure (Expr.call "__sqlean_aggregate_filter" #[call, condition] false)
      else pure call
    let isWindow ← acceptKeyword "over"
    if isWindow then
      if ← acceptSymbol "(" then
        let mut depth := 1
        while depth > 0 do
          match ← advance with
          | .symbol "(" => depth := depth + 1
          | .symbol ")" => depth := depth - 1
          | .eof => throw "incomplete input"
          | _ => pure ()
      else discard <| expectIdent
    pure (if isWindow then match call with
      | .call name args star => .call ("lean_window_" ++ name) args star
      | other => other
      else call)

  private def parsePrimaryFuel : Nat → ParserM Expr
    | 0 => throw "parser stack overflow"
    | fuel + 1 => do
      match ← advance with
      | .integer i source =>
        let spelling := SQLite.NumericLiteral.integerSpelling i (source.getD (toString i))
        if i <= 9223372036854775807 then pure (.literal (.integer i) spelling)
        else pure (.literal (.real (Float.ofInt i)) spelling)
      | .real s =>
        match parseDecimal? (SQLite.NumericLiteral.normalize s) with
        | some f => pure (.literal (.real f) (some (SQLite.NumericLiteral.normalize s)))
        | none => throw s!"invalid real number {s}"
      | .string s => pure (.literal (.text s))
      | .symbol "*" => pure (.star)
      | .symbol "?" => pure (.column none "?")
      | .symbol "(" =>
        if isKeyword (← peek) "select" || isKeyword (← peek) "values" then
          pure (.scalarSubquery (← captureSubquery))
        else
          let e ← parseExprFuel fuel
          expectSymbol ")"
          pure e
      | .ident s =>
        if keywordEq s "x" && (match ← peek with | .string _ => true | _ => false) then
          match ← advance with
          | .string source =>
            match decodeBlob? source with
            | some bytes => pure (.literal (.blob bytes))
            | none => throw "unrecognized token: invalid blob literal"
          | tok => throw (syntaxError tok)
        else if keywordEq s "exists" then
          expectSymbol "("
          pure (.existsSubquery (← captureSubquery))
        else if keywordEq s "cast" then
          expectSymbol "("
          let argument ← parseExprFuel fuel
          expectKeyword "as"
          let typeName ← expectIdent
          expectSymbol ")"
          pure (.call ("cast_" ++ typeName.toLower) #[argument] false)
        else if keywordEq s "case" then
          let base ← if isKeyword (← peek) "when" then pure none else some <$> parseExprFuel fuel
          let mut branches := #[]
          while ← acceptKeyword "when" do
            let condition ← parseExprFuel fuel
            expectKeyword "then"
            branches := branches.push (condition, ← parseExprFuel fuel)
          let else_ ← if ← acceptKeyword "else" then some <$> parseExprFuel fuel else pure none
          expectKeyword "end"
          pure (.case_ base branches else_)
        else if keywordEq s "null" then pure (.literal .null)
        else if ["from", "where", "group", "having", "order", "limit", "offset",
            "union", "intersect", "except"].contains s.toLower then
          throw (syntaxError (.ident s))
        else if ← acceptSymbol "(" then
          parseCallFuel fuel s
        else if ← acceptSymbol "." then
          if ← acceptSymbol "*" then pure (.star (some s))
          else
            let second ← expectIdent
            if ← acceptSymbol "." then
              let qualifier := s ++ "." ++ second
              if ← acceptSymbol "*" then pure (.star (some qualifier))
              else pure (.column (some qualifier) (← expectIdent))
            else pure (.column (some s) second)
        else if keywordEq s "true" then pure (.call "__sqlean_boolean_true" #[] false)
        else if keywordEq s "false" then pure (.call "__sqlean_boolean_false" #[] false)
        else pure (.column none s)
      | .quotedIdent s _ =>
        if ← acceptSymbol "(" then parseCallFuel fuel s
        else if ← acceptSymbol "." then
          if ← acceptSymbol "*" then pure (.star (some s))
          else pure (.column (some s) (← expectIdent))
        else pure (.call "lean_dqs" #[.literal (.text s)] false)
      | tok => throw (syntaxError tok)
end

private def parserExpressionDepth : Nat := 1000


private def parseExpr (minPrec : Nat := 0) : ParserM Expr :=
  parseExprFuel (Nat.succ parserExpressionDepth) minPrec

private def parseUnary : ParserM Expr :=
  parseUnaryFuel (Nat.succ parserExpressionDepth)

private def constantInt? : Expr → Option Int
  | .literal (.integer value) _ => some value
  | .call "__sqlean_boolean_true" #[] false => some 1
  | .call "__sqlean_boolean_false" #[] false => some 0
  | .unary .plus expr => constantInt? expr
  | .unary .neg expr => (-·) <$> constantInt? expr
  | .binary op left right => do
    let a ← constantInt? left
    let b ← constantInt? right
    match op with
    | .add => some (a + b)
    | .sub => some (a - b)
    | .mul => some (a * b)
    | .div => if b == 0 then none else some (a / b)
    | .mod => if b == 0 then none else some (a % b)
    | _ => none
  | _ => none

private def skippedLimitLiteral : Expr → Bool
  | .literal _ _ => true
  | .unary .plus expression | .unary .neg expression => skippedLimitLiteral expression
  | _ => false

/-- Preserve the two LIMIT spellings until the count is known: count zero
skips conversion of a literal offset, including NULL and out-of-range reals. -/
private def parseLimitClause : ParserM (Option Nat × Nat × Bool) := do
  unless ← acceptKeyword "limit" do return (none, 0, false)
  let first ← parseExpr
  let mut countExpression := first
  let mut offsetExpression : Expr := .literal (.integer 0)
  if ← acceptSymbol "," then
    offsetExpression := first
    countExpression ← parseExpr
  else if ← acceptKeyword "offset" then
    offsetExpression ← parseExpr
  let count ← match constantInt? countExpression with
    | some value => pure value
    | none => throw "datatype mismatch"
  unless (-9223372036854775808 : Int) ≤ count && count ≤ 9223372036854775807 do
    throw "datatype mismatch"
  let skip ← match constantInt? offsetExpression with
    | some value => pure value
    | none =>
        if count == 0 && skippedLimitLiteral offsetExpression then pure 0
        else throw "datatype mismatch"
  unless count == 0 || ((-9223372036854775808 : Int) ≤ skip && skip ≤ 9223372036854775807) do
    throw "datatype mismatch"
  return (if count < 0 then none else some count.toNat,
    if count == 0 then 0 else (max 0 skip).toNat, true)


private def parseOptionalNameList : ParserM (Option (Array String)) := do
  if ← acceptSymbol "(" then
    let mut names := #[(← expectIdent)]
    while ← acceptSymbol "," do names := names.push (← expectIdent)
    unless isSymbol (← peek) ")" do
      throw s!"syntax error after column name \"{names[names.size - 1]!}\""
    expectSymbol ")"
    pure (some names)
  else pure none

private def isColumnConstraint : Token → Bool
  | .ident s => ["primary", "not", "null", "unique", "check", "default", "collate",
      "references", "constraint", "as", "generated"].contains s.toLower
  | _ => false

private def skipTableConstraint : ParserM Unit := do
  let mut depth := 0
  let mut done := false
  while !done do
    match ← peek with
    | .symbol "(" => depth := depth + 1; discard <| advance
    | .symbol ")" =>
      if depth == 0 then done := true
      else depth := depth - 1; discard <| advance
    | .symbol "," =>
      if depth == 0 then done := true else discard <| advance
    | .eof => throw "incomplete input"
    | _ => discard <| advance

private def parseConflictAction : ParserM ConflictAction := do
  if ← acceptKeyword "rollback" then pure .rollback
  else if ← acceptKeyword "abort" then pure .abort
  else if ← acceptKeyword "fail" then pure .fail
  else if ← acceptKeyword "ignore" then pure .ignore
  else if ← acceptKeyword "replace" then pure .replace
  else throw "expected conflict action"

private def consumeIgnoredConstraintNames : ParserM Unit := do
  while ← acceptKeyword "constraint" do discard <| expectIdent

private def parseTableConstraint : ParserM (Option TableConstraintDef) := do
  let constraintName ← if ← acceptKeyword "constraint" then some <$> expectIdent else pure none
  let primary ← if ← acceptKeyword "primary" then expectKeyword "key" *> pure true
    else pure false
  if primary || (← acceptKeyword "unique") then
    expectSymbol "("
    let mut columns := #[]
    let mut collations : Array (Option String) := #[]
    let mut descending : Array Bool := #[]
    let mut autoIncrement := false
    let mut done := false
    while !done do
      columns := columns.push (← expectIdent)
      if isSymbol (← peek) "(" then
        throw "expressions prohibited in PRIMARY KEY and UNIQUE constraints"
      if primary && columns.size == 1 then
        autoIncrement := ← acceptKeyword "autoincrement"
      let collation ← if ← acceptKeyword "collate" then some <$> expectIdent else pure none
      collations := collations.push collation
      let desc ← if ← acceptKeyword "asc" then pure false else acceptKeyword "desc"
      descending := descending.push desc
      done := !(← acceptSymbol ",")
    expectSymbol ")"
    let conflict ← if ← acceptKeyword "on" then
        expectKeyword "conflict" *> parseConflictAction
      else pure .abort
    consumeIgnoredConstraintNames
    pure (some { columns, collations, descending, primaryKey := primary, autoIncrement, conflict })
  else if ← acceptKeyword "check" then
    expectSymbol "("
    let sourceStart ← currentTokenPos
    let expression ← parseExpr
    let sourceStop ← currentTokenPos
    let sourceSql ← tokenSource sourceStart sourceStop
    expectSymbol ")"
    if ← acceptKeyword "on" then
      expectKeyword "conflict"
      discard <| parseConflictAction
    consumeIgnoredConstraintNames
    pure (some { columns := #[], check := some { expression, name := constraintName, sourceSql } })
  else if ← acceptKeyword "foreign" then
    expectKeyword "key"
    expectSymbol "("
    discard <| expectIdent
    if isSymbol (← peek) "(" then throw "near \"(\": syntax error"
    while ← acceptSymbol "," do discard <| expectIdent
    expectSymbol ")"
    expectKeyword "references"
    discard <| expectIdent
    discard <| parseOptionalNameList
    pure none
  else
    skipTableConstraint
    pure none

private def parseColumnDef : ParserM ColumnDef := do
  let name ← expectIdent
  let typeStart ← currentTokenPos
  let mut typeDepth := 0
  let mut scanningType := true
  while scanningType do
    match ← peek with
    | token@(.ident _) =>
      if typeDepth == 0 && isColumnConstraint token then scanningType := false
      else discard <| advance
    | .symbol "(" => typeDepth := typeDepth + 1; discard <| advance
    | .symbol ")" =>
      if typeDepth == 0 then scanningType := false
      else typeDepth := typeDepth - 1; discard <| advance
    | .symbol "," =>
      if typeDepth == 0 then scanningType := false else discard <| advance
    | .symbol ";" => scanningType := false
    | .eof => scanningType := false
    | _ => discard <| advance
  let typ ← tokenSource typeStart (← currentTokenPos)
  let mut defaultValue := none
  let mut defaultSql := none
  let mut generated := none
  let mut notNull := false
  let mut notNullConflict := ConflictAction.abort
  let mut primaryKey := false
  let mut autoIncrement := false
  let mut unique := false
  let mut conflict := ConflictAction.abort
  let mut collation := "binary"
  let mut references : Option ForeignKeyDef := none
  let mut check : Option CheckDef := none
  let mut pendingConstraintName : Option String := none
  let mut scanning := true
  while scanning do
    if ← acceptKeyword "constraint" then pendingConstraintName := some (← expectIdent)
    else if ← acceptKeyword "default" then
      let sourceStart ← currentTokenPos
      defaultValue := some (← parseUnary)
      defaultSql := some (← tokenSource sourceStart (← currentTokenPos))
    else if ← acceptKeyword "generated" then
      discard <| acceptKeyword "always"
      expectKeyword "as"
      expectSymbol "("
      generated := some (← parseExpr)
      expectSymbol ")"
      if !(← acceptKeyword "stored") then discard <| acceptKeyword "virtual"
    else if ← acceptKeyword "as" then
      expectSymbol "("
      generated := some (← parseExpr)
      expectSymbol ")"
      if !(← acceptKeyword "stored") then discard <| acceptKeyword "virtual"
    else if ← acceptKeyword "not" then
      expectKeyword "null"
      notNull := true
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        notNullConflict := ← parseConflictAction
    else if ← acceptKeyword "null" then pure ()
    else if ← acceptKeyword "primary" then
      expectKeyword "key"
      primaryKey := true
      autoIncrement := ← acceptKeyword "autoincrement"
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        conflict := ← parseConflictAction
      if ← acceptKeyword "autoincrement" then autoIncrement := true
    else if ← acceptKeyword "unique" then
      unique := true
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        conflict := ← parseConflictAction
    else if ← acceptKeyword "references" then
      let table ← expectIdent
      let column ← if ← acceptSymbol "(" then
        let name ← expectIdent
        expectSymbol ")"
        pure (some name)
        else pure none
      let mut cascade := false
      let mut scanningActions := true
      while scanningActions do
        if ← acceptKeyword "on" then
          if ← acceptKeyword "delete" then
            if ← acceptKeyword "cascade" then cascade := true
            else if ← acceptKeyword "set" then discard <| advance
            else discard <| advance
          else if ← acceptKeyword "update" then discard <| advance
          else scanningActions := false
        else scanningActions := false
      references := some { table, column, onDeleteCascade := cascade }
    else if ← acceptKeyword "collate" then collation := ← expectIdent
    else if ← acceptKeyword "check" then
      expectSymbol "("
      let sourceStart ← currentTokenPos
      let expression ← parseExpr
      let sourceStop ← currentTokenPos
      let sourceSql ← tokenSource sourceStart sourceStop
      expectSymbol ")"
      check := some { expression, name := pendingConstraintName, sourceSql }
    else scanning := false
  pure (ColumnDef.mk name typ defaultValue generated notNull notNullConflict primaryKey unique conflict
    collation references check defaultSql autoIncrement)

private def parseTableAlias : ParserM (Option String) := do
  if ← acceptKeyword "as" then some <$> expectAlias
  else
    match ← peek with
    | .ident s =>
      if ["where", "order", "limit", "offset", "group", "having", "join", "left", "right", "full",
          "inner", "cross", "outer", "on", "using", "natural", "union", "intersect", "except", "returning"].contains s.toLower
      then pure none else some <$> expectIdent
    | _ => pure none

mutual
  private def parseTableFactorFuel : Nat → ParserM (Array TableRef)
    | 0 => throw "parser stack overflow"
    | fuel + 1 => do
      if ← acceptSymbol "(" then
        if isKeyword (← peek) "select" || isKeyword (← peek) "values" then
          let sql ← captureSubquery
          let alias ← parseTableAlias
          let columnAliases := (← parseOptionalNameList).getD #[]
          pure #[{ name := "(subquery-0)", alias, columnAliases, subquerySql := some sql }]
        else
          let refs ← parseFromItemsFuel fuel
          expectSymbol ")"
          let alias ← parseTableAlias
          discard <| parseOptionalNameList
          pure (match alias with
            | none => refs
            | some name => refs.map fun ref => { ref with alias := some name })
      else
        let (schema, objectName) ← parseQualifiedName
        let name := match schema with
          | some schemaName => schemaName ++ "." ++ objectName
          | none => objectName
        let alias ← parseTableAlias
        let columnAliases := (← parseOptionalNameList).getD #[]
        pure #[{ name, alias, columnAliases }]

  private def parseFromItemsFuel : Nat → ParserM (Array TableRef)
    | 0 => throw "parser stack overflow"
    | fuel + 1 => do
      let mut sources ← parseTableFactorFuel fuel
      let mut scanning := true
      while scanning do
        if ← acceptSymbol "," then
          let mut right ← parseTableFactorFuel fuel
          if ← acceptKeyword "on" then
            let condition ← parseExpr
            let last := right.size - 1
            if let some final := right[last]? then
              let combined := final.joinOn.map (fun prior => Expr.binary .and prior condition) |>.getD condition
              right := right.set! last { final with joinOn := some combined }
          sources := sources ++ right
        else
          let mut leftJoin := false
          let mut rightJoin := false
          let mut naturalJoin := false
          let joinStarter := match ← peek with
            | .ident word => ["natural", "left", "right", "full", "inner", "cross", "outer", "join"].contains word.toLower
            | _ => false
          if joinStarter then
            let mut words : Array String := #[]
            while !isKeyword (← peek) "join" do
              match ← advance with
              | .ident word => words := words.push word.toUpper
              | token => throw (syntaxError token)
            expectKeyword "join"
            let kind := String.intercalate " " words.toList
            if ["", "INNER", "CROSS"].contains kind then pure ()
            else if ["NATURAL", "NATURAL INNER", "NATURAL CROSS"].contains kind then
              naturalJoin := true
            else if ["LEFT", "LEFT OUTER"].contains kind then leftJoin := true
            else if ["RIGHT", "RIGHT OUTER"].contains kind then rightJoin := true
            else if ["FULL", "FULL OUTER"].contains kind then
              leftJoin := true
              rightJoin := true
            else if ["NATURAL LEFT", "NATURAL LEFT OUTER", "OUTER LEFT NATURAL"].contains kind then
              naturalJoin := true
              leftJoin := true
            else throw s!"unknown join type: {kind}"
            let mut right ← parseTableFactorFuel fuel
            let joinOn ← if ← acceptKeyword "on" then some <$> parseExpr else pure none
            let mut usingColumns := #[]
            if ← acceptKeyword "using" then
              if joinOn.isSome then throw "near \"USING\": syntax error"
              expectSymbol "("
              usingColumns := usingColumns.push (← expectIdent)
              while ← acceptSymbol "," do usingColumns := usingColumns.push (← expectIdent)
              expectSymbol ")"
            if naturalJoin && (joinOn.isSome || !usingColumns.isEmpty) then
              throw "a NATURAL join may not have an ON or USING clause"
            if let some first := right[0]? then
              let mergedUsing := first.usingColumns ++ usingColumns
              let mergedNatural := first.naturalJoin || naturalJoin
              let mergedLeft := first.leftJoin || leftJoin
              let mergedRight := first.rightJoin || rightJoin
              let updated := { first with
                usingColumns := mergedUsing
                naturalJoin := mergedNatural
                leftJoin := mergedLeft
                rightJoin := mergedRight }
              right := right.set! 0 updated
            if let some condition := joinOn then
              let last := right.size - 1
              if let some final := right[last]? then
                let combined := final.joinOn.map (fun prior => Expr.binary .and prior condition) |>.getD condition
                right := right.set! last { final with joinOn := some combined }
            sources := sources ++ right
          else scanning := false
      pure sources

end

private def parserFromDepth : Nat := 1000

private def parseFromItems : ParserM (Array TableRef) :=
  parseFromItemsFuel (Nat.succ parserFromDepth)

private def parseValuesRows : ParserM (Array (Array Expr)) := do
  let mut rows := #[]
  let mut more := true
  while more do
    expectSymbol "("
    let mut row := #[]
    unless ← acceptSymbol ")" do
      row := row.push (← parseExpr)
      while ← acceptSymbol "," do row := row.push (← parseExpr)
      expectSymbol ")"
    rows := rows.push row
    more := ← acceptSymbol ","
  pure rows

private def valuesQuery (rows : Array (Array Expr)) : Select :=
  let columns := (rows[0]?.getD #[]).mapIdx fun i expression =>
    ({ expr := expression, alias := some s!"column{i + 1}", sourceSql := some expression.sql } : ResultColumn)
  { columns, valueRows := some rows }

private def parseResultColumn : ParserM ResultColumn := do
  let start ← currentTokenPos
  let expr ← parseExpr
  let stop ← currentTokenPos
  let sourceSql := some (← tokenSource start stop)
  let alias ←
    if ← acceptKeyword "as" then some <$> expectAlias
    else
      match ← peek with
      | .quotedIdent s _ | .string s => discard advance; pure (some s)
      | .ident s =>
        if ["from", "where", "order", "limit", "offset", "group", "having",
            "union", "intersect", "except", "asc", "desc", "returning"].contains s.toLower then pure none
        else discard advance; pure (some s)
      | _ => pure none
  pure { expr, alias, sourceSql }

private def parseSelectAfterSelectFuel : Nat → Bool → ParserM Select
  | 0, _ => throw "too many nested SELECT terms"
  | fuel + 1, compoundArm => do
    let distinct ← acceptKeyword "distinct"
    if !distinct then discard <| acceptKeyword "all"
    let mut columns := #[(← parseResultColumn)]
    while ← acceptSymbol "," do columns := columns.push (← parseResultColumn)
    let mut sources := #[]
    if ← acceptKeyword "from" then
      sources := ← parseFromItems
      if sources.size > 64 then throw "at most 64 tables in a join"
      if isKeyword (← peek) "using" then throw "a JOIN clause is required before USING"
    let where_ ← if ← acceptKeyword "where" then some <$> parseExpr else pure none
    let mut groupBy := #[]
    if ← acceptKeyword "group" then
      expectKeyword "by"
      groupBy := groupBy.push (← parseExpr)
      while ← acceptSymbol "," do groupBy := groupBy.push (← parseExpr)
    let having ← if ← acceptKeyword "having" then some <$> parseExpr else pure none
    let mut query : Select := { columns, sources, where_, groupBy, having, distinct }
    unless compoundArm do
      let mut scanningCompounds := true
      while scanningCompounds do
        let operation ← if ← acceptKeyword "union" then
            pure (some (if ← acceptKeyword "all" then CompoundOp.unionAll else .unionDistinct))
          else if ← acceptKeyword "except" then pure (some .except)
          else if ← acceptKeyword "intersect" then pure (some .intersect)
          else pure none
        match operation with
        | none => scanningCompounds := false
        | some operation =>
          let arm ← if ← acceptKeyword "select" then parseSelectAfterSelectFuel fuel true
            else if ← acceptKeyword "values" then valuesQuery <$> parseValuesRows
            else throw (syntaxError (← peek))
          query := { query with compounds := query.compounds.push (operation, arm) }
          if query.compounds.size >= 500 then throw "too many terms in compound SELECT"
      let mut orderBy := #[]
      if ← acceptKeyword "order" then
        expectKeyword "by"
        let e ← parseExpr
        let desc ← acceptKeyword "desc"
        if !desc then discard <| acceptKeyword "asc"
        let nullsFirst ← parseNullOrder
        orderBy := orderBy.push { expr := e, descending := desc, nullsFirst }
        while ← acceptSymbol "," do
          let e ← parseExpr
          let desc ← acceptKeyword "desc"
          if !desc then discard <| acceptKeyword "asc"
          let nullsFirst ← parseNullOrder
          orderBy := orderBy.push { expr := e, descending := desc, nullsFirst }
      let (limit, offset, hadLimit) ← parseLimitClause
      query := { query with orderBy, limit, offset }
      if !orderBy.isEmpty || hadLimit then
        let pending ← if ← acceptKeyword "union" then
            pure (some (if ← acceptKeyword "all" then "UNION ALL" else "UNION"))
          else if ← acceptKeyword "except" then pure (some "EXCEPT")
          else if ← acceptKeyword "intersect" then pure (some "INTERSECT")
          else pure none
        if let some operation := pending then
          if !orderBy.isEmpty then throw s!"ORDER BY clause should come after {operation} not before"
          else throw s!"LIMIT clause should come after {operation} not before"
    pure query

private def maxCompoundSelectDepth : Nat := 500

private def parseSelectAfterSelect (compoundArm : Bool := false) : ParserM Select :=
  parseSelectAfterSelectFuel (Nat.succ maxCompoundSelectDepth) compoundArm

private def parseValuesAfterValues (rows : Array (Array Expr)) : ParserM Select := do
  let mut query := valuesQuery rows
  let mut scanningCompounds := true
  while scanningCompounds do
    let operation ← if ← acceptKeyword "union" then
        pure (some (if ← acceptKeyword "all" then CompoundOp.unionAll else .unionDistinct))
      else if ← acceptKeyword "except" then pure (some .except)
      else if ← acceptKeyword "intersect" then pure (some .intersect)
      else pure none
    match operation with
    | none => scanningCompounds := false
    | some operation =>
      let arm ← if ← acceptKeyword "select" then parseSelectAfterSelect true
        else if ← acceptKeyword "values" then valuesQuery <$> parseValuesRows
        else throw (syntaxError (← peek))
      query := { query with compounds := query.compounds.push (operation, arm) }
      if query.compounds.size >= 500 then throw "too many terms in compound SELECT"
  let mut orderBy := #[]
  if ← acceptKeyword "order" then
    expectKeyword "by"
    let expression ← parseExpr
    let descending ← acceptKeyword "desc"
    if !descending then discard <| acceptKeyword "asc"
    let nullsFirst ← parseNullOrder
    orderBy := orderBy.push { expr := expression, descending, nullsFirst }
    while ← acceptSymbol "," do
      let expression ← parseExpr
      let descending ← acceptKeyword "desc"
      if !descending then discard <| acceptKeyword "asc"
      let nullsFirst ← parseNullOrder
      orderBy := orderBy.push { expr := expression, descending, nullsFirst }
  let (limit, offset, hadLimit) ← parseLimitClause
  query := { query with orderBy, limit, offset }
  if !orderBy.isEmpty || hadLimit then
    let pending ← if ← acceptKeyword "union" then
        pure (some (if ← acceptKeyword "all" then "UNION ALL" else "UNION"))
      else if ← acceptKeyword "except" then pure (some "EXCEPT")
      else if ← acceptKeyword "intersect" then pure (some "INTERSECT")
      else pure none
    if let some operation := pending then
      if !orderBy.isEmpty then throw s!"ORDER BY clause should come after {operation} not before"
      else throw s!"LIMIT clause should come after {operation} not before"
  pure query

private def inlineCteSourceFuel : Nat → Select → String → String → Array String → Select
  | 0, query, _, _, _ => query
  | fuel + 1, query, name, sourceSql, columns =>
    { query with
      sources := query.sources.map fun source =>
        if source.name.toLower == name.toLower && source.subquerySql.isNone then
          { source with subquerySql := some sourceSql, columnAliases := columns }
        else source
      compounds := query.compounds.map fun (operation, arm) =>
        (operation, inlineCteSourceFuel fuel arm name sourceSql columns) }

private def inlineCteSource (query : Select) (name sourceSql : String)
    (columns : Array String) : Select :=
  inlineCteSourceFuel query.compoundHeight query name sourceSql columns

private def parseWithSelectQuery : ParserM Select := do
  discard <| acceptKeyword "recursive"
  let name ← expectIdent
  let columns := (← parseOptionalNameList).getD #[]
  expectKeyword "as"
  if ← acceptKeyword "not" then expectKeyword "materialized"
  else discard <| acceptKeyword "materialized"
  expectSymbol "("
  let sourceStart ← currentTokenPos
  if ← acceptKeyword "select" then discard <| parseSelectAfterSelect
  else if ← acceptKeyword "values" then discard <| parseValuesAfterValues (← parseValuesRows)
  else throw (syntaxError (← peek))
  let sourceStop ← currentTokenPos
  let sourceSql ← tokenSource sourceStart sourceStop
  expectSymbol ")"
  expectKeyword "select"
  let body ← parseSelectAfterSelect
  pure (inlineCteSource body name sourceSql columns)

private def parseCreate (temporarySeen : Bool := false) (sourceStart : Option Nat := none) : ParserM Statement := do
  let temporary ← if temporarySeen then pure true
    else if ← acceptKeyword "temp" then pure true else acceptKeyword "temporary"
  if ← acceptKeyword "table" then
    let ifNotExists ← if ← acceptKeyword "if" then
      expectKeyword "not" *> expectKeyword "exists" *> pure true
      else pure false
    let (schema, objectName) ← parseQualifiedName
    let name := match schema with
      | some schemaName => schemaName ++ "." ++ objectName
      | none => if temporary then "temp." ++ objectName else objectName
    if ← acceptKeyword "as" then
      expectKeyword "select"
      pure (.createTableAs name (← parseSelectAfterSelect))
    else
      expectSymbol "("
      let mut columns := #[]
      let mut constraints := #[]
      unless ← acceptSymbol ")" do
        let mut more := true
        while more do
          if isKeyword (← peek) "primary" || isKeyword (← peek) "unique" ||
             isKeyword (← peek) "check" || isKeyword (← peek) "foreign" ||
             isKeyword (← peek) "constraint" then
            if let some constraint ← parseTableConstraint then
              constraints := constraints.push constraint
          else columns := columns.push (← parseColumnDef)
          more := ← acceptSymbol ","
        expectSymbol ")"
      if ← acceptKeyword "without" then expectKeyword "rowid"
      pure (.createTable name columns constraints ifNotExists)
  else if ← acceptKeyword "view" then
    let ifNotExists ← if ← acceptKeyword "if" then
      expectKeyword "not" *> expectKeyword "exists" *> pure true
      else pure false
    let name ← expectIdent
    let columns ← parseOptionalNameList
    expectKeyword "as"
    let query ← if ← acceptKeyword "select" then parseSelectAfterSelect
      else if ← acceptKeyword "with" then parseWithSelectQuery
      else throw (syntaxError (← peek))
    let sourceSql ← match sourceStart with
      | some start => tokenSource start (← currentTokenPos)
      | none => pure ""
    pure (.createView name columns query ifNotExists temporary sourceSql)
  else
    let unique ← acceptKeyword "unique"
    expectKeyword "index"
    let ifNotExists ← if ← acceptKeyword "if" then
      expectKeyword "not" *> expectKeyword "exists" *> pure true
      else pure false
    let (schema, objectName) ← parseQualifiedName
    let name := schema.map (· ++ "." ++ objectName) |>.getD objectName
    expectKeyword "on"
    let table ← expectIdent
    expectSymbol "("
    let mut expressions := #[]
    unless ← acceptSymbol ")" do
      let first ← parseExpr
      expressions := expressions.push first
      if !(← acceptKeyword "desc") then discard <| acceptKeyword "asc"
      while ← acceptSymbol "," do
        let term ← parseExpr
        expressions := expressions.push term
        if !(← acceptKeyword "desc") then discard <| acceptKeyword "asc"
      expectSymbol ")"
    let where_ ← if ← acceptKeyword "where" then some <$> parseExpr else pure none
    pure (.createIndex name table expressions unique where_ ifNotExists)

private def parseDmlTableName (insideTrigger : Bool) : ParserM String := do
  let first ← expectAlias
  if ← acceptSymbol "." then
    if insideTrigger then
      throw "qualified table names are not allowed on INSERT, UPDATE, and DELETE statements within triggers"
    else pure (first ++ "." ++ (← expectAlias))
  else pure first

private def parseInsert (initial : ConflictAction := .default)
    (insideTrigger : Bool := false) : ParserM Statement := do
  let mut conflict := initial
  let hasOr ← acceptKeyword "or"
  -- Conflict action, when present.
  if hasOr then
    conflict := ← parseConflictAction
  expectKeyword "into"
  let table ← parseDmlTableName insideTrigger
  -- An INSERT target alias is not a binding source for VALUES or RETURNING.
  -- UPSERT, the form which can use it, is not admitted by this Core grammar.
  if ← acceptKeyword "as" then discard <| expectAlias
  let columns ← parseOptionalNameList
  let statement : Statement ← do
    if ← acceptKeyword "default" then
      expectKeyword "values"
      pure (.insert table columns #[#[]] conflict)
    else if ← acceptKeyword "values" then
      let rows ← parseValuesRows
      if ["union", "except", "intersect"].any (isKeyword (← peek)) then
        pure (.insertSelect table columns (← parseValuesAfterValues rows) conflict)
      else pure (.insert table columns rows conflict)
    else if ← acceptKeyword "select" then
      pure (.insertSelect table columns (← parseSelectAfterSelect) conflict)
    else throw "expected VALUES, DEFAULT VALUES, or SELECT after INSERT"
  let mut returning := #[]
  if ← acceptKeyword "returning" then
    if insideTrigger then throw "cannot use RETURNING in a trigger"
    returning := returning.push (← parseResultColumn)
    while ← acceptSymbol "," do returning := returning.push (← parseResultColumn)
  match statement with
  | .insert target names rows policy _ => pure (.insert target names rows policy returning)
  | .insertSelect target names query policy _ => pure (.insertSelect target names query policy returning)
  | _ => throw "invalid INSERT source"

private def parseDelete (insideTrigger : Bool := false) : ParserM Statement := do
  expectKeyword "from"
  let table ← parseDmlTableName insideTrigger
  if ← acceptKeyword "not" then
    expectKeyword "indexed"
    if insideTrigger then
      throw "the NOT INDEXED clause is not allowed on UPDATE or DELETE statements within triggers"
  if ← acceptKeyword "indexed" then
    expectKeyword "by"
    discard <| expectIdent
    if insideTrigger then
      throw "the INDEXED BY clause is not allowed on UPDATE or DELETE statements within triggers"
  let alias ← if ← acceptKeyword "as" then some <$> expectAlias else pure none
  let where_ ← if ← acceptKeyword "where" then some <$> parseExpr else pure none
  let mut returning := #[]
  if ← acceptKeyword "returning" then
    returning := returning.push (← parseResultColumn)
    while ← acceptSymbol "," do returning := returning.push (← parseResultColumn)
  pure (.delete table alias where_ returning)

/-- Try a scalar, a row of scalars, then an extra grouping layer. Each
alternative starts at the same token state, and nesting is fuel bounded. -/
private def parseAssignmentValuesFuel : Nat → ParserM (Array Expr)
  | 0 => throw "parser stack overflow"
  | fuel + 1 => fun state =>
      let scalar : ParserM (Array Expr) := do return #[(← parseExpr)]
      let vector : ParserM (Array Expr) := do
        expectSymbol "("
        let mut expressions := #[(← parseExpr)]
        while ← acceptSymbol "," do expressions := expressions.push (← parseExpr)
        expectSymbol ")"
        return expressions
      let grouped : ParserM (Array Expr) := do
        expectSymbol "("
        let expressions ← parseAssignmentValuesFuel fuel
        expectSymbol ")"
        return expressions
      match scalar state with
      | .ok result => .ok result
      | .error _ => match vector state with
          | .ok result => .ok result
          | .error _ => grouped state

private def parseUpdateAssignment : ParserM (Array (String × Expr)) := do
  let names : Array String ← match ← parseOptionalNameList with
    | some names => pure names
    | none => do pure #[(← expectIdent)]
  expectSymbol "="
  let values ← parseAssignmentValuesFuel (parserExpressionDepth + 1)
  match SQLite.RowAssignment.bind names.toList values.toList with
  | .ok assignments => return assignments.toArray
  | .error message => throw message

private def parseUpdate (insideTrigger : Bool := false) : ParserM Statement := do
  let mut conflict := ConflictAction.default
  if ← acceptKeyword "or" then
    conflict := ← parseConflictAction
  let table ← parseDmlTableName insideTrigger
  if ← acceptKeyword "not" then
    expectKeyword "indexed"
    if insideTrigger then
      throw "the NOT INDEXED clause is not allowed on UPDATE or DELETE statements within triggers"
  if ← acceptKeyword "indexed" then
    expectKeyword "by"
    discard <| expectIdent
    if insideTrigger then
      throw "the INDEXED BY clause is not allowed on UPDATE or DELETE statements within triggers"
  let alias ← if ← acceptKeyword "as" then some <$> expectAlias else pure none
  expectKeyword "set"
  let mut assignments ← parseUpdateAssignment
  while ← acceptSymbol "," do
    assignments := assignments ++ (← parseUpdateAssignment)
  unless assignments.size ≤ SQLite.Limits.maxColumns do throw "too many columns in set list"
  let where_ ← if ← acceptKeyword "where" then some <$> parseExpr else pure none
  let mut returning := #[]
  if ← acceptKeyword "returning" then
    if insideTrigger then throw "cannot use RETURNING in a trigger"
    returning := returning.push (← parseResultColumn)
    while ← acceptSymbol "," do returning := returning.push (← parseResultColumn)
  pure (.update table alias assignments where_ conflict returning)

private def Select.referencesSourceFuel : Nat → Select → String → Bool
  | 0, _, _ => false
  | fuel + 1, query, name =>
    query.sources.any (fun source => source.name.toLower == name.toLower) ||
      query.compounds.any (fun compound => referencesSourceFuel fuel compound.2 name)

private def Select.referencesSource (query : Select) (name : String) : Bool :=
  query.referencesSourceFuel query.compoundHeight name

private def recursiveCteParts? (name : String) (query : Select) :
    Option (Select × Select × Bool) :=
  match query.compounds with
  | #[(operation, step)] =>
      if step.referencesSource name then
        some ({ query with compounds := #[], orderBy := #[], limit := none, offset := 0 },
          step, operation == .unionAll)
      else none
  | _ => none

private def parseWith : ParserM Statement := do
  let recursive ← acceptKeyword "recursive"
  let name ← expectIdent
  let columns := (← parseOptionalNameList).getD #[]
  expectKeyword "as"
  if ← acceptKeyword "not" then expectKeyword "materialized"
  else discard <| acceptKeyword "materialized"
  expectSymbol "("
  if recursive then
    let seed ← if ← acceptKeyword "values" then valuesQuery <$> parseValuesRows
      else if ← acceptKeyword "select" then parseSelectAfterSelect true
      else throw (syntaxError (← peek))
    expectKeyword "union"
    let all ← acceptKeyword "all"
    expectKeyword "select"
    let step ← parseSelectAfterSelect
    expectSymbol ")"
    let body ←
      if ← acceptKeyword "insert" then parseInsert
      else if ← acceptKeyword "replace" then parseInsert .replace
      else if ← acceptKeyword "update" then parseUpdate
      else if ← acceptKeyword "delete" then parseDelete
      else if ← acceptKeyword "select" then pure (.select (← parseSelectAfterSelect))
      else throw (syntaxError (← peek))
    pure (.withRecursive name columns seed step all body)
  else
    let source : Statement ←
      if ← acceptKeyword "select" then pure (Statement.select (← parseSelectAfterSelect))
      else if ← acceptKeyword "values" then pure (Statement.values (← parseValuesRows))
      else throw (syntaxError (← peek))
    expectSymbol ")"
    let body ←
      if ← acceptKeyword "insert" then parseInsert
      else if ← acceptKeyword "replace" then parseInsert .replace
      else if ← acceptKeyword "update" then parseUpdate
      else if ← acceptKeyword "delete" then parseDelete
      else if ← acceptKeyword "select" then pure (.select (← parseSelectAfterSelect))
      else throw (syntaxError (← peek))
    match source with
    | Statement.select query =>
        match recursiveCteParts? name query with
        | some (seed, step, all) => pure (.withRecursive name columns seed step all body)
        | none => pure (.withCte name columns source body)
    | _ => pure (.withCte name columns source body)

private def parseTrigger (temporary : Bool := false) (statementStart : Option Nat := none) : ParserM Statement := do
  let ifNotExists ← if ← acceptKeyword "if" then
    expectKeyword "not" *> expectKeyword "exists" *> pure true
    else pure false
  let (first, firstDisplay) ← expectDisplayedName
  let (name, displayName) ← if ← acceptSymbol "." then expectDisplayedName
    else pure (first, firstDisplay)
  let timing ← if ← acceptKeyword "before" then pure TriggerTiming.before
    else if ← acceptKeyword "after" then pure .after
    else if ← acceptKeyword "instead" then expectKeyword "of" *> pure .insteadOf
    else pure .before
  let event ← if ← acceptKeyword "delete" then pure TriggerEvent.delete
    else if ← acceptKeyword "insert" then pure TriggerEvent.insert
    else if ← acceptKeyword "update" then
      if ← acceptKeyword "of" then
        discard <| expectIdent
        while ← acceptSymbol "," do discard <| expectIdent
      pure TriggerEvent.update
    else throw "expected INSERT, UPDATE, or DELETE in trigger"
  expectKeyword "on"
  let table ← expectIdent
  if ← acceptKeyword "for" then discard (acceptKeyword "each"); discard (acceptKeyword "row")
  let when_ ← if ← acceptKeyword "when" then some <$> parseExpr else pure none
  expectKeyword "begin"
  let mut body := #[]
  while !isKeyword (← peek) "end" do
    if ← acceptKeyword "insert" then body := body.push (← parseInsert (insideTrigger := true))
    else if ← acceptKeyword "replace" then body := body.push (← parseInsert .replace true)
    else if ← acceptKeyword "update" then body := body.push (← parseUpdate true)
    else if ← acceptKeyword "delete" then body := body.push (← parseDelete true)
    else if ← acceptKeyword "select" then body := body.push (.select (← parseSelectAfterSelect))
    else
      while !(isSymbol (← peek) ";") && !isKeyword (← peek) "end" do discard advance
    discard <| acceptSymbol ";"
  expectKeyword "end"
  let stop ← currentTokenPos
  let sourceSql ← match statementStart with
    | some start => tokenSource start stop
    | none => pure ""
  pure (.createTrigger name table event timing when_ body ifNotExists temporary displayName sourceSql)

private def parseStatement : ParserM Statement := do
  let statementStart ← currentTokenPos
  if ← acceptKeyword "with" then parseWith
  else if ← acceptKeyword "create" then
    if ← acceptKeyword "trigger" then parseTrigger false (some statementStart)
    else if ← acceptKeyword "temp" then
      if ← acceptKeyword "trigger" then parseTrigger true (some statementStart) else parseCreate true (some statementStart)
    else if ← acceptKeyword "temporary" then
      if ← acceptKeyword "trigger" then parseTrigger true (some statementStart) else parseCreate true (some statementStart)
    else parseCreate false (some statementStart)
  else if ← acceptKeyword "drop" then
    if ← acceptKeyword "table" then
      let ifExists ← if ← acceptKeyword "if" then expectKeyword "exists" *> pure true else pure false
      pure (.dropTable (← expectIdent) ifExists)
    else if ← acceptKeyword "index" then
      let ifExists ← if ← acceptKeyword "if" then expectKeyword "exists" *> pure true else pure false
      pure (.dropIndex (← expectIdent) ifExists)
    else if ← acceptKeyword "view" then
      let ifExists ← if ← acceptKeyword "if" then expectKeyword "exists" *> pure true else pure false
      let (schema, name) ← parseQualifiedName
      let qualified := match schema with
        | some schemaName => schemaName ++ "." ++ name
        | none => name
      pure (.dropView qualified ifExists)
    else if ← acceptKeyword "trigger" then
      let ifExists ← if ← acceptKeyword "if" then expectKeyword "exists" *> pure true else pure false
      pure (.dropTrigger (← expectIdent) ifExists)
    else throw "expected TABLE, VIEW, INDEX, or TRIGGER after DROP"
  else if ← acceptKeyword "insert" then parseInsert
  else if ← acceptKeyword "replace" then parseInsert .replace
  else if ← acceptKeyword "select" then pure (.select (← parseSelectAfterSelect))
  else if ← acceptKeyword "values" then pure (.select (← parseValuesAfterValues (← parseValuesRows)))
  else if ← acceptKeyword "delete" then parseDelete
  else if ← acceptKeyword "update" then parseUpdate
  else if ← acceptKeyword "attach" then
    discard <| parseExpr
    discard <| acceptKeyword "as"
    discard <| expectIdent
    pure (.pragma "lean_attach" none)
  else if ← acceptKeyword "detach" then
    discard <| acceptKeyword "database"
    discard <| expectIdent
    pure (.pragma "lean_detach" none)
  else if ← acceptKeyword "alter" then
    expectKeyword "table"
    let table ← expectIdent
    if ← acceptKeyword "add" then
      discard <| acceptKeyword "column"
      pure (.alterAddColumn table (← parseColumnDef))
    else if ← acceptKeyword "rename" then
      discard <| acceptKeyword "column"
      let oldName ← expectIdent
      expectKeyword "to"
      pure (.alterRenameColumn table oldName (← expectIdent))
    else throw (syntaxError (← peek))
  else if ← acceptKeyword "begin" then discard <| acceptKeyword "transaction"; pure .begin
  else if ← acceptKeyword "commit" then discard <| acceptKeyword "transaction"; pure .commit
  else if ← acceptKeyword "end" then discard <| acceptKeyword "transaction"; pure .commit
  else if ← acceptKeyword "rollback" then discard <| acceptKeyword "transaction"; pure .rollback
  else if ← acceptKeyword "reindex" then pure .reindex
  else if ← acceptKeyword "analyze" then
    if (← peek) != .eof && !isSymbol (← peek) ";" then discard <| advance
    pure (.pragma "lean_analyze" none)
  else if ← acceptKeyword "vacuum" then
    if (← peek) != .eof && !isSymbol (← peek) ";" then discard <| advance
    pure (.pragma "lean_vacuum" none)
  else if ← acceptKeyword "pragma" then
    let first ← expectIdent
    let name ← if ← acceptSymbol "." then
      let second ← expectIdent
      pure (first ++ "." ++ second)
      else pure first
    let equals ← acceptSymbol "="
    let paren ← if equals then pure false else acceptSymbol "("
    let arg ← if equals || paren then
      let e ← parseExpr
      discard <| acceptSymbol ")"
      pure (some e)
      else pure none
    pure (.pragma name arg)
  else throw s!"unsupported statement beginning at {(← peek).render}"

private def parseStatementsM : ParserM (Array Statement) := do
  let mut out := #[]
  while (← peek) != .eof do
    while ← acceptSymbol ";" do pure ()
    unless (← peek) == .eof do
      out := out.push (← parseStatement)
      let semicolon ← acceptSymbol ";"
      unless semicolon || (← peek) == .eof do
        throw (syntaxError (← peek))
  pure out

/-- Run the total syntax parser over an already-tokenized input.  Exposing this
boundary lets the verified Core front end use one proof-producing lexical pass
and independently certify the resulting token-to-AST relation. -/
def parseTokens (tokens : Array Token) : Except String (Array Statement) :=
  (parseStatementsM.run { tokens }).map (·.1)

def parse (sql : String) : Except String (Array Statement) := do
  let tokens ← lex sql
  parseTokens tokens

/-- A successful parse exposes the proof-producing lexical trace used by the
live parser.  This is the text-to-token half of the verified front-end
boundary; token-to-AST correctness is stated separately by the Core grammar. -/
theorem parse_success_tokenizes {sql : String} {statements : Array Statement}
    (success : parse sql = .ok statements) :
    ∃ tokens : Array Token,
      lex sql = .ok tokens ∧ Tokenizes sql.toList tokens.toList := by
  cases tokenized : lex sql with
  | error message =>
      simp only [parse, tokenized] at success
      cases success
  | ok tokens =>
      exact ⟨tokens, rfl, lex_sound tokenized⟩

private def parseOne : ParserM (Option Statement) := do
  while ← acceptSymbol ";" do pure ()
  if (← peek) == .eof then pure none
  else
    let statement ← parseStatement
    let semicolon ← acceptSymbol ";"
    unless semicolon || (← peek) == .eof do throw (syntaxError (← peek))
    pure (some statement)

/-- Parse complete statements up to the first syntax error, retaining the valid prefix. -/
def parseProgress (sql : String) : Except String (Array Statement × Option String) := do
  let tokens ← lex sql
  let rec loop (fuel : Nat) (state : ParserState) (statements : Array Statement) :=
    match fuel with
    | 0 => (statements, some "parser progress limit exceeded")
    | fuel + 1 =>
      match parseOne.run state with
      | .error message => (statements, some message)
      | .ok (none, _) => (statements, none)
      | .ok (some statement, next) => loop fuel next (statements.push statement)
  pure (loop (tokens.size + 1) { tokens } #[])

end SQLeanite
