import SQLeanite.SQLite.CastType
import SQLeanite.SQLite.Limits
import SQLeanite.Syntax.UnaryOp

namespace SQLeanite

structure ParserState where
  tokens : Array Token
  pos : Nat := 0
  preserveWindowSyntax : Bool := true

abbrev ParserM := StateT ParserState (Except String)

def nextTokenAt (tokens : Array Token) (pos : Nat) : Nat × Token := Id.run do
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

def peek : ParserM Token := do
  let st ← get
  pure (nextTokenAt st.tokens st.pos).2

def peekAfter : ParserM Token := do
  let st ← get
  let (pos, _) := nextTokenAt st.tokens st.pos
  pure (nextTokenAt st.tokens (pos + 1)).2

def advance : ParserM Token := do
  let st ← get
  let (pos, tok) := nextTokenAt st.tokens st.pos
  set { st with pos := pos + 1 }
  pure tok

def currentTokenPos : ParserM Nat := do
  let st ← get
  pure (nextTokenAt st.tokens st.pos).1

def tokenSource (start stop : Nat) : ParserM String := do
  let st ← get
  pure (String.join ((st.tokens.extract start stop).toList.map Token.render)).trimAscii.toString

def keywordEq (s kw : String) : Bool := s.toLower == kw

def isKeyword (tok : Token) (kw : String) : Bool :=
  match tok with
  | .ident s => keywordEq s kw
  | _ => false

def syntaxError : Token → String
  | .eof => "incomplete input"
  | token => s!"near \"{token.render}\": syntax error"

def acceptKeyword (kw : String) : ParserM Bool := do
  if isKeyword (← peek) kw then advance *> pure true else pure false

def expectKeyword (kw : String) : ParserM Unit := do
  unless ← acceptKeyword kw do
    throw (syntaxError (← peek))

def isSymbol (tok : Token) (s : String) : Bool :=
  match tok with
  | .symbol x => x == s
  | _ => false

def acceptSymbol (s : String) : ParserM Bool := do
  if isSymbol (← peek) s then advance *> pure true else pure false

def expectSymbol (s : String) : ParserM Unit := do
  unless ← acceptSymbol s do throw (syntaxError (← peek))

def expectIdent : ParserM String := do
  let token ← advance
  let some name := SQLite.Identifier.nameToken token | throw (syntaxError token)
  pure name

def expectPragmaName : ParserM String := do
  let token ← advance
  let some name := SQLite.PragmaSyntax.nameToken false token | throw (syntaxError token)
  pure name

def parsePragmaArgument : ParserM Expr := do
  let negative ← acceptSymbol "-"
  let positive ← if negative then pure false else acceptSymbol "+"
  let token ← advance
  match SQLite.PragmaSyntax.numeric negative token with
  | some (value, source) => pure (.literal value (some source))
  | none =>
      if negative || positive then throw (syntaxError token)
      let some name := SQLite.PragmaSyntax.nameToken true token | throw (syntaxError token)
      match token with
      | .ident _ => pure (.column none name)
      | _ => pure (.literal (.text name))

def expectAlias : ParserM String := expectIdent

def parseImplicitAlias : ParserM (Option String) := do
  match SQLite.Identifier.aliasToken (← peek) with
  | none => pure none
  | some name => discard advance; pure (some name)

def parseQualifiedName : ParserM (Option String × String) := do
  let first ← expectIdent
  if ← acceptSymbol "." then pure (some first, ← expectIdent)
  else pure (none, first)

def expectDisplayedName : ParserM (String × String) := do
  match ← advance with
  | .ident name => pure (name, name)
  | .quotedIdent name source => pure (name, source)
  | .string name => pure (name, "'" ++ name.replace "'" "''" ++ "'")
  | token => throw (syntaxError token)

def captureSubquery : ParserM String := do
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

def parseCastType : ParserM String := do
  let start ← currentTokenPos
  let mut stop := start
  let mut depth := 0
  let mut scanning := true
  while scanning do
    match ← peek with
    | .symbol ")" =>
        if depth == 0 then scanning := false
        else depth := depth - 1; discard advance; stop := (← get).pos
    | .symbol "(" => depth := depth + 1; discard advance; stop := (← get).pos
    | .eof => throw "incomplete input"
    | _ => discard advance; stop := (← get).pos
  let source ← tokenSource start stop
  match SQLite.CastType.check source with
  | .ok name => pure name
  | .error message => throw message

def parseNullOrder : ParserM (Option Bool) := do
  if ← acceptKeyword "nulls" then
    if ← acceptKeyword "first" then return some true
    expectKeyword "last"
    return some false
  return none

def binaryInfo : Token → Option (BinaryOp × Nat)
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

def hexNibble? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' <= c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def decodeBlobChars : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
      let high ← hexNibble? high
      let low ← hexNibble? low
      return UInt8.ofNat (high * 16 + low) :: (← decodeBlobChars rest)
  | _ => none

def decodeBlob? (source : String) : Option (Array UInt8) :=
  (decodeBlobChars source.toList).map List.toArray

def parseInRhs (item : ParserM Expr) (argument : Expr) (negated : Bool) : ParserM Expr := do
  if ← acceptSymbol "(" then
    if isKeyword (← peek) "select" || isKeyword (← peek) "values" then
      let expression := Expr.inSubquery argument (← captureSubquery)
      return if negated then .unary .not expression else expression
    let mut values := #[]
    unless ← acceptSymbol ")" do
      values := values.push (← item)
      while ← acceptSymbol "," do values := values.push (← item)
      expectSymbol ")"
    return .inList argument values negated
  let start ← currentTokenPos
  discard parseQualifiedName
  let source ← tokenSource start (← currentTokenPos)
  let expression := Expr.inSubquery argument ("SELECT * FROM " ++ source)
  return if negated then .unary .not expression else expression

mutual
  def parseExprFuel : Nat → (minPrec : Nat := 0) → ParserM Expr
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
          lhs := .call "__sqlean_between" #[lhs, lower, upper] false
        else if minPrec <= 3 && isKeyword (← peek) "not" then
          discard <| advance
          if ← acceptKeyword "between" then
            let lower ← parseExprFuel fuel 3
            expectKeyword "and"
            let upper ← parseExprFuel fuel 4
            lhs := .unary .not (.call "__sqlean_between" #[lhs, lower, upper] false)
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
          else if ← acceptKeyword "regexp" then
            lhs := .unary .not (.call "regexp" #[(← parseExprFuel fuel 4), lhs] false)
          else if ← acceptKeyword "null" then
            lhs := .isNull lhs true
          else if ← acceptKeyword "in" then
            lhs := ← parseInRhs (parseExprFuel fuel 0) lhs true
          else throw (syntaxError (← peek))
        else if minPrec <= 3 && isKeyword (← peek) "regexp" then
          discard advance
          lhs := .call "regexp" #[(← parseExprFuel fuel 4), lhs] false
        else if minPrec <= 3 && isKeyword (← peek) "in" then
          discard <| advance
          lhs := ← parseInRhs (parseExprFuel fuel 0) lhs false
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

  def parseUnaryFuel : Nat → ParserM Expr
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

  def parseCallFuel (fuel : Nat) (name spelling : String) : ParserM Expr := do
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
        throw s!"too many arguments on function {spelling}"
      let call := Expr.call (if distinct then distinctAggregateName name else name) args false
      pure (if ordering.isEmpty then call else .call "__sqlean_aggregate_order" (#[call] ++ ordering) false)
    let filtered := isKeyword (← peek) "filter" && isSymbol (← peekAfter) "("
    let call ← if filtered then do
        discard advance
        expectSymbol "("
        expectKeyword "where"
        let condition ← parseExprFuel fuel
        expectSymbol ")"
        pure (Expr.call "__sqlean_aggregate_filter" #[call, condition] false)
      else pure call
    let next ← peekAfter
    let isWindow := isKeyword (← peek) "over" &&
      (isSymbol next "(" || SQLite.Identifier.windowNameToken next)
    if isWindow then
      discard advance
      let start ← currentTokenPos
      if ← acceptSymbol "(" then
        discard captureSubquery
      else discard expectIdent
      let specification ← tokenSource start (← currentTokenPos)
      if !(← get).preserveWindowSyntax then
        return match call with
          | .call name args star => .call ("lean_window_" ++ name) args star
          | other => other
      return .call "__sqlean_window" #[call, .literal (.text specification)] false
    return call

  def parsePrimaryFuel : Nat → ParserM Expr
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
      | .string s =>
        if ← acceptSymbol "." then
          if ← acceptSymbol "*" then pure (.star (some s))
          else pure (.column (some s) (← expectIdent))
        else pure (.literal (.text s))
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
        let st ← get
        let adjacentString := match st.tokens[st.pos]? with | some (.string _) => true | _ => false
        if keywordEq s "x" && adjacentString then
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
          let typeName ← parseCastType
          expectSymbol ")"
          pure (.call ("cast_" ++ typeName.toLower) #[argument] false)
        else if keywordEq s "raise" then
          expectSymbol "("
          if ← acceptKeyword "ignore" then
            expectSymbol ")"
            pure (.call "__sqlean_raise_ignore" #[] false)
          else
            let action ← if ← acceptKeyword "abort" then pure "abort"
              else if ← acceptKeyword "fail" then pure "fail"
              else if ← acceptKeyword "rollback" then pure "rollback"
              else throw (syntaxError (← peek))
            expectSymbol ","
            let message ← parseExprFuel fuel
            expectSymbol ")"
            pure (.call ("__sqlean_raise_" ++ action) #[message] false)
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
        else if ["current_date", "current_time", "current_timestamp"].contains s.toLower then
          pure (.call s #[] false)
        else if (SQLite.Identifier.primaryToken false (.ident s)).isNone then
          throw (syntaxError (.ident s))
        else if ← acceptSymbol "(" then
          parseCallFuel fuel s s
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
      | .quotedIdent s spelling =>
        if ← acceptSymbol "(" then parseCallFuel fuel s spelling
        else if ← acceptSymbol "." then
          if ← acceptSymbol "*" then pure (.star (some s))
          else pure (.column (some s) (← expectIdent))
        else pure (.call "lean_dqs" #[.literal (.text s)] false)
      | tok => throw (syntaxError tok)
end

def parserExpressionDepth : Nat := 1000

def parseExpr (minPrec : Nat := 0) : ParserM Expr :=
  parseExprFuel (Nat.succ parserExpressionDepth) minPrec

def parseUnary : ParserM Expr :=
  parseUnaryFuel (Nat.succ parserExpressionDepth)

end SQLeanite
