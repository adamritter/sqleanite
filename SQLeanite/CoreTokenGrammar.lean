import SQLeanite.Parser

namespace SQLeanite
namespace CoreTokenGrammar

/-!
# Independent concrete grammar for the live Core SQL surface

The broad compatibility parser proposes an AST.  This module does not call any
of its recursive-descent routines: it independently replays the significant
token stream against that exact AST.  Consequently a successful certificate
checks names, literal values, operator-tree precedence, delimiters, statement
boundaries, aliases, joins, and transaction commands rather than trusting the
parser's final equation.

The checker is intentionally narrower than the compatibility parser.  Syntax
which the verified Core cannot execute is rejected here and remains available
only to the legacy conformance fixture.
-/

def significant : List Token → List Token
  | [] => []
  | .space _ :: tokens => significant tokens
  | token :: tokens => token :: significant tokens

structure MatchState where
  remaining : List Token

abbrev MatchM := StateT MatchState (Except String)

private def mismatch (expected : String) : MatchM α := do
  let state ← get
  let found := (significant state.remaining).head?.map Token.render
    |>.getD "end of input"
  throw s!"verified grammar expected {expected}, found {found}"

private def nextSignificant : List Token → Token × List Token
  | [] => (.eof, [])
  | .space _ :: tokens => nextSignificant tokens
  | token :: tokens => (token, tokens)

private def peek : MatchM Token := do
  return (nextSignificant (← get).remaining).1

private def advance : MatchM Token := do
  let state ← get
  let (token, tokens) := nextSignificant state.remaining
  set ({ remaining := tokens } : MatchState)
  return token

private def tokenName? : Token → Option String
  | .ident name | .quotedIdent name _ | .string name => some name
  | _ => none

private def isKeyword (token : Token) (word : String) : Bool :=
  match token with
  | .ident name => name.toLower == word
  | _ => false

private def isSymbol (token : Token) (symbol : String) : Bool :=
  match token with
  | .symbol found => found == symbol
  | _ => false

private def acceptKeyword (word : String) : MatchM Bool := do
  if isKeyword (← peek) word then
    discard <| advance
    return true
  return false

private def expectKeyword (word : String) : MatchM Unit := do
  unless ← acceptKeyword word do mismatch word.toUpper

private def acceptSymbol (symbol : String) : MatchM Bool := do
  if isSymbol (← peek) symbol then
    discard <| advance
    return true
  return false

private def expectSymbol (symbol : String) : MatchM Unit := do
  unless ← acceptSymbol symbol do mismatch symbol

private def expectName (expected : String) : MatchM Unit := do
  match SQLite.Identifier.nameToken (← advance) with
  | some found =>
      unless found.toLower == expected.toLower do mismatch s!"name {expected}"
  | none => mismatch s!"name {expected}"

private def expectPrimaryName (qualified : Bool) (expected : String) : MatchM Unit := do
  let some found := SQLite.Identifier.primaryToken qualified (← advance) | mismatch "an expression identifier"
  unless found.toLower == expected.toLower do mismatch "the parsed expression identifier"

/-- A newly declared name is stored verbatim, so case is semantic metadata
here even though references to an existing name compare case-insensitively. -/
private def expectDeclaredName (expected : String) : MatchM Unit := do
  match SQLite.Identifier.nameToken (← advance) with
  | some found => unless found == expected do mismatch s!"declared name {expected}"
  | none => mismatch s!"declared name {expected}"

/-- The current AST does not distinguish a schema qualifier from a period in
one quoted identifier. Admit one object-name token until that metadata is
represented explicitly; never reinterpret a quoted period as a qualifier. -/
private def expectObjectName (expected : String) : MatchM Unit :=
  expectName expected

private def expectSemanticToken (expected : Token) : MatchM Unit := do
  let found ← advance
  let namesMatch := match tokenName? expected, tokenName? found with
    | some left, some right => left.toLower == right.toLower
    | _, _ => false
  unless namesMatch || found == expected do
    mismatch expected.render

private def matchCastType (expected : String) : MatchM Unit := do
  let before := (← get).remaining.dropWhile fun token => match token with | .space _ => true | _ => false
  let mut after := before
  let mut depth := 0
  let mut scanning := true
  while scanning do
    match ← peek with
    | .symbol ")" =>
        if depth == 0 then scanning := false
        else depth := depth - 1; discard advance; after := (← get).remaining
    | .symbol "(" => depth := depth + 1; discard advance; after := (← get).remaining
    | .eof => mismatch "a closed CAST expression"
    | _ => discard advance; after := (← get).remaining
  let source := String.join ((before.take (before.length - after.length)).map Token.render)
  let actual ← match SQLite.CastType.check source with
    | .ok name => pure name
    | .error _ => mismatch "a legal CAST type"
  unless actual.toLower == expected do mismatch "the CAST type semantics"

private def sourceTokens (source : String) : Except String (List Token) := do
  let tokens ← lex source
  return (significant tokens.toList).filter (· != .eof)

private def expectSource (source : String) : MatchM Unit := do
  for token in ← sourceTokens source do expectSemanticToken token

private def expectConflict : ConflictAction → MatchM Unit
  | .rollback => expectKeyword "rollback"
  | .abort => expectKeyword "abort"
  | .fail => expectKeyword "fail"
  | .replace => expectKeyword "replace"
  | .ignore => expectKeyword "ignore"
  | .default => mismatch "an explicit conflict action"

private def matchConflictAction : MatchM ConflictAction := do
  let token ← peek
  let result ← if isKeyword token "abort" then pure ConflictAction.abort
    else if isKeyword token "ignore" then pure .ignore
    else if isKeyword token "replace" then pure .replace
    else if isKeyword token "fail" then pure .fail
    else if isKeyword token "rollback" then pure .rollback
    else mismatch "an explicit conflict action"
  discard advance
  return result

private def expectInteger (expected : Int) : MatchM Unit := do
  match ← peek with
  | .integer found _ =>
      discard advance
      unless found == expected do mismatch s!"integer {expected}"
  | _ =>
      unless expected < 0 do mismatch s!"integer {expected}"
      expectSymbol "-"
      match ← advance with
      | .integer found _ =>
          unless found == -expected do mismatch s!"integer {expected}"
      | _ => mismatch s!"integer {expected}"

private def expectNat (expected : Nat) : MatchM Unit :=
  expectInteger (Int.ofNat expected)

private def expectBinaryOp : BinaryOp → MatchM Unit
  | .add => expectSymbol "+"
  | .sub => expectSymbol "-"
  | .mul => expectSymbol "*"
  | .div => expectSymbol "/"
  | .mod => expectSymbol "%"
  | .eq => do
      let token ← advance
      unless isSymbol token "=" || isSymbol token "==" do mismatch "="
  | .ne => do
      let token ← advance
      unless isSymbol token "!=" || isSymbol token "<>" do mismatch "!="
  | .lt => expectSymbol "<"
  | .le => expectSymbol "<="
  | .gt => expectSymbol ">"
  | .ge => expectSymbol ">="
  | .is => do
      expectKeyword "is"
      if ← acceptKeyword "not" then
        expectKeyword "distinct"
        expectKeyword "from"
  | .isNot => do
      expectKeyword "is"
      unless ← acceptKeyword "not" do
        expectKeyword "distinct"
        expectKeyword "from"
  | .like => expectKeyword "like"
  | .glob => expectKeyword "glob"
  | .match => expectKeyword "match"
  | .and => expectKeyword "and"
  | .or => expectKeyword "or"
  | .concat => expectSymbol "||"
  | .bitAnd => expectSymbol "&"
  | .bitOr => expectSymbol "|"
  | .shiftLeft => expectSymbol "<<"
  | .shiftRight => expectSymbol ">>"
  | .arrow => expectSymbol "->"
  | .arrowText => expectSymbol "->>"

private def expectLiteral : Value → MatchM Unit
  | .null => expectKeyword "null"
  | .integer value => expectInteger value
  | .real value => do
      match ← advance with
      | .real source =>
          match parseDecimal? (SQLite.NumericLiteral.normalize source) with
          | some found => unless found == value do mismatch "the parsed REAL literal"
          | none => mismatch "a REAL literal"
      | .integer source _ =>
          unless source > 9223372036854775807 && Float.ofInt source == value do mismatch "the parsed REAL literal"
      | _ => mismatch "a REAL literal"
  | .text value => do
      match ← advance with
      | .string found => unless found == value do mismatch "the parsed text literal"
      | _ => mismatch "a text literal"
  | .textBytes _ => mismatch "a source literal (raw TEXT requires CAST)"
  | .blob value => do
      let initial ← get
      let lead ← advance
      unless (match lead with | .ident name => name.toLower == "x" | _ => false) do
        mismatch "the unquoted X blob prefix"
      unless (match (← get).remaining.head? with | some (.string _) => true | _ => false) do
        mismatch "an adjacent blob quote"
      set initial
      expectSource (toString (Value.blob value))

/-- Numeric spelling is checked independently against the original token,
including SQLite's removal of digit separators and its compact integer form.
Dropping or changing the retained spelling cannot forge expression identity. -/
private def expectLiteralSpelling (value : Value) (spelling : Option String) : MatchM Unit := do
  let expected ← match ← peek with
    | .real source => pure (some (SQLite.NumericLiteral.normalize source))
    | .integer value source => pure (SQLite.NumericLiteral.integerSpelling value (source.getD (toString value)))
    | .symbol "-" =>
        let tail := (nextSignificant (← get).remaining).2
        match (nextSignificant tail).1, value with
        | .integer magnitude source, .integer integer =>
            if magnitude == 9223372036854775808 && integer == -9223372036854775808 then
              pure (some ("-" ++ SQLite.NumericLiteral.normalize (source.getD (toString magnitude))))
            else pure none
        | _, _ => pure none
    | _ => pure none
  unless spelling == expected do mismatch "the normalized numeric token spelling"
  expectLiteral value

mutual
  private def matchExprFuel : Nat → Expr → MatchM Unit
    | 0, _ => mismatch "an expression within the grammar depth bound"
    | fuel + 1, expression => fun state =>
        if isSymbol (nextSignificant state.remaining).1 "(" then
          let wrapped : MatchM Unit := do
            expectSymbol "("
            matchExprFuel fuel expression
            expectSymbol ")"
          match wrapped state with
          | .ok result => .ok result
          -- Parentheses may wrap the left operand, not the whole expression:
          -- (1+2)*3. Retry the AST node against the original token state.
          | .error _ => matchExprAlternative fuel expression state
        else matchExprAlternative fuel expression state

  private def matchExprAlternative (fuel : Nat) (expression : Expr) : MatchM Unit :=
    fun state =>
      let between : MatchM Unit := do
        let (body, negated) := match expression with
          | .unary .not body => (body, true)
          | body => (body, false)
        match body with
        | .binary .and (.binary .ge left lower) (.binary .le repeated upper) =>
            let start ← get
            matchExprFuel fuel left
            let afterLeft ← get
            -- BETWEEN duplicates the left operand in the proposed AST.
            -- Replay both occurrences against exactly the same source span.
            set start
            matchExprFuel fuel repeated
            unless (← get).remaining == afterLeft.remaining do
              mismatch "the same BETWEEN operand"
            if negated then expectKeyword "not"
            expectKeyword "between"
            matchExprFuel fuel lower
            expectKeyword "and"
            matchExprFuel fuel upper
        | _ => mismatch "a BETWEEN expression"
      let pattern : MatchM Unit := do
        let (body, negated) := match expression with
          | .unary .not body => (body, true)
          | body => (body, false)
        match body with
        | .binary op left right =>
            unless op == .like || op == .glob do mismatch "LIKE or GLOB"
            matchExprFuel fuel left
            if negated then expectKeyword "not"
            expectBinaryOp op
            matchExprFuel fuel right
        | .call "regexp" arguments false =>
            match arguments.toList with
            | [pattern, input] =>
                matchExprFuel fuel input
                if negated then expectKeyword "not"
                expectKeyword "regexp"
                matchExprFuel fuel pattern
            | _ => mismatch "REGEXP expression"
        | .call "like" arguments false =>
            match arguments.toList with
            | [pattern, input, escape] =>
                matchExprFuel fuel input
                if negated then expectKeyword "not"
                expectKeyword "like"
                matchExprFuel fuel pattern
                expectKeyword "escape"
                matchExprFuel fuel escape
            | _ => mismatch "LIKE ... ESCAPE"
        | _ => mismatch "a pattern expression"
      match between state with
      | .ok result => .ok result
      | .error _ => match pattern state with
          | .ok result => .ok result
          | .error _ => matchExprCore fuel expression state

  private def matchExprCore : Nat → Expr → MatchM Unit
    | _, .literal value spelling => expectLiteralSpelling value spelling
    | _, .column none name => expectPrimaryName false name
    | _, .column (some qualifier) name =>
        expectPrimaryName true qualifier *> expectSymbol "." *> expectName name
    | _, .star none => expectSymbol "*"
    | _, .star (some qualifier) =>
        expectPrimaryName true qualifier *> expectSymbol "." *> expectSymbol "*"
    | fuel, .unary operation argument => do
        match operation with
        | .plus => expectSymbol "+"
        | .neg => expectSymbol "-"
        | .not => expectKeyword "not"
        | .bitNot => expectSymbol "~"
        matchExprFuel fuel argument
    | fuel, .binary operation left right => do
        matchExprFuel fuel left
        expectBinaryOp operation
        matchExprFuel fuel right
    | fuel, .call name arguments star => do
        unless name == "__sqlean_aggregate_order" || arguments.size ≤ SQLite.Limits.maxFunctionArgs do
          mismatch "at most 1000 function arguments"
        if name == "__sqlean_aggregate_order" then
          match arguments.toList, star with
          | .call function inputs false :: ordering, false =>
              unless inputs.size ≤ SQLite.Limits.maxFunctionArgs &&
                  !ordering.isEmpty && ordering.length ≤ SQLite.Limits.maxColumns do
                mismatch "aggregate arguments and ORDER BY terms within their limits"
              expectName (aggregateFunctionName function)
              expectSymbol "("
              if isDistinctAggregateName function then expectKeyword "distinct"
              else discard <| acceptKeyword "all"
              match inputs.toList with
              | [] => pure ()
              | first :: rest =>
                  matchExprFuel fuel first
                  for next in rest do
                    expectSymbol ","
                    matchExprFuel fuel next
              expectKeyword "order"
              expectKeyword "by"
              let mut first := true
              for encoded in ordering do
                if !first then expectSymbol ","
                first := false
                let some term := AggregateOrder.decode? encoded | mismatch "an aggregate ORDER BY term"
                matchExprFuel fuel term.expr
                if term.descending then expectKeyword "desc"
                else discard <| acceptKeyword "asc"
                if let some nullsFirst := term.nullsFirst then
                  expectKeyword "nulls"
                  expectKeyword (if nullsFirst then "first" else "last")
              expectSymbol ")"
          | _, _ => mismatch "aggregate ORDER BY syntax"
        else if name == "__sqlean_aggregate_filter" then
          match arguments.toList, star with
          | [aggregate, condition], false =>
              matchExprFuel fuel aggregate
              expectKeyword "filter"
              expectSymbol "("
              expectKeyword "where"
              matchExprFuel fuel condition
              expectSymbol ")"
          | _, _ => mismatch "aggregate FILTER (WHERE expression)"
        else if name == "__sqlean_boolean_true" || name == "__sqlean_boolean_false" then
          unless arguments.isEmpty && !star do mismatch "a boolean keyword"
          expectKeyword (if name == "__sqlean_boolean_true" then "true" else "false")
        else if name == "lean_dqs" then
          match arguments.toList, star with
          | [.literal (.text expected)], false =>
              match ← advance with
              | .quotedIdent found _ =>
                  unless found.toLower == expected.toLower do
                    mismatch s!"quoted identifier {expected}"
              | _ => mismatch s!"quoted identifier {expected}"
          | _, _ => mismatch "a supported quoted identifier"
        else if name.toLower.startsWith "cast_" then
          match arguments.toList, star with
          | [argument], false =>
              expectKeyword "cast"
              expectSymbol "("
              matchExprFuel fuel argument
              expectKeyword "as"
              matchCastType (name.drop 5).toString
              expectSymbol ")"
          | _, _ => mismatch "CAST(expression AS type)"
        else
          let distinct := isDistinctAggregateName name
          let displayed := aggregateFunctionName name
          expectName displayed
          expectSymbol "("
          if star then
            expectSymbol "*"
          else
            if distinct then expectKeyword "distinct"
            else discard <| acceptKeyword "all"
            match arguments.toList with
            | [] => pure ()
            | argument :: rest =>
                matchExprFuel fuel argument
                for next in rest do
                  expectSymbol ","
                  matchExprFuel fuel next
          expectSymbol ")"
    | fuel, .isNull argument negated => do
        matchExprFuel fuel argument
        if !negated && (← acceptKeyword "isnull") then return
        if negated && (← acceptKeyword "notnull") then return
        if negated && (← acceptKeyword "not") then
          expectKeyword "null"
          return
        expectKeyword "is"
        if negated then expectKeyword "not"
        matchExprFuel fuel (.literal .null)
    | fuel, .inList argument values negated _ => do
        matchExprFuel fuel argument
        if negated then expectKeyword "not"
        expectKeyword "in"
        expectSymbol "("
        match values.toList with
        | [] => pure ()
        | value :: rest =>
            matchExprFuel fuel value
            for next in rest do
              expectSymbol ","
              matchExprFuel fuel next
        expectSymbol ")"
    | fuel, .collate argument name =>
        matchExprFuel fuel argument *> expectKeyword "collate" *> expectName name
    | fuel, .case_ base branches otherwise => do
        expectKeyword "case"
        if let some expression := base then matchExprFuel fuel expression
        if branches.isEmpty then mismatch "at least one WHEN branch"
        for (condition, result) in branches do
          expectKeyword "when"
          matchExprFuel fuel condition
          expectKeyword "then"
          matchExprFuel fuel result
        if let some expression := otherwise then
          expectKeyword "else"
          matchExprFuel fuel expression
        expectKeyword "end"
    | _, .scalarSubquery _ => mismatch "a Core expression (subquery is outside the subset)"
    | _, .inSubquery _ _ _ => mismatch "a Core expression (subquery is outside the subset)"
    | _, .existsSubquery _ => mismatch "a Core expression (subquery is outside the subset)"
end

private def matchExpr (expression : Expr) : MatchM Unit := do
  -- The compatibility parser admits at most 1000 nested expression levels.
  -- A fixed allowance avoids recomputing the remaining token-list length for
  -- every literal in a bulk INSERT (which would make certification quadratic).
  matchExprFuel (expression.height + 1001) expression

/-- Replay the original expressions and independently derive the normalized
execution window. No computed count can substitute for source-token checking. -/
private def matchLimit (query : Select) (deferErrors : Bool := false) : MatchM Unit := do
  match query.limitClause with
  | none =>
      unless query.limit.isNone && query.offset == 0 do mismatch "LIMIT/OFFSET clause"
  | some clause =>
      expectKeyword "limit"
      if clause.comma then
        let some offset := clause.offset | mismatch "a comma LIMIT offset"
        matchExpr offset
        expectSymbol ","
        matchExpr clause.count
      else
        matchExpr clause.count
        if let some offset := clause.offset then
          expectKeyword "offset"
          matchExpr offset
      let (limit, offset) ← match SQLite.Limit.resolve clause with
        | .ok result => pure result
        | .error _ =>
            if deferErrors then pure (none, 0)
            else mismatch "admitted LIMIT/OFFSET expressions"
      unless query.limit == limit && query.offset == offset do
        mismatch "the translated LIMIT/OFFSET values"

private def matchExprList : List Expr → MatchM Unit
  | [] => pure ()
  | expression :: expressions => do
      matchExpr expression
      for next in expressions do
        expectSymbol ","
        matchExpr next

/-- ASC is the default index order. DESC remains rejected until the AST and
physical index metadata can retain and execute that ordering. -/
private def matchAscendingIndexExprs : List Expr → MatchM Unit
  | [] => pure ()
  | expression :: expressions => do
      matchExpr expression
      discard <| acceptKeyword "asc"
      for next in expressions do
        expectSymbol ","
        matchExpr next
        discard <| acceptKeyword "asc"

private def matchPragmaName (expected : String) : MatchM Unit := do
  let some found := SQLite.PragmaSyntax.nameToken false (← advance) |
    mismatch "a PRAGMA or schema name"
  unless found.toLower == expected.toLower do mismatch "the parsed PRAGMA or schema name"

/-- Replay one atom and its optional sign, independently of parsePragmaArgument.
In this context source spelling is retained even for compact integer literals. -/
private def matchPragmaArgument (expression : Expr) : MatchM Unit := do
  let negative ← acceptSymbol "-"
  let positive ← if negative then pure false else acceptSymbol "+"
  let token ← advance
  match SQLite.PragmaSyntax.numeric negative token with
  | some (value, source) =>
      match expression with
      | .literal expected spelling =>
          unless expected == value && spelling == some source do
            mismatch "the PRAGMA numeric value and original spelling"
      | _ => mismatch "a numeric PRAGMA argument"
  | none =>
      if negative || positive then mismatch "a signed numeric PRAGMA argument"
      let some name := SQLite.PragmaSyntax.nameToken true token | mismatch "a PRAGMA name argument"
      match expression with
      | .column none expected | .literal (.text expected) none =>
          unless name == expected do mismatch "the original PRAGMA argument name"
      | _ => mismatch "a PRAGMA name argument"

private def matchNameList : List String → MatchM Unit
  | [] => pure ()
  | name :: names => do
      expectName name
      for next in names do
        expectSymbol ","
        expectName next

private def matchOptionalNameList : Option (Array String) → MatchM Unit
  | none => pure ()
  | some names =>
      expectSymbol "(" *> matchNameList names.toList <* expectSymbol ")"

private def matchAlias : Option String → MatchM Unit
  | none => pure ()
  | some alias => do
      if ← acceptKeyword "as" then expectDeclaredName alias
      else
        let some found := SQLite.Identifier.aliasToken (← advance) | mismatch "an implicit alias"
        unless found == alias do mismatch "the declared implicit alias"

private def matchDefault (expression : Expr) (source : String) : MatchM Unit := do
  let before := (← get).remaining.dropWhile fun token => match token with | .space _ => true | _ => false
  let token ← peek
  match token, expression with
  | .ident name, .literal (.text text) none =>
      unless SQLite.DefaultSyntax.identifier name && name == text &&
          !["true", "false", "current_time", "current_date", "current_timestamp"].contains name.toLower do
        mismatch "an identifier DEFAULT string"
      discard <| advance
  | .quotedIdent name _, .literal (.text text) none =>
      unless name == text do mismatch "a quoted DEFAULT string"
      discard <| advance
  | _, _ => matchExpr expression
  let after := (← get).remaining
  let consumed := before.take (before.length - after.length)
  unless SQLite.DefaultSyntax.shape (significant consumed) &&
      (String.join (consumed.map Token.render)).trimAscii.toString == source do
    mismatch "the complete original DEFAULT source"

private def matchConstraintName : MatchM Unit := do
  unless (SQLite.PragmaSyntax.nameToken false (← advance)).isSome do
    mismatch "a legal constraint name"

private def matchColumnConstraints (column : ColumnDef) : MatchM Unit := do
  unless column.generated.isNone &&
      !column.unique && column.references.isNone && column.check.isNone do
    mismatch "a verified-Core column definition"
  let finalDefault ← match column.defaultValue, column.defaultSql with
    | none, none => pure []
    | some expression, some source => pure [(expression, source)]
    | _, _ => mismatch "consistent DEFAULT metadata"
  let defaults := column.earlierDefaults.toList ++ finalDefault
  let mut defaultIndex := 0
  let mut sawNotNull := false
  let mut notNullConflict := ConflictAction.abort
  let mut sawPrimary := false
  let mut sawAutoIncrement := false
  let mut primaryConflict := ConflictAction.abort
  let mut sawCollation := false
  let mut scanning := true
  while scanning do
    if ← acceptKeyword "constraint" then matchConstraintName
    else if ← acceptKeyword "default" then
      let some (expression, source) := defaults[defaultIndex]? | mismatch "a declared DEFAULT clause"
      matchDefault expression source
      defaultIndex := defaultIndex + 1
    else if isKeyword (← peek) "not" then
      expectKeyword "not"
      expectKeyword "null"
      sawNotNull := true
      notNullConflict := .abort
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        notNullConflict := ← matchConflictAction
    else if isKeyword (← peek) "null" then
      expectKeyword "null"
    else if isKeyword (← peek) "primary" then
      expectKeyword "primary"
      expectKeyword "key"
      sawPrimary := true
      primaryConflict := .abort
      discard <| acceptKeyword "asc"
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        primaryConflict := ← matchConflictAction
      sawAutoIncrement := ← acceptKeyword "autoincrement"
    else if isKeyword (← peek) "collate" then
      expectKeyword "collate"
      expectName column.collation
      sawCollation := true
    else
      scanning := false
  unless defaultIndex == defaults.length && sawNotNull == column.notNull && notNullConflict == column.notNullConflict && sawPrimary == column.primaryKey && sawAutoIncrement == column.autoIncrement && primaryConflict == column.conflict &&
      (sawCollation || column.collation.toLower == "binary") do
    mismatch s!"the parsed constraints for column {column.name}"

private def matchDeclaredType (source : String) : MatchM Unit := do
  unless SQLite.ColumnType.valid source do mismatch "a legal column type"
  unless source.isEmpty do
    let before := (← get).remaining.dropWhile fun token => match token with | .space _ => true | _ => false
    expectSource source
    let after := (← get).remaining
    let actual := (String.join ((before.take (before.length - after.length)).map Token.render)).trimAscii.toString
    unless actual == source do mismatch "the exact column type source"

private def matchColumn (column : ColumnDef) : MatchM Unit := do
  expectDeclaredName column.name
  matchDeclaredType column.declaredType
  matchColumnConstraints column

private def matchColumns : List ColumnDef → MatchM Unit
  | [] => pure ()
  | column :: columns => do
      matchColumn column
      for next in columns do
        expectSymbol ","
        matchColumn next

private def matchTablePrimary (constraint : TableConstraintDef) : MatchM Unit := do
  unless constraint.primaryKey && constraint.columns.size == 1 &&
      constraint.collations.size == 1 && constraint.descending.size == 1 &&
      constraint.check.isNone do
    mismatch "a single-column table PRIMARY KEY"
  expectKeyword "primary"
  expectKeyword "key"
  expectSymbol "("
  expectName constraint.columns[0]!
  if let some collation := constraint.collations[0]! then
    expectKeyword "collate"
    expectName collation
  if constraint.descending[0]! then expectKeyword "desc"
  else discard <| acceptKeyword "asc"
  if constraint.autoIncrement then expectKeyword "autoincrement"
  expectSymbol ")"
  if ← acceptKeyword "on" then
    expectKeyword "conflict"
    expectConflict constraint.conflict
  else unless constraint.conflict == .abort do mismatch "the default table-key conflict action"

/-- Table CONSTRAINT names are standalone grammar productions, optionally
separated by commas. They can precede, follow or stand without an actual key.
Every actual key must still match exactly one retained AST constraint. -/
private def matchTableConstraints (constraints : Array TableConstraintDef) : MatchM Unit := do
  let mut position := 0
  let mut more ← acceptSymbol ","
  while more do
    if ← acceptKeyword "constraint" then matchConstraintName
    else
      let some constraint := constraints[position]? | mismatch "a retained table constraint"
      matchTablePrimary constraint
      position := position + 1
    if ← acceptSymbol "," then more := true
    else more := isKeyword (← peek) "constraint" || isKeyword (← peek) "primary"
  unless position == constraints.size do mismatch "all retained table constraints"

private def skipSpaceTokens (tokens : List Token) : List Token :=
  tokens.dropWhile fun token => match token with | .space _ => true | _ => false

private def matchResultColumn (column : ResultColumn) : MatchM Unit := do
  let before := skipSpaceTokens (← get).remaining
  matchExpr column.expr
  let after := skipSpaceTokens (← get).remaining
  let source := (String.join ((before.take (before.length - after.length)).map Token.render)).trimAscii.toString
  unless column.sourceSql == some source do mismatch "the original result-expression source"
  matchAlias column.alias

private def matchResultColumns : List ResultColumn → MatchM Unit
  | [] => mismatch "at least one result column"
  | column :: columns => do
      matchResultColumn column
      for next in columns do
        expectSymbol ","
        matchResultColumn next

private def matchOrderTerm (term : OrderTerm) : MatchM Unit := do
  matchExpr term.expr
  if term.descending then expectKeyword "desc"
  else discard <| acceptKeyword "asc"
  if let some first := term.nullsFirst then
    expectKeyword "nulls"
    expectKeyword (if first then "first" else "last")

private def matchOrderTerms : List OrderTerm → MatchM Unit
  | [] => pure ()
  | term :: terms => do
      matchOrderTerm term
      for next in terms do
        expectSymbol ","
        matchOrderTerm next

private def matchTableFactor (source : TableRef) : MatchM Unit := do
  unless source.subquerySql.isNone && source.columnAliases.isEmpty do
    mismatch "a named Core table source"
  expectObjectName source.name
  matchAlias source.alias

private def matchJoinSource (source : TableRef) : MatchM Unit := do
  unless !source.rightJoin && !source.naturalJoin && source.usingColumns.isEmpty do
    mismatch "an INNER or LEFT JOIN ... ON source"
  if source.leftJoin then
    expectKeyword "left"
    discard <| acceptKeyword "outer"
    expectKeyword "join"
  else
    discard <| acceptKeyword "inner"
    expectKeyword "join"
  matchTableFactor source
  match source.joinOn with
  | none => mismatch "JOIN ... ON"
  | some condition => expectKeyword "on" *> matchExpr condition

private def matchSources : List TableRef → MatchM Unit
  | [] => pure ()
  | source :: sources => do
      matchTableFactor source
      for next in sources do matchJoinSource next

private def matchRows : List (Array Expr) → MatchM Unit
  | [] => mismatch "at least one VALUES row"
  | row :: rows => do
      expectSymbol "("
      matchExprList row.toList
      expectSymbol ")"
      for next in rows do
        expectSymbol ","
        expectSymbol "("
        matchExprList next.toList
        expectSymbol ")"


/-- Replay the first VALUES row twice: once as result metadata and once as
its actual value row. Neither AST copy may hide a different expression. -/
private def matchValuesBase (query : Select) (rows : Array (Array Expr)) : MatchM Unit := do
  unless query.sources.isEmpty && query.where_.isNone && query.groupBy.isEmpty &&
      query.having.isNone && !query.distinct && rows.all (fun row => !row.isEmpty) do
    mismatch "a nonempty VALUES row list without SELECT clauses"
  let some first := rows[0]? | mismatch "at least one VALUES row"
  unless first.size == query.columns.size do mismatch "VALUES result column count"
  for i in [:first.size] do
    let some value := first[i]? | mismatch "VALUES first row"
    let some column := query.columns[i]? | mismatch "VALUES result column"
    unless column.alias == some s!"column{i + 1}" && column.sourceSql == some value.sql do
      mismatch "VALUES result-column metadata"
  expectKeyword "values"
  let start ← get
  matchRows [query.columns.map (·.expr)]
  let afterColumns ← get
  set start
  matchRows [first]
  unless (← get).remaining == afterColumns.remaining do mismatch "the same first VALUES row"
  for row in rows.toList.drop 1 do
    expectSymbol ","
    matchRows [row]

private def matchSelectBase (query : Select) : MatchM Unit := do
  if let some rows := query.valueRows then return ← matchValuesBase query rows
  expectKeyword "select"
  if query.distinct then expectKeyword "distinct"
  else discard <| acceptKeyword "all"
  matchResultColumns query.columns.toList
  unless query.sources.isEmpty do
    expectKeyword "from"
    matchSources query.sources.toList
  match query.where_ with
  | some predicate => expectKeyword "where" *> matchExpr predicate
  | none => pure ()
  unless query.groupBy.isEmpty do
    expectKeyword "group"
    expectKeyword "by"
    matchExprList query.groupBy.toList
  match query.having with
  | some predicate => expectKeyword "having" *> matchExpr predicate
  | none => pure ()

private def matchCompoundOp : CompoundOp → MatchM Unit
  | .unionAll => expectKeyword "union" *> expectKeyword "all"
  | .unionDistinct => do
      expectKeyword "union"
      discard <| acceptKeyword "distinct"
  | .except => expectKeyword "except"
  | .intersect => expectKeyword "intersect"

private def matchSelectArm (query : Select) : MatchM Unit := do
  unless query.compounds.isEmpty && query.orderBy.isEmpty &&
      query.limit.isNone && query.offset == 0 && query.limitClause.isNone do
    mismatch "a compound SELECT arm without a local tail clause"
  matchSelectBase query

private def matchSelect (query : Select) (deferLimitErrors : Bool := false) : MatchM Unit := do
  matchSelectBase query
  for arm in query.compounds do
    matchCompoundOp arm.1
    matchSelectArm arm.2
  let lastValues := (query.compounds.toList.getLast?).map
    (fun arm => arm.2.valueRows.isSome) |>.getD query.valueRows.isSome
  if lastValues && (isKeyword (← peek) "order" || isKeyword (← peek) "limit") then
    mismatch "a final SELECT arm before ORDER BY or LIMIT"
  unless query.orderBy.isEmpty do
    expectKeyword "order"
    expectKeyword "by"
    matchOrderTerms query.orderBy.toList
  matchLimit query deferLimitErrors


/-- Replay a tuple's target names against consecutive flattened AST pairs,
returning exactly their associated expressions and the untouched remainder. -/
private def matchAssignmentNames : List (String × Expr) → MatchM (List Expr × List (String × Expr))
  | [] => mismatch "an assignment target"
  | (name, expression) :: rest => do
      expectName name
      if ← acceptSymbol ")" then return ([expression], rest)
      expectSymbol ","
      let (expressions, remaining) ← matchAssignmentNames rest
      return (expression :: expressions, remaining)

private def matchAssignmentValues : Nat → List Expr → MatchM Unit
  | 0, _ => mismatch "bounded assignment parentheses"
  | fuel + 1, expressions => fun state =>
      let direct : MatchM Unit := match expressions with
        | [] => mismatch "an assignment value"
        | [expression] => matchExpr expression
        | _ => do
            expectSymbol "("
            matchExprList expressions
            expectSymbol ")"
      let grouped : MatchM Unit := do
        expectSymbol "("
        matchAssignmentValues fuel expressions
        expectSymbol ")"
      match direct state with
      | .ok result => .ok result
      | .error _ => grouped state

private def matchAssignmentGroups : Nat → List (String × Expr) → MatchM Unit
  | 0, _ => mismatch "bounded assignment groups"
  | _ + 1, [] => pure ()
  | fuel + 1, (name, expression) :: rest => do
      let (expressions, remaining) ← do
        if ← acceptSymbol "(" then matchAssignmentNames ((name, expression) :: rest)
        else do expectName name; pure ([expression], rest)
      expectSymbol "="
      matchAssignmentValues ((← get).remaining.length + 1) expressions
      unless remaining.isEmpty do
        expectSymbol ","
        matchAssignmentGroups fuel remaining

private def matchAssignments (assignments : List (String × Expr)) : MatchM Unit := do
  unless !assignments.isEmpty && assignments.length ≤ SQLite.Limits.maxColumns do
    mismatch "between 1 and 2000 UPDATE targets"
  matchAssignmentGroups (assignments.length + 1) assignments

private def matchInsertPrefix (conflict : ConflictAction) : MatchM Unit := do
  if conflict == .replace && isKeyword (← peek) "replace" then
    expectKeyword "replace"
  else
    expectKeyword "insert"
    unless conflict == .default do
      expectKeyword "or"
      expectConflict conflict
  expectKeyword "into"

/-- Replay trans_opt independently; names in this production are ignored by
SQLite, but they must still be legal nm tokens. -/
private def matchTransactionSuffix : MatchM Unit := do
  if ← acceptKeyword "transaction" then
    if (SQLite.Identifier.nameToken (← peek)).isSome then discard advance

private def matchStatement : Statement → MatchM Unit
  | .alterDropColumn table name => do
      expectKeyword "alter"
      expectKeyword "table"
      expectObjectName table
      expectKeyword "drop"
      discard <| acceptKeyword "column"
      expectName name
  | .alterAddColumn table column => do
      expectKeyword "alter"
      expectKeyword "table"
      expectObjectName table
      expectKeyword "add"
      discard <| acceptKeyword "column"
      matchColumn column
  | .alterRenameTable table name => do
      expectKeyword "alter"
      expectKeyword "table"
      expectObjectName table
      expectKeyword "rename"
      expectKeyword "to"
      expectDeclaredName name
  | .alterRenameColumn table oldName newName => do
      expectKeyword "alter"
      expectKeyword "table"
      expectObjectName table
      expectKeyword "rename"
      discard <| acceptKeyword "column"
      expectName oldName
      expectKeyword "to"
      expectDeclaredName newName
  | .insertSelect table columns query conflict returning => do
      matchInsertPrefix conflict
      expectObjectName table
      if ← acceptKeyword "as" then
        unless (SQLite.Identifier.nameToken (← advance)).isSome do mismatch "an INSERT target alias"
      matchOptionalNameList columns
      matchSelect query
      unless returning.isEmpty do
        expectKeyword "returning"
        matchResultColumns returning.toList
  | .dropTable name ifExists => do
      expectKeyword "drop"
      expectKeyword "table"
      if ifExists then expectKeyword "if" *> expectKeyword "exists"
      expectName name
  | .dropIndex name ifExists => do
      expectKeyword "drop"
      expectKeyword "index"
      if ifExists then expectKeyword "if" *> expectKeyword "exists"
      expectName name
  | .createTableAs name query ifNotExists => do
      expectKeyword "create"
      expectKeyword "table"
      if ifNotExists then expectKeyword "if" *> expectKeyword "not" *> expectKeyword "exists"
      expectDeclaredName name
      expectKeyword "as"
      -- CTAS rechecks LIMIT evaluation after its possible schema no-op.
      -- All original expression tokens are still replayed here.
      matchSelect query true
  | .createTable name columns constraints ifNotExists => do
      expectKeyword "create"
      expectKeyword "table"
      if ifNotExists then
        expectKeyword "if" *> expectKeyword "not" *> expectKeyword "exists"
      expectDeclaredName name
      expectSymbol "("
      matchColumns columns.toList
      matchTableConstraints constraints
      expectSymbol ")"
  | .createIndex name table expressions unique where_ ifNotExists => do
      expectKeyword "create"
      if unique then expectKeyword "unique"
      expectKeyword "index"
      if ifNotExists then
        expectKeyword "if" *> expectKeyword "not" *> expectKeyword "exists"
      expectDeclaredName name
      expectKeyword "on"
      expectObjectName table
      expectSymbol "("
      matchAscendingIndexExprs expressions.toList
      expectSymbol ")"
      match where_ with
      | some predicate => expectKeyword "where" *> matchExpr predicate
      | none => pure ()
  | .insert table columns rows conflict returning => do
      matchInsertPrefix conflict
      expectObjectName table
      if ← acceptKeyword "as" then
        unless (SQLite.Identifier.nameToken (← advance)).isSome do mismatch "an INSERT target alias"
      matchOptionalNameList columns
      if ← acceptKeyword "default" then
        expectKeyword "values"
        unless rows.size == 1 && rows[0]!.isEmpty do mismatch "DEFAULT VALUES"
      else
        expectKeyword "values"
        unless rows.all (fun row => !row.isEmpty) do mismatch "a nonempty VALUES row"
        matchRows rows.toList
      unless returning.isEmpty do
        expectKeyword "returning"
        matchResultColumns returning.toList
  | .delete table alias where_ returning => do
      expectKeyword "delete"
      expectKeyword "from"
      expectObjectName table
      matchAlias alias
      match where_ with
      | some predicate => expectKeyword "where" *> matchExpr predicate
      | none => pure ()
      unless returning.isEmpty do
        expectKeyword "returning"
        matchResultColumns returning.toList
  | .update table alias assignments where_ conflict returning => do
      expectKeyword "update"
      unless conflict == .default do
        expectKeyword "or"
        expectConflict conflict
      expectObjectName table
      matchAlias alias
      expectKeyword "set"
      matchAssignments assignments.toList
      match where_ with
      | some predicate => expectKeyword "where" *> matchExpr predicate
      | none => pure ()
      unless returning.isEmpty do
        expectKeyword "returning"
        matchResultColumns returning.toList
  | .pragma name argument schema => do
      expectKeyword "pragma"
      if let some schema := schema then
        matchPragmaName schema
        expectSymbol "."
      matchPragmaName name
      match argument with
      | none => pure ()
      | some expression =>
          if ← acceptSymbol "=" then matchPragmaArgument expression
          else
            expectSymbol "("
            matchPragmaArgument expression
            expectSymbol ")"
  | .select query => matchSelect query
  | .begin => do
      expectKeyword "begin"
      discard <| acceptKeyword "deferred"
      matchTransactionSuffix
  | .commit => do
      if isKeyword (← peek) "end" then expectKeyword "end"
      else expectKeyword "commit"
      matchTransactionSuffix
  | .savepoint name => do
      expectKeyword "savepoint"
      matchPragmaName name
  | .release name => do
      expectKeyword "release"
      discard <| acceptKeyword "savepoint"
      matchPragmaName name
  | .rollbackTo name => do
      expectKeyword "rollback"
      matchTransactionSuffix
      expectKeyword "to"
      discard <| acceptKeyword "savepoint"
      matchPragmaName name
  | .rollback => do
      expectKeyword "rollback"
      matchTransactionSuffix
  | _ => mismatch "a statement in the verified Core grammar"

private def skipSemicolons : MatchM Unit := do
  while ← acceptSymbol ";" do pure ()

private def matchStatements : List Statement → MatchM Unit
  | [] => skipSemicolons
  | statement :: statements => do
      matchStatement statement
      match statements with
      | [] => skipSemicolons
      | _ :: _ =>
          expectSymbol ";"
          skipSemicolons
          matchStatements statements

/-- The inspectable token-to-AST grammar.  Unlike `Parser.parseTokens`, this
checker is AST-directed and shares no parsing routines or parser state. -/
def check (tokens : Array Token) (statements : Array Statement) : Except String Unit := do
  let initial : MatchState := { remaining := tokens.toList }
  let (_, finalState) ← (matchStatements statements.toList).run initial
  match significant finalState.remaining with
  | [] | [.eof] => pure ()
  | token :: _ =>
      throw s!"verified grammar expected end of input, found {token.render}"

def Matches (tokens : Array Token) (statements : Array Statement) : Prop :=
  check tokens statements = .ok ()

/-- Proof-carrying result admitted by the live verified Core front end. -/
structure CertifiedParse (sql : String) where
  tokens : Array Token
  statements : Array Statement
  lexes : lex sql = .ok tokens
  parses : parseTokens tokens = .ok statements
  tokenizes : Tokenizes sql.toList tokens.toList
  grammar : Matches tokens statements

/-- One lexical pass, one total compatibility parse, and one independent
grammar replay.  Proofs erase; the replay is the runtime admission check. -/
def parseCertified (sql : String) : Except String (CertifiedParse sql) := do
  match lexed : lex sql with
  | .error message => .error message
  | .ok tokens =>
      match parsed : parseTokens tokens with
      | .error message => .error message
      | .ok statements =>
          match checked : check tokens statements with
          | .error message => .error message
          | .ok () => .ok {
              tokens
              statements
              lexes := lexed
              parses := parsed
              tokenizes := lex_sound lexed
              grammar := checked }

theorem parseCertified_sound {sql : String} {result : CertifiedParse sql}
    (_success : parseCertified sql = .ok result) :
    lex sql = .ok result.tokens ∧
      parseTokens result.tokens = .ok result.statements ∧
      Tokenizes sql.toList result.tokens.toList ∧
      Matches result.tokens result.statements :=
  ⟨result.lexes, result.parses, result.tokenizes, result.grammar⟩

/-- The certified front end agrees with the broad parser on the admitted AST;
the additional `grammar` field is the independent evidence that the broad
parser alone did not provide. -/
theorem parseCertified_agrees_parse {sql : String}
    {result : CertifiedParse sql}
    (_success : parseCertified sql = .ok result) :
    parse sql = .ok result.statements := by
  simp [parse, result.lexes, result.parses, bind, Except.bind]

/-- A convenient proposition fixing the certified AST while hiding the
dependent certificate value.  Text-level semantic theorems use this relation
instead of the old, unchecked `parse text = .ok statements` premise. -/
def Parses (sql : String) (statements : Array Statement) : Prop :=
  ∃ certificate : CertifiedParse sql,
    parseCertified sql = .ok certificate ∧ certificate.statements = statements

theorem Parses.grammar {sql : String} {statements : Array Statement}
    (parsed : Parses sql statements) :
    ∃ tokens : Array Token,
      Tokenizes sql.toList tokens.toList ∧ Matches tokens statements := by
  rcases parsed with ⟨certificate, _, rfl⟩
  exact ⟨certificate.tokens, certificate.tokenizes, certificate.grammar⟩

theorem Parses.agrees_parse {sql : String} {statements : Array Statement}
    (parsed : Parses sql statements) : parse sql = .ok statements := by
  rcases parsed with ⟨certificate, success, rfl⟩
  exact parseCertified_agrees_parse success

/-- Production callers that only need the AST still pass through certificate
construction. This closes the gap between CoreSQL.execute and the file/CLI
fast paths, which previously called the broad parser directly. -/
def parseStatements (sql : String) : Except String (Array Statement) :=
  (·.statements) <$> parseCertified sql

theorem parseStatements_certified {sql : String} {statements : Array Statement}
    (success : parseStatements sql = .ok statements) : Parses sql statements := by
  unfold parseStatements at success
  cases parsed : parseCertified sql with
  | error message => simp [parsed, Functor.map, Except.map] at success
  | ok certificate =>
      simp [parsed, Functor.map, Except.map] at success
      exact ⟨certificate, parsed, success⟩

end CoreTokenGrammar
end SQLeanite
