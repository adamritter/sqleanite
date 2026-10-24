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
  match tokenName? (← advance) with
  | some found =>
      unless found.toLower == expected.toLower do mismatch s!"name {expected}"
  | none => mismatch s!"name {expected}"

private def expectQualifiedName (expected : String) : MatchM Unit := do
  match expected.splitOn "." with
  | [] => mismatch s!"name {expected}"
  | first :: rest =>
      expectName first
      for component in rest do
        expectSymbol "."
        expectName component

private def expectSemanticToken (expected : Token) : MatchM Unit := do
  let found ← advance
  let namesMatch := match tokenName? expected, tokenName? found with
    | some left, some right => left.toLower == right.toLower
    | _, _ => false
  unless namesMatch || found == expected do
    mismatch expected.render

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

private def expectInteger (expected : Int) : MatchM Unit := do
  if expected < 0 then
    expectSymbol "-"
    match ← advance with
    | .integer found =>
        unless found == -expected do mismatch s!"integer {expected}"
    | _ => mismatch s!"integer {expected}"
  else
    match ← advance with
    | .integer found =>
        unless found == expected do mismatch s!"integer {expected}"
    | .ident found =>
        unless (found.toLower == "true" && expected == 1) ||
            (found.toLower == "false" && expected == 0) do mismatch s!"integer {expected}"
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
  | .is => expectKeyword "is"
  | .isNot => expectKeyword "is" *> expectKeyword "not"
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
          match parseDecimal? source with
          | some found => unless found == value do mismatch "the parsed REAL literal"
          | none => mismatch "a REAL literal"
      | .integer source =>
          unless Float.ofInt source == value do mismatch "the parsed REAL literal"
      | _ => mismatch "a REAL literal"
  | .text value => do
      match ← advance with
      | .string found => unless found == value do mismatch "the parsed text literal"
      | _ => mismatch "a text literal"
  | .blob value => expectSource (toString (Value.blob value))

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
          | .error _ => matchExprCore fuel expression state
        else matchExprCore fuel expression state

  private def matchExprCore : Nat → Expr → MatchM Unit
    | _, .literal value => expectLiteral value
    | _, .column none name => expectName name
    | _, .column (some qualifier) name =>
        expectQualifiedName qualifier *> expectSymbol "." *> expectName name
    | _, .star none => expectSymbol "*"
    | _, .star (some qualifier) =>
        expectQualifiedName qualifier *> expectSymbol "." *> expectSymbol "*"
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
        if name == "lean_dqs" then
          match arguments.toList, star with
          | [.literal (.text expected)], false =>
              match ← advance with
              | .quotedIdent found _ =>
                  unless found.toLower == expected.toLower do
                    mismatch s!"quoted identifier {expected}"
              | _ => mismatch s!"quoted identifier {expected}"
          | _, _ => mismatch "a supported quoted identifier"
        else if name.startsWith "cast_" then
          match arguments.toList, star with
          | [argument], false =>
              expectKeyword "cast"
              expectSymbol "("
              matchExprFuel fuel argument
              expectKeyword "as"
              expectName (name.drop 5).toString
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
        expectKeyword "is"
        if negated then expectKeyword "not"
        expectKeyword "null"
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

private def matchExprList : List Expr → MatchM Unit
  | [] => pure ()
  | expression :: expressions => do
      matchExpr expression
      for next in expressions do
        expectSymbol ","
        matchExpr next

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
      discard <| acceptKeyword "as"
      expectName alias

private def matchColumnConstraints (column : ColumnDef) : MatchM Unit := do
  unless column.defaultValue.isNone && column.generated.isNone &&
      !column.unique && column.references.isNone && column.check.isNone &&
      !column.autoIncrement do
    mismatch "a verified-Core column definition"
  let mut sawNotNull := false
  let mut sawPrimary := false
  let mut sawCollation := false
  let mut scanning := true
  while scanning do
    if isKeyword (← peek) "not" then
      expectKeyword "not"
      expectKeyword "null"
      sawNotNull := true
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        expectConflict column.notNullConflict
    else if isKeyword (← peek) "null" then
      expectKeyword "null"
    else if isKeyword (← peek) "primary" then
      expectKeyword "primary"
      expectKeyword "key"
      sawPrimary := true
      if ← acceptKeyword "on" then
        expectKeyword "conflict"
        expectConflict column.conflict
    else if isKeyword (← peek) "collate" then
      expectKeyword "collate"
      expectName column.collation
      sawCollation := true
    else
      scanning := false
  unless sawNotNull == column.notNull && sawPrimary == column.primaryKey &&
      sawCollation == (column.collation.toLower != "binary") do
    mismatch s!"the parsed constraints for column {column.name}"

private def matchColumn (column : ColumnDef) : MatchM Unit := do
  expectName column.name
  unless column.declaredType.isEmpty do expectSource column.declaredType
  matchColumnConstraints column

private def matchColumns : List ColumnDef → MatchM Unit
  | [] => pure ()
  | column :: columns => do
      matchColumn column
      for next in columns do
        expectSymbol ","
        matchColumn next

private def matchResultColumn (column : ResultColumn) : MatchM Unit := do
  matchExpr column.expr
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
  expectQualifiedName source.name
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

private def matchSelectBase (query : Select) : MatchM Unit := do
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
      query.limit.isNone && query.offset == 0 do
    mismatch "a compound SELECT arm without a local tail clause"
  matchSelectBase query

private def matchSelect (query : Select) : MatchM Unit := do
  unless query.valueRows.isNone do mismatch "SELECT rather than top-level VALUES"
  matchSelectBase query
  for arm in query.compounds do
    matchCompoundOp arm.1
    matchSelectArm arm.2
  unless query.orderBy.isEmpty do
    expectKeyword "order"
    expectKeyword "by"
    matchOrderTerms query.orderBy.toList
  match query.limit with
  | none =>
      unless query.offset == 0 do mismatch "LIMIT before OFFSET"
  | some limit =>
      expectKeyword "limit"
      expectNat limit
      unless query.offset == 0 do
        expectKeyword "offset"
        expectNat query.offset

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

private def matchAssignments : List (String × Expr) → MatchM Unit
  | [] => mismatch "at least one assignment"
  | assignment :: assignments => do
      expectName assignment.1
      expectSymbol "="
      matchExpr assignment.2
      for next in assignments do
        expectSymbol ","
        expectName next.1
        expectSymbol "="
        matchExpr next.2

private def matchInsertPrefix (conflict : ConflictAction) : MatchM Unit := do
  if conflict == .replace && isKeyword (← peek) "replace" then
    expectKeyword "replace"
  else
    expectKeyword "insert"
    unless conflict == .default do
      expectKeyword "or"
      expectConflict conflict
  expectKeyword "into"

private def matchStatement : Statement → MatchM Unit
  | .createTable name columns constraints ifNotExists => do
      unless constraints.isEmpty do mismatch "column-level Core constraints"
      expectKeyword "create"
      expectKeyword "table"
      if ifNotExists then
        expectKeyword "if" *> expectKeyword "not" *> expectKeyword "exists"
      expectQualifiedName name
      expectSymbol "("
      matchColumns columns.toList
      expectSymbol ")"
  | .createIndex name table expressions unique where_ ifNotExists => do
      expectKeyword "create"
      if unique then expectKeyword "unique"
      expectKeyword "index"
      if ifNotExists then
        expectKeyword "if" *> expectKeyword "not" *> expectKeyword "exists"
      expectQualifiedName name
      expectKeyword "on"
      expectQualifiedName table
      expectSymbol "("
      matchExprList expressions.toList
      expectSymbol ")"
      match where_ with
      | some predicate => expectKeyword "where" *> matchExpr predicate
      | none => pure ()
  | .insert table columns rows conflict => do
      matchInsertPrefix conflict
      expectQualifiedName table
      matchOptionalNameList columns
      expectKeyword "values"
      matchRows rows.toList
  | .delete table alias where_ returning => do
      expectKeyword "delete"
      expectKeyword "from"
      expectQualifiedName table
      matchAlias alias
      match where_ with
      | some predicate => expectKeyword "where" *> matchExpr predicate
      | none => pure ()
      unless returning.isEmpty do
        expectKeyword "returning"
        matchResultColumns returning.toList
  | .update table alias assignments where_ conflict => do
      expectKeyword "update"
      unless conflict == .default do
        expectKeyword "or"
        expectConflict conflict
      expectQualifiedName table
      matchAlias alias
      expectKeyword "set"
      matchAssignments assignments.toList
      match where_ with
      | some predicate => expectKeyword "where" *> matchExpr predicate
      | none => pure ()
  | .select query => matchSelect query
  | .begin => do
      expectKeyword "begin"
      discard <| acceptKeyword "transaction"
  | .commit => do
      if isKeyword (← peek) "end" then expectKeyword "end"
      else expectKeyword "commit"
      discard <| acceptKeyword "transaction"
  | .rollback => do
      expectKeyword "rollback"
      discard <| acceptKeyword "transaction"
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

end CoreTokenGrammar
end SQLeanite
