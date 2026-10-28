import SQLeanite.Parser.ParseSelectAfterSelectFuel

namespace SQLeanite

def parseTrigger (temporary : Bool := false) (statementStart : Option Nat := none) : ParserM Statement := do
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
      -- An unknown body token is a syntax error. At EOF this also prevents
      -- repeatedly advancing past the token array while waiting for END.
      throw (syntaxError (← peek))
    discard <| acceptSymbol ";"
  expectKeyword "end"
  let stop ← currentTokenPos
  let sourceSql ← match statementStart with
    | some start => tokenSource start stop
    | none => pure ""
  pure (.createTrigger name table event timing when_ body ifNotExists temporary displayName sourceSql)

/-- SQLite's optional TRANSACTION name is syntactic compatibility metadata;
it does not name the transaction or participate in matching COMMIT/ROLLBACK. -/
def parseTransactionSuffix : ParserM Unit := do
  if ← acceptKeyword "transaction" then
    if (SQLite.Identifier.nameToken (← peek)).isSome then discard advance

def parseStatement : ParserM Statement := do
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
    let (schema, table) ← parseQualifiedName
    if let some schema := schema then
      unless schema.toLower == "main" do throw s!"no such table: {schema}.{table}"
    if ← acceptKeyword "add" then
      discard <| acceptKeyword "column"
      pure (.alterAddColumn table (← parseColumnDef))
    else if ← acceptKeyword "drop" then
      discard <| acceptKeyword "column"
      pure (.alterDropColumn table (← expectIdent))
    else if ← acceptKeyword "rename" then
      if ← acceptKeyword "to" then
        pure (.alterRenameTable table (← expectIdent))
      else
        discard <| acceptKeyword "column"
        let oldName ← expectIdent
        expectKeyword "to"
        pure (.alterRenameColumn table oldName (← expectIdent))
    else throw (syntaxError (← peek))
  else if ← acceptKeyword "begin" then
    discard <| acceptKeyword "deferred"
    parseTransactionSuffix
    pure .begin
  else if ← acceptKeyword "commit" then parseTransactionSuffix; pure .commit
  else if ← acceptKeyword "end" then parseTransactionSuffix; pure .commit
  else if ← acceptKeyword "savepoint" then pure (.savepoint (← expectPragmaName))
  else if ← acceptKeyword "release" then
    discard <| acceptKeyword "savepoint"
    pure (.release (← expectPragmaName))
  else if ← acceptKeyword "rollback" then
    parseTransactionSuffix
    if ← acceptKeyword "to" then
      discard <| acceptKeyword "savepoint"
      pure (.rollbackTo (← expectPragmaName))
    else pure .rollback
  else if ← acceptKeyword "reindex" then pure .reindex
  else if ← acceptKeyword "analyze" then
    if (← peek) != .eof && !isSymbol (← peek) ";" then discard <| advance
    pure (.pragma "lean_analyze" none)
  else if ← acceptKeyword "vacuum" then
    if (← peek) != .eof && !isSymbol (← peek) ";" then discard <| advance
    pure (.pragma "lean_vacuum" none)
  else if ← acceptKeyword "pragma" then
    let first ← expectPragmaName
    let (name, schema) ← if ← acceptSymbol "." then
      let second ← expectPragmaName
      pure (second, some first)
      else pure (first, none)
    let equals ← acceptSymbol "="
    let paren ← if equals then pure false else acceptSymbol "("
    let arg ← if equals || paren then
      let expression ← parsePragmaArgument
      if paren then expectSymbol ")"
      pure (some expression)
      else pure none
    pure (.pragma name arg schema)
  else throw s!"unsupported statement beginning at {(← peek).render}"

def parseStatementsM : ParserM (Array Statement) := do
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

/-- Historical conformance interpreter only. Production parseTokens always
retains OVER syntax for independent token replay and CoreWindow execution. -/
def parseLegacy (sql : String) : Except String (Array Statement) := do
  let tokens ← lex sql
  return (← parseStatementsM.run { tokens, preserveWindowSyntax := false }).1

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

def parseOne : ParserM (Option Statement) := do
  while ← acceptSymbol ";" do pure ()
  if (← peek) == .eof then pure none
  else
    let statement ← parseStatement
    let semicolon ← acceptSymbol ";"
    unless semicolon || (← peek) == .eof do throw (syntaxError (← peek))
    pure (some statement)

/-- Parse complete statements up to the first syntax error, retaining the valid prefix. -/
def parseProgress (sql : String) (preserveWindowSyntax : Bool := true) : Except String (Array Statement × Option String) := do
  let tokens ← lex sql
  let rec loop (fuel : Nat) (state : ParserState) (statements : Array Statement) :=
    match fuel with
    | 0 => (statements, some "parser progress limit exceeded")
    | fuel + 1 =>
      match parseOne.run state with
      | .error message => (statements, some message)
      | .ok (none, _) => (statements, none)
      | .ok (some statement, next) => loop fuel next (statements.push statement)
  pure (loop (tokens.size + 1) { tokens, preserveWindowSyntax } #[])

def parseWindowBound : ParserM WindowBound := do
  if ← acceptKeyword "unbounded" then
    if ← acceptKeyword "preceding" then return .unboundedPreceding
    expectKeyword "following"
    return .unboundedFollowing
  if ← acceptKeyword "current" then
    expectKeyword "row"
    return .current
  let expression ← parseExpr
  if ← acceptKeyword "preceding" then return .preceding expression
  expectKeyword "following"
  return .following expression

def parseWindowSpecM : ParserM WindowSpec := do
  unless ← acceptSymbol "(" do
    let name ← expectIdent
    throw s!"no such window: {name}"
  let mut specification : WindowSpec := {}
  if ← acceptKeyword "partition" then
    expectKeyword "by"
    let mut terms := #[(← parseExpr)]
    while ← acceptSymbol "," do terms := terms.push (← parseExpr)
    specification := { specification with partition := terms }
  if ← acceptKeyword "order" then
    expectKeyword "by"
    let mut terms := #[]
    let mut more := true
    while more do
      let expr ← parseExpr
      let descending ← acceptKeyword "desc"
      unless descending do discard <| acceptKeyword "asc"
      let nullsFirst ← parseNullOrder
      terms := terms.push { expr, descending, nullsFirst }
      more ← acceptSymbol ","
    specification := { specification with ordering := terms }
  let token ← peek
  if ["rows", "range", "groups"].any (isKeyword token) then
    discard advance
    let kind := token.render.toLower
    let between ← acceptKeyword "between"
    let first ← parseWindowBound
    let last ← if between then expectKeyword "and" *> parseWindowBound else pure .current
    let boundOrder : WindowBound → Nat
      | .unboundedPreceding => 0 | .preceding _ => 1 | .current => 2
      | .following _ => 3 | .unboundedFollowing => 4
    if boundOrder first == 4 || boundOrder last == 0 then throw (syntaxError token)
    if boundOrder last < boundOrder first then throw "unsupported frame specification"
    specification := { specification with kind, first, last, explicitFrame := true }
  expectSymbol ")"
  unless (← peek) == .eof do throw (syntaxError (← peek))
  return specification

/-- Parse the complete captured OVER clause. Token replay independently ties
this exact clause to the statement before this semantic parser is used. -/
def parseWindowSpec (sql : String) : Except String WindowSpec := do
  let tokens ← lex sql
  return (← parseWindowSpecM.run { tokens }).1

end SQLeanite
