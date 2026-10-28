import SQLeanite.CoreTokenGrammar.MatchColumnConstraints
import SQLeanite.Parser.ParseTrigger

namespace SQLeanite
namespace CoreTokenGrammar

def matchInsertPrefix (conflict : ConflictAction) : MatchM Unit := do
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
def matchTransactionSuffix : MatchM Unit := do
  if ← acceptKeyword "transaction" then
    if (SQLite.Identifier.nameToken (← peek)).isSome then discard advance

def matchStatement (statement : Statement) (withPrefix : Bool := true) : MatchM Unit :=
  match statement with
  | .createView name columns query ifNotExists temporary _ => do
      expectKeyword "create"
      if temporary then
        unless (← acceptKeyword "temp") || (← acceptKeyword "temporary") do mismatch "TEMP or TEMPORARY"
      expectKeyword "view"
      if ifNotExists then expectKeyword "if" *> expectKeyword "not" *> expectKeyword "exists"
      expectDeclaredName name
      matchOptionalNameList columns
      expectKeyword "as"
      matchViewSelect query
  | .dropView name ifExists => do
      expectKeyword "drop"
      expectKeyword "view"
      if ifExists then expectKeyword "if" *> expectKeyword "exists"
      expectMainObjectName name
  | .upsert source alias clauses => do
      unless !clauses.isEmpty do mismatch "at least one ON CONFLICT clause"
      let (table, columns, conflict, returning) ← match source with
        | .insert table columns _ conflict returning | .insertSelect table columns _ conflict returning =>
            pure (table, columns, conflict, returning)
        | _ => mismatch "an INSERT source for UPSERT"
      matchInsertPrefix conflict
      expectObjectName table
      if let some alias := alias then expectKeyword "as" *> expectName alias
      matchOptionalNameList columns
      match source with
      | .insert _ _ rows _ _ =>
          expectKeyword "values"
          matchRows rows.toList
      | .insertSelect _ _ query _ _ => matchSelect query
      | _ => mismatch "an INSERT source"
      for clause in clauses do
        expectKeyword "on"
        expectKeyword "conflict"
        if let some target := clause.target then
          expectSymbol "("
          let mut first := true
          for expression in target do
            if !first then expectSymbol ","
            first := false
            matchExpr expression
            if !(← acceptKeyword "desc") then discard <| acceptKeyword "asc"
          expectSymbol ")"
        if let some expression := clause.targetWhere then expectKeyword "where" *> matchExpr expression
        expectKeyword "do"
        match clause.assignments with
        | none => expectKeyword "nothing"
        | some assignments =>
            expectKeyword "update"
            expectKeyword "set"
            matchAssignments assignments.toList
        if let some condition := clause.where_ then expectKeyword "where" *> matchExpr condition
      unless returning.isEmpty do expectKeyword "returning" *> matchResultColumns returning.toList
  | .withRecursive name columns seed step all body materialization => do
      if withPrefix then
        expectKeyword "with"
        discard <| acceptKeyword "recursive"
      expectName name
      unless columns.isEmpty do
        expectSymbol "("
        matchNameList columns.toList
        expectSymbol ")"
      expectKeyword "as"
      let actual : CteMaterialization ← if ← acceptKeyword "not" then
          expectKeyword "materialized" *> pure .notMaterialized
        else do
          if ← acceptKeyword "materialized" then pure .materialized else pure .default
      unless actual == materialization do mismatch "the CTE materialization hint"
      expectSymbol "("
      matchSelect seed
      expectKeyword "union"
      if all then expectKeyword "all"
      matchSelect step
      expectSymbol ")"
      match body with
      | .withCte .. | .withRecursive .. => expectSymbol "," *> matchStatement body false
      | _ => matchStatement body
  | .withCte name columns source body materialization => do
      if withPrefix then
        expectKeyword "with"
        discard <| acceptKeyword "recursive"
      expectName name
      unless columns.isEmpty do
        expectSymbol "("
        matchNameList columns.toList
        expectSymbol ")"
      expectKeyword "as"
      let actual : CteMaterialization ← if ← acceptKeyword "not" then
          expectKeyword "materialized" *> pure .notMaterialized
        else do
          if ← acceptKeyword "materialized" then pure .materialized else pure .default
      unless actual == materialization do mismatch "the CTE materialization hint"
      expectSymbol "("
      matchStatement source
      expectSymbol ")"
      match body with
      | .withCte .. | .withRecursive .. => expectSymbol "," *> matchStatement body false
      | _ => matchStatement body
  | .values rows => do
      expectKeyword "values"
      matchRows rows.toList
  | .alterDropColumn table name => do
      expectKeyword "alter"
      expectKeyword "table"
      expectMainObjectName table
      expectKeyword "drop"
      discard <| acceptKeyword "column"
      expectName name
  | .alterAddColumn table column => do
      expectKeyword "alter"
      expectKeyword "table"
      expectMainObjectName table
      expectKeyword "add"
      discard <| acceptKeyword "column"
      matchColumn column
  | .alterRenameTable table name => do
      expectKeyword "alter"
      expectKeyword "table"
      expectMainObjectName table
      expectKeyword "rename"
      expectKeyword "to"
      expectDeclaredName name
  | .alterRenameColumn table oldName newName => do
      expectKeyword "alter"
      expectKeyword "table"
      expectMainObjectName table
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
      expectMainDeclaredName name
      expectKeyword "as"
      -- CTAS rechecks LIMIT evaluation after its possible schema no-op.
      -- All original expression tokens are still replayed here.
      matchSelect query true
  | .createTable name columns constraints ifNotExists => do
      expectKeyword "create"
      expectKeyword "table"
      if ifNotExists then
        expectKeyword "if" *> expectKeyword "not" *> expectKeyword "exists"
      expectMainDeclaredName name
      expectSymbol "("
      matchColumns columns.toList
      matchTableConstraints constraints
      expectSymbol ")"
  | .createStrictTable name columns constraints ifNotExists => do
      expectKeyword "create"
      expectKeyword "table"
      if ifNotExists then
        expectKeyword "if" *> expectKeyword "not" *> expectKeyword "exists"
      expectMainDeclaredName name
      expectSymbol "("
      matchColumns columns.toList
      matchTableConstraints constraints
      expectSymbol ")"
      expectKeyword "strict"
  | .createIndex name table expressions unique where_ ifNotExists => do
      expectKeyword "create"
      if unique then expectKeyword "unique"
      expectKeyword "index"
      if ifNotExists then
        expectKeyword "if" *> expectKeyword "not" *> expectKeyword "exists"
      expectIndexName name
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

def skipSemicolons : MatchM Unit := do
  while ← acceptSymbol ";" do pure ()

def matchStatements : List Statement → MatchM Unit
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

/-- Trace exact identifier roles using the same independent concrete grammar.
Normal admission leaves tracing disabled. -/
def references (tokens : Array Token) (statements : Array Statement) : Except String (List Reference) := do
  let (_,finalState) ← (matchStatements statements.toList).run { remaining := tokens.toList, tracing := true }
  unless significant finalState.remaining == [] || significant finalState.remaining == [.eof] do
    throw "unexpected input after traced statement"
  return finalState.references.reverse

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
