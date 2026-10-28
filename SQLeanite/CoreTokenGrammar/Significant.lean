import SQLeanite.SQLite.CastType
import SQLeanite.Syntax.TableConstraintDef

namespace SQLeanite
namespace CoreTokenGrammar

def significant : List Token → List Token
  | [] => []
  | .space _ :: tokens => significant tokens
  | token :: tokens => token :: significant tokens

/-- Identifier roles recorded by the independent replay for schema-source
renames. A tail length identifies the actual significant token, not spelling
matches in literals, aliases, comments or function names. -/
inductive ReferenceKind where
  | column (qualifier : Option String) (name : String)
  | qualifier (name : String)
  | table (source : TableRef)
  | captured (sql : String) (correlated : Bool := true)

structure Reference where
  kind : ReferenceKind
  query : Option Select
  tailLength : Nat
  outputAliases : Bool := false

structure MatchState where
  remaining : List Token
  tracing : Bool := false
  query : Option Select := none
  references : List Reference := []
  outputAliases : Bool := false

abbrev MatchM := StateT MatchState (Except String)

def mismatch (expected : String) : MatchM α := do
  let state ← get
  let found := (significant state.remaining).head?.map Token.render
    |>.getD "end of input"
  throw s!"verified grammar expected {expected}, found {found}"

def nextSignificant : List Token → Token × List Token
  | [] => (.eof, [])
  | .space _ :: tokens => nextSignificant tokens
  | token :: tokens => (token, tokens)

def peek : MatchM Token := do
  return (nextSignificant (← get).remaining).1

def advance : MatchM Token := do
  let state ← get
  let (token, tokens) := nextSignificant state.remaining
  set { state with remaining := tokens }
  return token

def traceReference (kind : ReferenceKind) : MatchM Unit := do
  let state ← get
  if state.tracing then
    set { state with references := {
      kind, query := state.query, tailLength := (nextSignificant state.remaining).2.length,
      outputAliases := state.outputAliases } :: state.references }

def tokenName? : Token → Option String
  | .ident name | .quotedIdent name _ | .string name => some name
  | _ => none

def isKeyword (token : Token) (word : String) : Bool :=
  match token with
  | .ident name => name.toLower == word
  | _ => false

def isSymbol (token : Token) (symbol : String) : Bool :=
  match token with
  | .symbol found => found == symbol
  | _ => false

def acceptKeyword (word : String) : MatchM Bool := do
  if isKeyword (← peek) word then
    discard <| advance
    return true
  return false

def expectKeyword (word : String) : MatchM Unit := do
  unless ← acceptKeyword word do mismatch word.toUpper

def acceptSymbol (symbol : String) : MatchM Bool := do
  if isSymbol (← peek) symbol then
    discard <| advance
    return true
  return false

def expectSymbol (symbol : String) : MatchM Unit := do
  unless ← acceptSymbol symbol do mismatch symbol

def expectName (expected : String) : MatchM Unit := do
  match SQLite.Identifier.nameToken (← advance) with
  | some found =>
      unless found.toLower == expected.toLower do mismatch s!"name {expected}"
  | none => mismatch s!"name {expected}"

def expectPrimaryName (qualified : Bool) (expected : String) : MatchM Unit := do
  let some found := SQLite.Identifier.primaryToken qualified (← advance) | mismatch "an expression identifier"
  unless found.toLower == expected.toLower do mismatch "the parsed expression identifier"

/-- A newly declared name is stored verbatim, so case is semantic metadata
here even though references to an existing name compare case-insensitively. -/
def expectDeclaredName (expected : String) : MatchM Unit := do
  match SQLite.Identifier.nameToken (← advance) with
  | some found => unless found == expected do mismatch s!"declared name {expected}"
  | none => mismatch s!"declared name {expected}"

/-- CREATE INDEX admits the main schema qualifier as two lexical names.
A quoted period remains part of one identifier and is never split. -/
def expectIndexName (expected : String) : MatchM Unit := do
  let some first := SQLite.Identifier.nameToken (← advance) | mismatch "an index name"
  if ← acceptSymbol "." then
    unless first.toLower == "main" do mismatch "the main index schema"
    expectDeclaredName expected
  else unless first == expected do mismatch s!"declared name {expected}"

/-- CREATE's main qualifier is lexical namespace syntax. A quoted period
belongs to one declared identifier and cannot become that qualifier. -/
def expectMainDeclaredName (expected : String) : MatchM Unit := do
  let token ← advance
  let some first := SQLite.Identifier.nameToken token | mismatch "a declared table name"
  if ← acceptSymbol "." then
    unless first.toLower == "main" do
      if first.toLower == "temp" then mismatch "the main table schema"
      else throw s!"unknown database {token.render}"
    expectDeclaredName expected
  else unless first == expected do mismatch s!"declared name {expected}"

/-- The current AST does not distinguish a schema qualifier from a period in
one quoted identifier. Admit one object-name token until that metadata is
represented explicitly; never reinterpret a quoted period as a qualifier. -/
def expectObjectName (expected : String) : MatchM Unit :=
  expectName expected

/-- ALTER's target is the object name in the sole persistent schema. A
literal quoted period remains part of that name; only two lexical identifiers
separated by a dot can supply the explicit main qualifier. -/
def expectMainObjectName (expected : String) : MatchM Unit := do
  let some first := SQLite.Identifier.nameToken (← advance) | mismatch "an ALTER table name"
  if ← acceptSymbol "." then
    unless first.toLower == "main" do mismatch "the main ALTER schema"
    expectName expected
  else unless first.toLower == expected.toLower do mismatch s!"ALTER target {expected}"

/-- IN table shorthand names exactly one table, with an optional schema.
The bounded shape prevents captured SQL from consuming an outer WHERE or alias. -/
def inTableNames? (tokens : List Token) : Option (Option String × String) := do
  match tokens with
  | select :: .symbol "*" :: fromToken :: first :: second :: rest =>
      if !isKeyword select "select" || !isKeyword fromToken "from" then none else
        match second with
        | .eof => if rest.isEmpty then some (none, ← SQLite.Identifier.nameToken first) else none
        | .symbol "." =>
            match rest with
            | [name, .eof] => some (some (← SQLite.Identifier.nameToken first), ← SQLite.Identifier.nameToken name)
            | _ => none
        | _ => none
  | _ => none

theorem inTableNames?_where (name : Token) (condition : List Token) :
    inTableNames? ([.ident "SELECT", .symbol "*", .ident "FROM", name,
      .ident "WHERE"] ++ condition) = none := by
  simp [inTableNames?]

def matchInTable (tokens : List Token) : MatchM Unit := do
  let some (schema, name) := inTableNames? tokens | mismatch "one captured IN table name"
  if let some schema := schema then
    expectName schema
    expectSymbol "."
  traceReference (.table { name := schema.map (fun schema => schema ++ "." ++ name) |>.getD name, schema })
  expectName name

def expectSemanticToken (expected : Token) : MatchM Unit := do
  let found ← advance
  let namesMatch := match tokenName? expected, tokenName? found with
    | some left, some right => left.toLower == right.toLower
    | _, _ => false
  unless namesMatch || found == expected do
    mismatch expected.render

def matchCastType (expected : String) : MatchM Unit := do
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

def sourceTokens (source : String) : Except String (List Token) := do
  let tokens ← lex source
  return (significant tokens.toList).filter (· != .eof)

def expectSource (source : String) : MatchM Unit := do
  for token in ← sourceTokens source do expectSemanticToken token

def expectConflict : ConflictAction → MatchM Unit
  | .rollback => expectKeyword "rollback"
  | .abort => expectKeyword "abort"
  | .fail => expectKeyword "fail"
  | .replace => expectKeyword "replace"
  | .ignore => expectKeyword "ignore"
  | .default => mismatch "an explicit conflict action"

def matchConflictAction : MatchM ConflictAction := do
  let token ← peek
  let result ← if isKeyword token "abort" then pure ConflictAction.abort
    else if isKeyword token "ignore" then pure .ignore
    else if isKeyword token "replace" then pure .replace
    else if isKeyword token "fail" then pure .fail
    else if isKeyword token "rollback" then pure .rollback
    else mismatch "an explicit conflict action"
  discard advance
  return result

def expectInteger (expected : Int) : MatchM Unit := do
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

def expectNat (expected : Nat) : MatchM Unit :=
  expectInteger (Int.ofNat expected)

def expectBinaryOp : BinaryOp → MatchM Unit
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

def expectLiteral : Value → MatchM Unit
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
def expectLiteralSpelling (value : Value) (spelling : Option String) : MatchM Unit := do
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

end CoreTokenGrammar

end SQLeanite
