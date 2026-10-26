import SQLeanite.Lexer

namespace SQLeanite.SQLite.CreateCatalog

structure Span where
  token : Token
  start : Nat
  finish : Nat

/-- Source offsets refer to the original character list. Comments and spaces
advance the offset but never become identifier or end-token candidates. -/
def spans : Nat → Nat → List Char → List Span → Except String (List Span)
  | 0, _, _, _ => .error "catalog tokenization progress limit exceeded"
  | fuel+1, offset, input, accumulated => do
      match ← lexicalStep input with
      | none => return accumulated.reverse
      | some step =>
          let finish := offset + (input.length - step.rest.length)
          let next := step.emitted.foldl (fun previous token => match token with
            | .space _ | .eof => previous
            | _ => { token, start := offset, finish } :: previous) accumulated
          spans fuel finish step.rest next

def keyword (word : String) (span : Span) : Bool :=
  match span.token with
  | .ident name => name.toUpper == word
  | _ => false

def afterKeyword (word : String) : List Span → Option (List Span)
  | span :: rest => if keyword word span then some rest else none
  | [] => none

/-- Locate the lexical table-name token, retaining its original quote style. -/
def nameSpan (tokens : List Span) : Option Span := do
  let rest ← afterKeyword "CREATE" tokens
  let rest := match rest with
    | first :: tail => if keyword "TEMP" first || keyword "TEMPORARY" first then tail else rest
    | [] => []
  let rest ← afterKeyword "TABLE" rest
  let rest ← match afterKeyword "IF" rest with
    | none => some rest
    | some rest => afterKeyword "NOT" rest >>= afterKeyword "EXISTS"
  match rest with
    | _ :: dot :: name :: _ => if dot.token == .symbol "." then some name else rest.head?
    | _ => rest.head?

/-- Duplicate-name errors use the original name token, including its quotes. -/
def nameToken (sql : String) : Option String := do
  let chars := sql.toList
  let tokens ← (spans (chars.length+1) 0 chars []).toOption
  let name ← nameSpan tokens
  return String.ofList (chars.drop name.start |>.take (name.finish-name.start))

/-- Normalize an already admitted ordinary CREATE TABLE. Component support for
TEMP/STRICT/WITHOUT ROWID does not admit those forms into Core execution.
SQLite build.c keeps the name through ')' for ordinary tables, and through
pre-terminator trivia when table options follow the closing parenthesis. -/
def table (sql : String) : Option String := do
  let chars := sql.toList
  let tokens ← (spans (chars.length+1) 0 chars []).toOption
  let terminator := tokens.find? (fun span => span.token == .symbol ";")
  let tokens := tokens.takeWhile (fun span => span.token != .symbol ";")
  let name ← nameSpan tokens
  let last ← tokens.getLast?
  let finish := if last.token == .symbol ")" then last.finish else
    (terminator.map (·.start)).getD chars.length
  return "CREATE TABLE " ++ String.ofList (chars.drop name.start |>.take (finish-name.start))

end SQLeanite.SQLite.CreateCatalog
