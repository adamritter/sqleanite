import SQLeanite.SQLite.PragmaSyntax

/-! SQLite 3.53.4 parse.y typetoken/typename/signed and build.c type metadata.
The source span ends at its last token, before trailing comments. -/
namespace SQLeanite.SQLite.ColumnType

def significant (tokens : List Token) : List Token :=
  tokens.filter fun token => match token with | .space _ | .eof => false | _ => true

def word : Token → Bool
  | .ident name => PragmaSyntax.bareName name &&
      !["INDEXED", "LEFT", "RIGHT", "FULL", "INNER", "OUTER", "CROSS", "NATURAL"].contains name.toUpper
  | .quotedIdent .. | .string _ => true
  | _ => false

def number : Token → Bool
  | .integer _ source => source.all (fun text => !text.contains '_')
  | .real source => !source.contains '_'
  | _ => false

def unsigned (tokens : List Token) : Option (List Token) := do
  let token :: rest := tokens | none
  if number token then some rest else none

def signed : List Token → Option (List Token)
  | .symbol "+" :: rest | .symbol "-" :: rest => unsigned rest
  | tokens => unsigned tokens

def dimensions : List Token → Bool
  | [] => true
  | .symbol "(" :: tokens =>
      match signed tokens with
      | some [.symbol ")"] => true
      | some (.symbol "," :: rest) => signed rest == some [.symbol ")"]
      | _ => false
  | _ => false

/-- The lexer represents a blob with two adjacent tokens. Such a token cannot
be a type-name word; separated X and string tokens can be two ordinary words. -/
def containsBlobToken : List Token → Bool
  | .ident name :: .string value :: rest =>
      name.toUpper == "X" || containsBlobToken (.string value :: rest)
  | _ :: rest => containsBlobToken rest
  | [] => false

def valid (source : String) : Bool :=
  match lex source with
  | .error _ => false
  | .ok raw =>
      let tokens := significant raw.toList
      !containsBlobToken raw.toList &&
        (tokens.isEmpty || (word tokens.head! && dimensions (tokens.dropWhile word)))

/-- build.c removes an unquoted trailing ALWAYS from spans of at least 16
bytes, and then removes a preceding GENERATED suffix. This is a historical
string operation, including when the suffix is part of one type-name token. -/
def adjusted (source : String) : String :=
  if source.toUTF8.size ≥ 16 && source.toUpper.endsWith "ALWAYS" then
    let withoutAlways := (source.dropEnd 6).trimAsciiEnd.toString
    if withoutAlways.toUTF8.size ≥ 9 && withoutAlways.toUpper.endsWith "GENERATED" then
      (withoutAlways.dropEnd 9).trimAsciiEnd.toString
    else withoutAlways
  else source

def standardNames : List String := ["ANY", "BLOB", "INT", "INTEGER", "REAL", "TEXT"]

def standardAdjusted (source : String) : Option String := do
  let tokens ← (lex source).toOption
  let [token, .eof] := tokens.toList | none
  let name ← match token with
    | .ident name | .quotedIdent name _ | .string name => some name
    | _ => none
  if standardNames.contains name.toUpper then some name.toUpper else none

def standard (source : String) : Option String := standardAdjusted (adjusted source)

def name (source : String) : String :=
  let source := adjusted source
  match standardAdjusted source with
  | some name => name
  | none => match lex source with
      | .ok tokens => match (significant tokens.toList).head? with
          | some (.quotedIdent name _) | some (.string name) => name
          | _ => source
      | .error _ => source

/-- A quoted custom name such as "text" extra has a lowercase pragma type.
A harmless precision suffix keeps it custom when canonical SQL is printed. -/
def preserveCase (name : String) : Bool :=
  standardNames.contains name.toUpper && name != name.toUpper

end SQLeanite.SQLite.ColumnType
