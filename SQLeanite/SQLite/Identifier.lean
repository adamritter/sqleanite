import SQLeanite.SQLite.PragmaSyntax

/-! SQLite parse.y distinguishes nm (idj or STRING) from ids (ID or STRING).
INDEXED and join-kind keywords are allowed in nm, including explicit AS aliases,
but not in an implicit alias or a type-name word. Quoting bypasses keyword roles. -/
namespace SQLeanite.SQLite.Identifier

def nameToken (token : Token) : Option String := PragmaSyntax.nameToken false token

def joinWords : List String := ["INDEXED", "LEFT", "RIGHT", "FULL", "INNER", "OUTER", "CROSS", "NATURAL"]

def aliasToken (token : Token) : Option String :=
  match token with
  | .ident name => if joinWords.contains name.toUpper then none else nameToken token
  | _ => nameToken token

/-- Expression-leading CAST, RAISE and clock keywords have dedicated grammar
productions, so they do not fall back to column names. STRING may qualify a
column, but an unqualified STRING is a literal. -/
def primaryToken (qualified : Bool) (token : Token) : Option String :=
  match token with
  | .ident name =>
      if ["CAST", "RAISE", "CURRENT_DATE", "CURRENT_TIME", "CURRENT_TIMESTAMP"].contains name.toUpper
      then none else nameToken token
  | .string name => if qualified then some name else none
  | _ => nameToken token

theorem primaryToken_quoted (qualified : Bool) (name source : String) :
    primaryToken qualified (.quotedIdent name source) = some name := rfl

theorem primaryToken_string (name : String) :
    primaryToken false (.string name) = none := rfl

/-- tokenize.c getToken folds fallback keywords and JOIN_KW to ID for OVER
lookahead, but not bare INDEXED or FILTER. Quoted names remain identifiers. -/
def windowNameToken (token : Token) : Bool :=
  match token with
  | .ident name => !["INDEXED", "FILTER"].contains name.toUpper && (nameToken token).isSome
  | _ => (nameToken token).isSome

theorem windowNameToken_quoted (name source : String) :
    windowNameToken (.quotedIdent name source) = true := rfl

theorem aliasToken_name (token : Token) (name : String)
    (matched : aliasToken token = some name) : nameToken token = some name := by
  cases token <;> try exact matched
  case ident value =>
    simp only [aliasToken] at matched
    split at matched
    · contradiction
    · exact matched

theorem aliasToken_join (name : String) (keyword : joinWords.contains name.toUpper = true) :
    aliasToken (.ident name) = none := by
  change (if joinWords.contains name.toUpper then none else nameToken (.ident name)) = none
  rw [keyword]
  rfl

theorem aliasToken_quoted (name source : String) :
    aliasToken (.quotedIdent name source) = some name := rfl

end SQLeanite.SQLite.Identifier
