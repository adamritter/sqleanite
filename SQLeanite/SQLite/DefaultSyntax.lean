import SQLeanite.SQLite.PragmaSyntax

/-! The DEFAULT productions in SQLite 3.53.4 parse.y: a term, a signed
term, an identifier string, or a parenthesized expression. -/
namespace SQLeanite.SQLite.DefaultSyntax

def identifier (name : String) : Bool :=
  PragmaSyntax.bareName name &&
    !["left", "right", "full", "inner", "outer", "cross", "natural"].contains name.toLower

def term : List Token → Bool
  | [.integer ..] | [.real _] | [.string _] => true
  | [.ident name] => ["null", "current_time", "current_date", "current_timestamp"].contains name.toLower
  | [.ident name, .string _] => name.toLower == "x"
  | _ => false

def shape : List Token → Bool
  | .symbol "(" :: rest => (rest.getLast?).any (fun t => match t with | .symbol ")" => true | _ => false)
  | .symbol "+" :: rest | .symbol "-" :: rest => term rest
  | [.ident name] => identifier name || term [.ident name]
  | [.quotedIdent ..] => true
  | tokens => term tokens

end SQLeanite.SQLite.DefaultSyntax
