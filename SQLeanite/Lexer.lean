import SQLeanite.Syntax

namespace SQLeanite

inductive Token where
  | space (value : String)
  | ident (value : String)
  | quotedIdent (value source : String)
  | string (value : String)
  | integer (value : Int)
  | real (source : String)
  | symbol (value : String)
  | eof
  deriving Repr, Inhabited, BEq

def Token.render : Token → String
  | .space s => s
  | .ident s => s
  | .quotedIdent _ source => source
  | .string s => "'" ++ s ++ "'"
  | .integer i => toString i
  | .real s => s
  | .symbol s => s
  | .eof => "end of input"

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_' || c.val ≥ 128
private def isIdentRest (c : Char) : Bool := isIdentStart c || c.isDigit || c == '$'

private def scanQuoted (quote : Char) (cs : List Char) (acc : List Char) :
    Except String (String × List Char) :=
  match cs with
  | [] => .error "unterminated quoted token"
  | c :: rest =>
    if c == quote then
      match rest with
      | d :: tail => if d == quote then scanQuoted quote tail (quote :: acc)
                     else .ok (String.mk acc.reverse, rest)
      | [] => .ok (String.mk acc.reverse, [])
    else scanQuoted quote rest (c :: acc)

private def skipBlockComment : List Char → Except String (List Char)
  | [] => .error "unterminated block comment"
  | '*' :: '/' :: rest => .ok rest
  | _ :: rest => skipBlockComment rest

private def takeWhile (p : Char → Bool) (cs : List Char) : List Char × List Char :=
  (cs.takeWhile p, cs.dropWhile p)

private def hexDigit? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' <= c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def parseHexNatAux : List Char → Nat → Option Nat
  | [], value => some value
  | digit :: rest, value => do
      parseHexNatAux rest (value * 16 + (← hexDigit? digit))

private def parseHexNat? (digits : List Char) : Option Nat :=
  if digits.isEmpty then none else parseHexNatAux digits 0

private def lexCharsFuel : Nat → List Char → Array Token → Except String (Array Token)
  | 0, _, _ => throw "tokenizer progress limit exceeded"
  | fuel + 1, cs, out => do
    match cs with
    | [] => pure (out.push .eof)
    | c :: rest =>
      if c.isWhitespace then
        let (suffix, tail) := takeWhile Char.isWhitespace rest
        lexCharsFuel fuel tail (out.push (.space (String.mk (c :: suffix))))
      else if c == '-' && rest.head? == some '-' then
        lexCharsFuel fuel (rest.dropWhile (fun x => x != '\n')) out
      else if c == '/' && rest.head? == some '*' then
        let tail ← skipBlockComment rest.tail!
        lexCharsFuel fuel tail out
      else if c == '\'' then
        let (s, tail) ← scanQuoted '\'' rest []
        lexCharsFuel fuel tail (out.push (.string s))
      else if c == '"' then
        let (s, tail) ← scanQuoted '"' rest []
        lexCharsFuel fuel tail (out.push (.quotedIdent s ("\"" ++ s.replace "\"" "\"\"" ++ "\"")))
      else if c == '`' then
        let (s, tail) ← scanQuoted '`' rest []
        lexCharsFuel fuel tail (out.push (.quotedIdent s ("`" ++ s.replace "`" "``" ++ "`")))
      else if c == '[' then
        let (inside, tail) := takeWhile (fun x => x != ']') rest
        match tail with
        | [] => throw "unterminated bracketed identifier"
        | _ :: after =>
          let value := String.mk inside
          lexCharsFuel fuel after (out.push (.quotedIdent value ("[" ++ value ++ "]")))
      else if c == ':' || c == '@' || c == '$' then
        let (name, tail) := takeWhile isIdentRest rest
        if name.isEmpty then throw s!"unrecognized token: {c}"
        else
          let parameter := out.push (.ident "lean_unbound_parameter")
            |>.push (.symbol "(") |>.push (.symbol ")")
          lexCharsFuel fuel tail parameter
      else if c == '?' then
        let (_, tail) := takeWhile Char.isDigit rest
        let parameter := out.push (.ident "lean_unbound_parameter")
          |>.push (.symbol "(") |>.push (.symbol ")")
        lexCharsFuel fuel tail parameter
      else if isIdentStart c then
        let (suffix, tail) := takeWhile isIdentRest rest
        lexCharsFuel fuel tail (out.push (.ident (String.mk (c :: suffix))))
      else if c == '0' && rest.head?.any (fun x => x == 'x' || x == 'X') then
        let (digits, tail) := takeWhile (fun x => (hexDigit? x).isSome) rest.tail!
        match parseHexNat? digits with
        | some value => lexCharsFuel fuel tail (out.push (.integer (Int.ofNat value)))
        | none => throw "unrecognized token: hexadecimal integer"
      else if c.isDigit || (c == '.' && rest.head?.any Char.isDigit) then
        let (whole, tail₁) := takeWhile (fun x => x.isDigit) rest
        let numPrefix := c :: whole
        let (fraction, tail₂) :=
          match tail₁ with
          | '.' :: after =>
            let (digits, tail) := takeWhile (fun x => x.isDigit) after
            ('.' :: digits, tail)
          | _ => ([], tail₁)
        let (exponent, tail₃) :=
          match tail₂ with
          | e :: after => if e == 'e' || e == 'E' then
              match after with
              | sign :: more => if sign == '+' || sign == '-' then
                  let (digits, tail) := takeWhile (fun x => x.isDigit) more
                  (e :: sign :: digits, tail)
                else
                  let (digits, tail) := takeWhile (fun x => x.isDigit) after
                  (e :: digits, tail)
              | [] => ([e], [])
            else ([], tail₂)
          | [] => ([], [])
        let source := String.mk (numPrefix ++ fraction ++ exponent)
        if fraction.isEmpty && exponent.isEmpty then
          match source.toInt? with
          | some i => lexCharsFuel fuel tail₃ (out.push (.integer i))
          | none => throw s!"invalid integer: {source}"
        else lexCharsFuel fuel tail₃ (out.push (.real source))
      else if c == '#' then
        let (suffix, tail) := takeWhile isIdentRest rest
        lexCharsFuel fuel tail (out.push (.symbol (String.mk (c :: suffix))))
      else
        let two := String.mk [c, rest.head?.getD ' ']
        let three := String.mk [c, rest.head?.getD ' ', (rest.drop 1).head?.getD ' ']
        if three == "->>" then
          lexCharsFuel fuel (rest.drop 2) (out.push (.symbol three))
        else if ["<=", ">=", "!=", "<>", "==", "||", "<<", ">>", "->"].contains two then
          lexCharsFuel fuel rest.tail! (out.push (.symbol two))
        else if "(),;.*+-/%=<>~&|?".contains c then
          lexCharsFuel fuel rest (out.push (.symbol c.toString))
        else throw s!"unrecognized character '{c}'"

private def lexChars (cs : List Char) (out : Array Token) : Except String (Array Token) :=
  lexCharsFuel (Nat.succ cs.length) cs out

def lex (sql : String) : Except String (Array Token) := lexChars sql.toList #[]

theorem lex_budget_exceeds_character_count (sql : String) :
    sql.toList.length < Nat.succ sql.toList.length :=
  Nat.lt_succ_self _

theorem lex_empty : lex "" = .ok #[.eof] := by
  rfl

end SQLeanite
