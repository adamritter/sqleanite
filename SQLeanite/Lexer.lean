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

/-- One transparent lexical-grammar step.  Comments intentionally emit no
tokens; parameters emit the same explicit unsupported-call token sequence as
SQLite's compatibility parser.  Keeping this operation separate from the
recursive driver makes `Tokenizes` an inspectable specification rather than a
restatement of the final `lex` equation. -/
structure LexStep where
  emitted : List Token
  rest : List Char

private def parameterTokens : List Token :=
  [.ident "lean_unbound_parameter", .symbol "(", .symbol ")"]

def lexicalStep : List Char → Except String (Option LexStep)
  | [] => pure none
  | c :: rest => do
      if c.isWhitespace then
        let (suffix, tail) := takeWhile Char.isWhitespace rest
        pure (some ⟨[.space (String.mk (c :: suffix))], tail⟩)
      else if c == '-' && rest.head? == some '-' then
        pure (some ⟨[], rest.dropWhile (fun x => x != '\n')⟩)
      else if c == '/' && rest.head? == some '*' then
        let tail ← skipBlockComment rest.tail!
        pure (some ⟨[], tail⟩)
      else if c == '\'' then
        let (s, tail) ← scanQuoted '\'' rest []
        pure (some ⟨[.string s], tail⟩)
      else if c == '"' then
        let (s, tail) ← scanQuoted '"' rest []
        pure (some ⟨[.quotedIdent s
          ("\"" ++ s.replace "\"" "\"\"" ++ "\"")], tail⟩)
      else if c == '`' then
        let (s, tail) ← scanQuoted '`' rest []
        pure (some ⟨[.quotedIdent s
          ("`" ++ s.replace "`" "``" ++ "`")], tail⟩)
      else if c == '[' then
        let (inside, tail) := takeWhile (fun x => x != ']') rest
        match tail with
        | [] => throw "unterminated bracketed identifier"
        | _ :: after =>
          let value := String.mk inside
          pure (some ⟨[.quotedIdent value ("[" ++ value ++ "]")], after⟩)
      else if c == ':' || c == '@' || c == '$' then
        let (name, tail) := takeWhile isIdentRest rest
        if name.isEmpty then throw s!"unrecognized token: {c}"
        else pure (some ⟨parameterTokens, tail⟩)
      else if c == '?' then
        let (_, tail) := takeWhile Char.isDigit rest
        pure (some ⟨parameterTokens, tail⟩)
      else if isIdentStart c then
        let (suffix, tail) := takeWhile isIdentRest rest
        pure (some ⟨[.ident (String.mk (c :: suffix))], tail⟩)
      else if c == '0' && rest.head?.any (fun x => x == 'x' || x == 'X') then
        let (digits, tail) :=
          takeWhile (fun x => (hexDigit? x).isSome) rest.tail!
        match parseHexNat? digits with
        | some value => pure (some ⟨[.integer (Int.ofNat value)], tail⟩)
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
          | some i => pure (some ⟨[.integer i], tail₃⟩)
          | none => throw s!"invalid integer: {source}"
        else pure (some ⟨[.real source], tail₃⟩)
      else if c == '#' then
        let (suffix, tail) := takeWhile isIdentRest rest
        pure (some ⟨[.symbol (String.mk (c :: suffix))], tail⟩)
      else
        let two := String.mk [c, rest.head?.getD ' ']
        let three :=
          String.mk [c, rest.head?.getD ' ', (rest.drop 1).head?.getD ' ']
        if three == "->>" then
          pure (some ⟨[.symbol three], rest.drop 2⟩)
        else if ["<=", ">=", "!=", "<>", "==", "||", "<<", ">>",
            "->"].contains two then
          pure (some ⟨[.symbol two], rest.tail!⟩)
        else if "(),;.*+-/%=<>~&|?".contains c then
          pure (some ⟨[.symbol c.toString], rest⟩)
        else throw s!"unrecognized character '{c}'"

/-- Declarative tokenization trace.  Every emitted token chunk is justified by
one `lexicalStep`, and the sole terminal token is EOF. -/
inductive Tokenizes : List Char → List Token → Prop where
  | eof : Tokenizes [] [.eof]
  | step {input : List Char} {result : LexStep} {tokens : List Token}
      (scanned : lexicalStep input = .ok (some result))
      (tail : Tokenizes result.rest tokens) :
      Tokenizes input (result.emitted ++ tokens)

private def lexCertifiedFuel : (fuel : Nat) → (input : List Char) →
    Except String { tokens : List Token // Tokenizes input tokens }
  | 0, _ => throw "tokenizer progress limit exceeded"
  | _ + 1, [] => pure ⟨[.eof], .eof⟩
  | fuel + 1, head :: rest =>
      match scanned : lexicalStep (head :: rest) with
      | .error message => .error message
      | .ok none => .error "tokenizer stopped before end of input"
      | .ok (some result) =>
          match lexCertifiedFuel fuel result.rest with
          | .error message => .error message
          | .ok tail => .ok ⟨result.emitted ++ tail.val,
              .step scanned tail.property⟩

def lexCertified (sql : String) :
    Except String { tokens : Array Token //
      Tokenizes sql.toList tokens.toList } :=
  (lexCertifiedFuel (Nat.succ sql.toList.length) sql.toList).map fun result =>
    ⟨result.val.toArray, by simpa using result.property⟩

private def appendTokens : Array Token → List Token → Array Token
  | output, [] => output
  | output, token :: tokens => appendTokens (output.push token) tokens

private theorem appendTokens_append (output : Array Token)
    (left right : List Token) :
    appendTokens (appendTokens output left) right =
      appendTokens output (left ++ right) := by
  induction left generalizing output with
  | nil => rfl
  | cons token tokens induction =>
      simp only [appendTokens, List.cons_append]
      exact induction (output.push token)

private theorem appendTokens_toList (output : Array Token) (tokens : List Token) :
    (appendTokens output tokens).toList = output.toList ++ tokens := by
  induction tokens generalizing output with
  | nil => simp [appendTokens]
  | cons token tokens induction =>
      simp only [appendTokens, induction, Array.push_toList,
        List.append_assoc, List.singleton_append]

/-- Tail-recursive erasure of the certified lexical grammar.  The Array is
uniquely owned along the loop, so native `push` is in-place; the theorem below
connects this fast implementation to the proof-producing reference. -/
private def lexFastFuel : Nat → List Char → Array Token →
    Except String (Array Token)
  | 0, _, _ => throw "tokenizer progress limit exceeded"
  | _ + 1, [], output => pure (output.push .eof)
  | fuel + 1, head :: rest, output =>
      match lexicalStep (head :: rest) with
      | .error message => .error message
      | .ok none => .error "tokenizer stopped before end of input"
      | .ok (some result) =>
          lexFastFuel fuel result.rest (appendTokens output result.emitted)

private theorem lexFastFuel_sound :
    ∀ (fuel : Nat) (input : List Char) (output final : Array Token),
      lexFastFuel fuel input output = .ok final →
      ∃ suffix : List Token,
        final.toList = output.toList ++ suffix ∧ Tokenizes input suffix
  | 0, input, output, final, success => by
      simp [lexFastFuel] at success
  | fuel + 1, [], output, final, success => by
      change Except.ok (output.push .eof) = Except.ok final at success
      have equal : output.push .eof = final := Except.ok.inj success
      subst final
      exact ⟨[.eof], by simp, .eof⟩
  | fuel + 1, head :: rest, output, final, success => by
      cases scanned : lexicalStep (head :: rest) with
      | error message => simp [lexFastFuel, scanned] at success
      | ok result =>
          cases result with
          | none => simp [lexFastFuel, scanned] at success
          | some step =>
              rw [lexFastFuel, scanned] at success
              rcases lexFastFuel_sound fuel step.rest
                  (appendTokens output step.emitted) final success with
                ⟨suffix, finalShape, tail⟩
              refine ⟨step.emitted ++ suffix, ?_, .step scanned tail⟩
              rw [finalShape, appendTokens_toList]
              simp [List.append_assoc]

private def lexFast (sql : String) : Except String (Array Token) :=
  lexFastFuel (Nat.succ sql.toList.length) sql.toList #[]

/-- The live lexer is the proved tail-recursive erasure of `lexCertified`. -/
def lex (sql : String) : Except String (Array Token) :=
  lexFast sql

theorem lex_sound {sql : String} {tokens : Array Token}
    (success : lex sql = .ok tokens) : Tokenizes sql.toList tokens.toList := by
  unfold lex lexFast at success
  rcases lexFastFuel_sound (Nat.succ sql.toList.length) sql.toList #[] tokens
      success with ⟨suffix, shape, trace⟩
  have same : tokens.toList = suffix := by simpa using shape
  simpa [same] using trace

theorem lex_budget_exceeds_character_count (sql : String) :
    sql.toList.length < Nat.succ sql.toList.length :=
  Nat.lt_succ_self _

theorem lex_empty : lex "" = .ok #[.eof] := by
  rfl

end SQLeanite
