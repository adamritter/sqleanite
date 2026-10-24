import SQLeanite.SQLite.Text

/-!
SQLite 3.53.4 func.c patternCompare/likeFunc and utf.c sqlite3Utf8Read.
Matching uses suffix dynamic programming instead of recursive backtracking.
ASCII case folding, malformed GLOB classes, NUL termination, the default
pattern-byte limit and SQLite's permissive UTF-8 reader are retained.
-/
namespace SQLeanite.SQLite.Pattern

def continuation (b : UInt8) : Bool := (b &&& 0xc0) == 0x80

def leader (b : UInt8) : UInt32 :=
  UInt32.ofNat (b.toNat &&& (if b < 0xe0 then 31 else if b < 0xf0 then 15
    else if b < 0xf8 then 7 else if b < 0xfc then 3 else if b < 0xfe then 1 else 0))

/-- SQLite intentionally accepts isolated continuation bytes and over-wide
codepoints. Overlong ASCII, surrogates and U+FFFE/U+FFFF become U+FFFD. -/
def decodeFuel : Nat → List UInt8 → List UInt32
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, b :: rest =>
      if b == 0 then []
      else if b < 0xc0 then b.toUInt32 :: decodeFuel fuel rest
      else
        let (extra, tail) := rest.span continuation
        let code := extra.foldl (fun (c : UInt32) (b : UInt8) => (c <<< 6) + (b.toUInt32 &&& 0x3f)) (leader b)
        let code := if code < 0x80 || (code &&& 0xfffff800) == 0xd800 ||
            (code &&& 0xfffffffe) == 0xfffe then 0xfffd else code
        code :: decodeFuel fuel tail

def decode (bytes : Array UInt8) : List UInt32 := decodeFuel bytes.size bytes.toList

def foldASCII (c : UInt32) : UInt32 := if 65 ≤ c && c ≤ 90 then c + 32 else c

theorem foldASCII_nonASCII (c : UInt32) (h : 128 ≤ c) : foldASCII c = c := by
  simp only [foldASCII]
  have : ¬c ≤ 90 := by
    intro upper
    have low := h
    change 128 ≤ c.toNat at low
    change c.toNat ≤ 90 at upper
    omega
  simp [this]

inductive Atom where
  | literal (code : UInt32)
  | one
  | star
  | set (inverted : Bool) (ranges : List (UInt32 × UInt32))
  | never
  deriving Repr

/-- A range does not erase its first literal: SQLite has already compared it
before reading '-'. A reversed range therefore still admits that first code. -/
def classScan : Nat → List UInt32 → Option UInt32 → List (UInt32 × UInt32) →
    Option (List (UInt32 × UInt32) × List UInt32)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, c :: rest, prior, ranges =>
      if c == 93 then some (ranges, rest)
      else if c == 45 then
        match prior, rest with
        | some first, last :: tail =>
            if last != 93 then classScan fuel tail none ((first, last) :: ranges)
            else classScan fuel rest (some c) ((c, c) :: ranges)
        | _, _ => classScan fuel rest (some c) ((c, c) :: ranges)
      else classScan fuel rest (some c) ((c, c) :: ranges)

def characterClass (chars : List UInt32) : Option (Atom × List UInt32) := do
  let (inverted, chars) := if chars.head? == some 94 then (true, chars.tail!) else (false, chars)
  let (ranges, chars) := if chars.head? == some 93 then ([(93, 93)], chars.tail!) else ([], chars)
  let (ranges, remaining) ← classScan (chars.length + 1) chars none ranges
  return (.set inverted ranges, remaining)

def compileFuel (glob : Bool) (escape : Option UInt32) : Nat → List UInt32 → List Atom
  | 0, _ => [.never]
  | _ + 1, [] => []
  | fuel + 1, c :: rest =>
      if !glob && escape == some c then
        match rest with
        | [] => [.never]
        | escaped :: tail => .literal escaped :: compileFuel glob escape fuel tail
      else if c == (if glob then 42 else 37) then .star :: compileFuel glob escape fuel rest
      else if c == (if glob then 63 else 95) then .one :: compileFuel glob escape fuel rest
      else if glob && c == 91 then
        match characterClass rest with
        | none => [.never]
        | some (set, tail) => set :: compileFuel glob escape fuel tail
      else .literal c :: compileFuel glob escape fuel rest

def accepts (noCase : Bool) (atom : Atom) (c : UInt32) : Bool :=
  match atom with
  | .literal expected => if noCase then foldASCII expected == foldASCII c else expected == c
  | .one => true
  | .set inverted ranges => (ranges.any fun (a, b) => a ≤ c && c ≤ b) != inverted
  | .star => true
  | .never => false

/-- A star matches the rest of the pattern at any remaining input suffix. -/
def starRow (previous : List Bool) : List Bool :=
  previous.reverse.foldl (fun acc value => (value || acc.headD false) :: acc) []

def nextRow (noCase : Bool) (chars : List UInt32) (previous : List Bool) (atom : Atom) : List Bool :=
  match atom with
  | .star => starRow previous
  | atom => (chars.zip previous.tail!).map (fun (c, suffix) => accepts noCase atom c && suffix) ++ [false]

/-- Row i records whether the current pattern suffix matches text suffix i.
Each step keeps only one row; work is O(pattern length * text length). -/
def fullMatch (noCase : Bool) (pattern : List Atom) (chars : List UInt32) : Bool :=
  let base := List.replicate chars.length false ++ [true]
  (pattern.reverse.foldl (nextRow noCase chars) base).headD false

theorem matches_empty (noCase : Bool) (chars : List UInt32) :
    fullMatch noCase [] chars = chars.isEmpty := by
  cases chars <;> simp [fullMatch, List.replicate_succ]

/-- The default SQLite build permits BLOB operands. Pattern length is checked
before ESCAPE, which is validated before either data operand's NULL test. -/
def evaluate (glob : Bool) (pattern input : Value) (escape : Option Value := none) :
    Except String Value := do
  let bytes := Text.bytes pattern
  if bytes.size > 50000 then throw "LIKE or GLOB pattern too complex"
  if escape.any Text.isNull then return .null
  let escape ← match escape with
    | none => pure none
    | some value => do
        match decode (Text.bytes value) with
        | [code] => pure (some code)
        | _ => throw "ESCAPE expression must be a single character"
  if Text.isNull pattern || Text.isNull input then return .null
  let chars := decode bytes
  let tokens := compileFuel glob escape (chars.length + 1) chars
  return .integer (if fullMatch (!glob) tokens (decode (Text.bytes input)) then 1 else 0)

theorem evaluate_null_input (glob : Bool) (pattern : Value)
    (bounded : (Text.bytes pattern).size ≤ 50000) :
    evaluate glob pattern .null = .ok .null := by
  simp [evaluate, Nat.not_lt.mpr bounded, Text.isNull, pure, Except.pure, bind, Except.bind]

end SQLeanite.SQLite.Pattern
