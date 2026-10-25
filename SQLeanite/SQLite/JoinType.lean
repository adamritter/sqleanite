import SQLeanite.Lexer

/-! sqlite3JoinType combines at most three join keywords. Repetition and
nonstandard order are legal; INNER/CROSS cannot mix with an outer direction.
The original CROSS flag is retained even when two-table evaluation coincides. -/
namespace SQLeanite.SQLite.JoinType

structure Flags where
  natural : Bool := false
  left : Bool := false
  right : Bool := false
  cross : Bool := false
  deriving Repr, DecidableEq

def keywords : List String := ["natural", "left", "right", "full", "outer", "inner", "cross"]

def keyword (token : Token) : Option String :=
  match token with
  | .ident name => if keywords.contains name.toLower then some name.toLower else none
  | _ => none

def classify (source : List String) : Option Flags :=
  if source.length ≤ 3 then
    let words := source.map String.toLower
    if words.all (keywords.contains ·) then
      let flags : Flags := {
        natural := words.contains "natural"
        left := words.contains "left" || words.contains "full"
        right := words.contains "right" || words.contains "full"
        cross := words.contains "cross" }
      let inner := words.contains "inner" || flags.cross
      let outer := words.contains "outer" || flags.left || flags.right
      if (inner && outer) || (outer && !flags.left && !flags.right) then none
      else some flags
    else none
  else none

theorem classify_length (source : List String) (flags : Flags)
    (accepted : classify source = some flags) : source.length ≤ 3 := by
  unfold classify at accepted
  split at accepted
  · assumption
  · contradiction

end SQLeanite.SQLite.JoinType
