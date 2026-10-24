import Std

namespace SQLeanite.SQLite

inductive Affinity where
  | integer | text | blob | real | numeric
  deriving BEq, DecidableEq, Repr, Inhabited

/-- build.c: sqlite3AffinityType. The first matching class wins, including
the surprising INTEGER affinity of FLOATING POINT. An absent type is BLOB. -/
def typeAffinity (typeName : String) : Affinity :=
  let s := typeName.toUpper
  if (s.splitOn "INT").length > 1 then .integer
  else if ["CHAR", "CLOB", "TEXT"].any (fun part => (s.splitOn part).length > 1) then .text
  else if s.isEmpty || (s.splitOn "BLOB").length > 1 then .blob
  else if ["REAL", "FLOA", "DOUB"].any (fun part => (s.splitOn part).length > 1) then .real
  else .numeric

def Affinity.isNumeric : Affinity → Bool
  | .integer | .real | .numeric => true
  | _ => false

/-- All three numeric affinities use the same comparison coercion. -/
def Affinity.comparison : Affinity → Affinity
  | .integer | .real | .numeric => .numeric
  | other => other

end SQLeanite.SQLite
