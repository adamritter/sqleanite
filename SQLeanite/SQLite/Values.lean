import SQLeanite.SQLite.Scalar

/-! The constant VALUES lowering in SQLite 3.53.4 insert.c. An initial CAST
keeps a row as a direct SELECT. The first row without affinity starts a
coroutine with the remaining rows, provided there is a following row. This
changes result metadata and whether OFFSET skips expression evaluation. -/
namespace SQLeanite.SQLite.Values

/-- Number of initial rows left as individual SELECTs by sqlite3MultiValues.
All expressions are separately checked by the caller for scalar admission. -/
def directCount : List (Array Expr) → Nat
  | [] => 0
  | row :: rest =>
      if rest.isEmpty || row.any (fun value => (Scalar.expressionAffinity value).isSome) then
        1 + directCount rest
      else 0

theorem directCount_le_length (rows : List (Array Expr)) : directCount rows ≤ rows.length := by
  induction rows with
  | nil => simp [directCount]
  | cons row rest ih =>
      simp only [directCount, List.length_cons]
      split <;> omega

/-- A projection and whether it reads synthetic coroutine/subquery columns.
A multi-row VALUES on the right of a compound is wrapped as one source. -/
def projections (rows : List (Array Expr)) (wrapped : Bool) : List (Array Expr × Bool) :=
  if wrapped && rows.length > 1 then rows.head?.toList.map (·, true)
  else
    let count := directCount rows
    (rows.take count).map (·, false) ++ ((rows.drop count).head?).toList.map (·, true)

/-- Generated source columns acquire BINARY when the defining expression has
no collation. Direct SELECT expressions retain the absence of a collation. -/
def projectionCollations (row : Array Expr) (source : Bool) : List (Option String) :=
  row.toList.map fun expression =>
    (ExprCollation.effectiveName expression).orElse fun _ => if source then some "binary" else none

def collations (rows : List (Array Expr)) (wrapped : Bool) : List (Option String) :=
  let width := rows.head?.map Array.size |>.getD 0
  (projections rows wrapped).foldl (fun current (row, source) =>
    current.zipWith (fun left right => left.orElse fun _ => right) (projectionCollations row source))
    (List.replicate width none)

end SQLeanite.SQLite.Values
