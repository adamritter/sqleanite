import SQLeanite.CoreExpr

/-! USING and NATURAL refer to declared visible columns, not implicit rowid
aliases. The shared column keeps its name and both physical positions, so the
same merge rule can drive SQL binding, star expansion and CTAS metadata. -/
namespace SQLeanite.CoreJoinUsing

structure Column where
  name : String
  left : Nat
  right : Nat
  deriving Repr, DecidableEq

def declaredColumn? (schema : Core.Schema) (name : String) : Option Nat :=
  schema.visibleColumnIndices.find? fun index =>
    (schema.columns[index]?).any (fun column => column.name.toLower == name.toLower)

theorem declaredColumn_visible (schema : Core.Schema) (name : String) (index : Nat)
    (found : declaredColumn? schema name = some index) :
    index ∈ schema.visibleColumnIndices := by
  exact List.mem_of_find?_eq_some found

def columns (left right : Core.Schema) (source : TableRef) : Except String (List Column) := do
  if source.naturalJoin && (source.joinOn.isSome || !source.usingColumns.isEmpty) then
    throw "a NATURAL join may not have an ON or USING clause"
  if source.joinOn.isSome && !source.usingColumns.isEmpty then
    throw "cannot have both ON and USING clauses in the same join"
  let names := if source.naturalJoin then
      (left.visibleColumns.filter (fun column => (declaredColumn? right column.name).isSome)).map (·.name)
    else source.usingColumns.toList
  names.mapM fun name => do
    let some li := declaredColumn? left name
      | throw s!"cannot join using column {name} - column not present in both tables"
    let some ri := declaredColumn? right name
      | throw s!"cannot join using column {name} - column not present in both tables"
    return { name := name.toLower, left := li, right := ri }

def merges (shared : List Column) (name : String) (left right : Nat) : Bool :=
  shared.any fun column => column.name == name.toLower && column.left == left && column.right == right

def suppressesRight (shared : List Column) (index : Nat) : Bool :=
  shared.any fun column => column.right == index

def suppressesName (shared : List Column) (name : String) (index : Nat) : Bool :=
  shared.any fun column => column.name == name.toLower && column.right == index

end SQLeanite.CoreJoinUsing
