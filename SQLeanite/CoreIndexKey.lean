import SQLeanite.CoreOverflow.ResolvePlansNextPage
import SQLeanite.SQLite.Collation

/-! Physical rowid-index records contain all declared keys followed by the
actual rowid. Key comparison and record encoding do not apply table affinity. -/
namespace SQLeanite.CoreIndexKey
open FileFormat

structure Entry where
  values : List Core.Value
  rowid : Core.Integer
  deriving DecidableEq

def Entry.recordValues (entry : Entry) : List Core.Value :=
  entry.values ++ [.integer entry.rowid]

@[simp] theorem Entry.recordValues_length (entry : Entry) :
    entry.recordValues.length = entry.values.length + 1 := by simp [recordValues]

def fromValues (values : List Core.Value) : Option Entry := do
  let .integer rowid :: reversed := values.reverse | none
  unless !reversed.isEmpty do none
  return { values := reversed.reverse, rowid }

theorem fromValues_recordValues (entry : Entry) (nonempty : entry.values ≠ []) :
    fromValues entry.recordValues = some entry := by
  cases entry with
  | mk values rowid =>
      simp [fromValues, Entry.recordValues, List.reverse_append, List.isEmpty_iff,
        List.reverse_eq_nil_iff, nonempty]

def compareValues : List SQLite.Collation.Kind → List Core.Value → List Core.Value → Ordering
  | _, [], [] => .eq
  | _, [], _ :: _ => .lt
  | _, _ :: _, [] => .gt
  | collations, left :: moreLeft, right :: moreRight =>
      let order := SQLite.Collation.compareValue (collations.headD .binary) left right
      if order == .eq then compareValues collations.tail moreLeft moreRight else order

def uniqueConflict (collations : List SQLite.Collation.Kind) (left right : List Core.Value) : Bool :=
  !left.any (fun value => value == .null) && !right.any (fun value => value == .null) &&
    left.length == right.length && compareValues collations left right == .eq

@[simp] theorem uniqueConflict_head_null (collations : List SQLite.Collation.Kind)
    (left right : List Core.Value) : uniqueConflict collations (.null :: left) right = false := by
  simp [uniqueConflict]

def adjacentUnique (unique : Bool) (collations : List SQLite.Collation.Kind) : List Entry → Bool
  | left :: right :: rest =>
      !(unique && uniqueConflict collations left.values right.values) &&
        adjacentUnique unique collations (right :: rest)
  | _ => true

def entryLe (collations : List SQLite.Collation.Kind) (left right : Entry) : Bool :=
  let ordering := compareValues collations left.values right.values
  if ordering == .eq then left.rowid.value ≤ right.rowid.value else ordering == .lt

def valuesCellPlan? (values : List Core.Value) : Option CoreOverflow.CellPlan := do
  let record ← CoreFile.physicalRecord? (values.map PhysicalCodec.Value.recordField)
  if bounded : record.encode.length < 2 ^ 64 then
    let size : U64Value := ⟨record.encode.length, by simpa using bounded⟩
    some ⟨CoreOverflow.PayloadKind.index, encodeVarint size, record.encode⟩
  else none

def cellPlan? (entry : Entry) : Option CoreOverflow.CellPlan :=
  valuesCellPlan? entry.recordValues

end SQLeanite.CoreIndexKey
