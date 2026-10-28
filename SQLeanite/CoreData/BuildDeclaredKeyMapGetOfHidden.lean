import SQLeanite.CoreData.Value
import SQLeanite.PersistentPageTree.NodeInsertStepDonePathAgrees

namespace SQLeanite
namespace Core
attribute [local instance] lexOrd

theorem buildDeclaredKeyMap_get_of_hidden (schema : Schema) (rows : List Row)
    (key : DeclaredKey) (hidden : schema.hasHiddenRowid = true) :
    (buildDeclaredKeyMap schema rows).get? key =
      rows.find? (fun row => row.declaredKey schema == key) := by
  unfold buildDeclaredKeyMap
  rw [if_pos hidden]
  induction rows with
  | nil => simp
  | cons row rows induction =>
      simp only [List.foldr_cons]
      change ((rows.foldr
        (fun row (map : DeclaredKeyMap) =>
          map.insert (row.declaredKey schema) row) ∅).insert
          (row.declaredKey schema) row)[key]? = _
      rw [Std.TreeMap.getElem?_insert]
      simp only [DeclaredKey.compareOn_orderKey_eq, beq_iff_eq]
      change (rows.foldr
        (fun row (map : DeclaredKeyMap) =>
          map.insert (row.declaredKey schema) row) ∅)[key]? = _
        at induction
      by_cases same : row.declaredKey schema = key <;>
        simp [same, induction]

def DeclaredKeyMapRepresents (schema : Schema) (rows : List Row)
    (map : DeclaredKeyMap) : Prop :=
  schema.hasHiddenRowid = true → ∀ key,
    map.get? key = rows.find? (fun row => row.declaredKey schema == key)

theorem buildDeclaredKeyMap_represents (schema : Schema) (rows : List Row) :
    DeclaredKeyMapRepresents schema rows
      (buildDeclaredKeyMap schema rows) := by
  intro hidden key
  exact buildDeclaredKeyMap_get_of_hidden schema rows key hidden

def Row.keyLess (left right : Row) : Prop :=
  left.rowid.value < right.rowid.value

instance (left right : Row) : Decidable (Row.keyLess left right) :=
  by unfold Row.keyLess; infer_instance

/-- Bias a signed 64-bit integer into the natural key space without changing
order. This is the routing key shared by logical rows, persisted index rowids,
and the primary tree. -/
def Integer.treeKey (integer : Integer) : Nat :=
  (integer.value + Int.ofNat FileFormat.IntegerWidth.eight.midpoint).toNat

def Row.treeKey (row : Row) : Nat := row.rowid.treeKey

theorem Integer.treeKey_int (integer : Integer) :
    Int.ofNat integer.treeKey =
      integer.value + Int.ofNat FileFormat.IntegerWidth.eight.midpoint := by
  unfold Integer.treeKey
  exact Int.toNat_of_nonneg (by
    have lower := integer.lowerBound
    omega)

theorem Integer.treeKey_eq_iff (left right : Integer) :
    left.treeKey = right.treeKey ↔ left.value = right.value := by
  constructor
  · intro equal
    have coerced := congrArg Int.ofNat equal
    rw [left.treeKey_int, right.treeKey_int] at coerced
    omega
  · intro equal
    unfold Integer.treeKey
    rw [equal]

theorem Row.treeKey_int (row : Row) :
    Int.ofNat row.treeKey =
      row.rowid.value + Int.ofNat FileFormat.IntegerWidth.eight.midpoint := by
  exact row.rowid.treeKey_int

theorem Row.treeKey_lt_iff (left right : Row) :
    left.treeKey < right.treeKey ↔ left.rowid.value < right.rowid.value := by
  constructor
  · intro less
    have coerced : Int.ofNat left.treeKey < Int.ofNat right.treeKey :=
      Int.ofNat_lt.mpr less
    rw [left.treeKey_int, right.treeKey_int] at coerced
    omega
  · intro less
    apply Int.ofNat_lt.mp
    change Int.ofNat left.treeKey < Int.ofNat right.treeKey
    rw [left.treeKey_int, right.treeKey_int]
    omega

theorem Row.treeKey_eq_iff (left right : Row) :
    left.treeKey = right.treeKey ↔ left.rowid.value = right.rowid.value := by
  exact Integer.treeKey_eq_iff left.rowid right.rowid

def treeEntries (rows : List Row) :
    List (RecursiveBPlusTree.Entry Row) :=
  rows.map fun row => (row.treeKey, row)

theorem treeEntries_sorted {rows : List Row}
    (sorted : rows.Pairwise Row.keyLess) :
    PagedBTree.KeysStrictlySorted (treeEntries rows) := by
  unfold treeEntries PagedBTree.KeysStrictlySorted
  change (rows.map fun row => (row.treeKey, row)).Pairwise
    (fun left right : Nat × Row => left.1 < right.1)
  apply List.pairwise_map.mpr
  exact sorted.imp fun less => (Row.treeKey_lt_iff _ _).2 less

def IndexesWellFormed (schema : Schema) (indexes : List Index) : Prop :=
  (∀ index ∈ indexes, index.WellFormed schema) ∧
  namesUnique (indexes.map (·.name))

instance (schema : Schema) (indexes : List Index) :
    Decidable (IndexesWellFormed schema indexes) := by
  unfold IndexesWellFormed namesUnique Index.WellFormed
  infer_instance

def RowsWellFormed (schema : Schema) (rows : List Row) : Prop :=
  (∀ row ∈ rows, row.WellFormed schema) ∧ rows.Pairwise Row.keyLess

/-- A linear-time decision form of `RowsWellFormed`.  Checking every pair in
an ordered row list made validation quadratic even though integer order is
transitive.  Adjacent comparisons carry exactly the same information. -/
def RowsWellFormedAdjacent (schema : Schema) : List Row → Prop
  | [] => True
  | [row] => row.WellFormed schema
  | row :: next :: rows =>
      row.WellFormed schema ∧ Row.keyLess row next ∧
        RowsWellFormedAdjacent schema (next :: rows)

def decideRowsWellFormedAdjacent (schema : Schema) :
    (rows : List Row) → Decidable (RowsWellFormedAdjacent schema rows)
  | [] => isTrue trivial
  | [row] => by
      exact inferInstanceAs (Decidable (row.WellFormed schema))
  | row :: next :: rows =>
      let rowValid : Decidable (row.WellFormed schema) := inferInstance
      let ordered : Decidable (Row.keyLess row next) := inferInstance
      let tail := decideRowsWellFormedAdjacent schema (next :: rows)
      @instDecidableAnd (row.WellFormed schema)
        (Row.keyLess row next ∧ RowsWellFormedAdjacent schema (next :: rows))
        rowValid
        (@instDecidableAnd (Row.keyLess row next)
          (RowsWellFormedAdjacent schema (next :: rows)) ordered tail)
termination_by rows => rows.length

instance (schema : Schema) (rows : List Row) :
    Decidable (RowsWellFormedAdjacent schema rows) :=
  decideRowsWellFormedAdjacent schema rows

theorem Row.keyLess_trans {first second third : Row}
    (left : Row.keyLess first second) (right : Row.keyLess second third) :
    Row.keyLess first third := by
  exact Int.lt_trans left right

private theorem keyLess_all_of_cons {first second : Row} {rows : List Row}
    (head : Row.keyLess first second)
    (tail : (second :: rows).Pairwise Row.keyLess) :
    ∀ row ∈ second :: rows, Row.keyLess first row := by
  intro row member
  rcases List.pairwise_cons.mp tail with ⟨secondBefore, _⟩
  simp only [List.mem_cons] at member
  cases member with
  | inl equal => simpa [equal] using head
  | inr later =>
      exact Row.keyLess_trans head (secondBefore row later)

theorem rowsWellFormedAdjacent_iff (schema : Schema) (rows : List Row) :
    RowsWellFormedAdjacent schema rows ↔ RowsWellFormed schema rows := by
  induction rows with
  | nil => simp [RowsWellFormedAdjacent, RowsWellFormed]
  | cons row rows induction =>
      cases rows with
      | nil => simp [RowsWellFormedAdjacent, RowsWellFormed]
      | cons next rows =>
          constructor
          · intro adjacent
            rcases adjacent with ⟨rowValid, head, tailAdjacent⟩
            have tail := induction.mp tailAdjacent
            refine ⟨?_, ?_⟩
            · intro candidate member
              simp only [List.mem_cons] at member
              cases member with
              | inl equal => simpa [equal] using rowValid
              | inr later => exact tail.1 candidate (by simpa using later)
            · exact List.pairwise_cons.mpr
                ⟨keyLess_all_of_cons head tail.2, tail.2⟩
          · intro wellFormed
            rcases wellFormed with ⟨allValid, ordered⟩
            rcases List.pairwise_cons.mp ordered with ⟨rowBefore, tailOrdered⟩
            refine ⟨allValid row (by simp), rowBefore next (by simp), ?_⟩
            apply induction.mpr
            exact ⟨fun candidate member =>
              allValid candidate (by simp [member]), tailOrdered⟩

instance (schema : Schema) (rows : List Row) :
    Decidable (RowsWellFormed schema rows) :=
  decidable_of_iff (RowsWellFormedAdjacent schema rows)
    (rowsWellFormedAdjacent_iff schema rows)

def storedRows (tree : PersistentPageTree.Store Row) : List Row :=
  tree.root.erase.toList.map (fun entry => entry.2)

def RowTreeWellKeyed (tree : PersistentPageTree.Store Row) : Prop :=
  tree.Represents (treeEntries (storedRows tree))

end Core

end SQLeanite
