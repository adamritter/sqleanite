import SQLeanite.CoreDistinct
import SQLeanite.PhysicalQuery
import SQLeanite.Syntax
import SQLeanite.RelationalAlgebra

/-! SQL set operations use BINARY numeric equality and retain original values.
The older optimizer algebra operates on representation-equal tuples; its
proofs remain useful for that algebra but are not the SQL equality contract. -/
namespace SQLeanite.CoreCompound

open Core

/-- Ascending SQL comparison order used by the pinned compound merge. -/
def rowCompare := PhysicalQuery.compareValues

def ordered (rows : List (List Core.Value)) : List (List Core.Value) :=
  rows.mergeSort (fun a b => rowCompare a b != .gt)

/-- The pinned SQLite compound merge retains the first row in each input.
On UNION ties its right arm wins; `inputRows` makes that choice explicit. -/
def representatives (rows : List (List Core.Value)) : List (List Core.Value) :=
  stableDistinctBy distinctRowKey rows

def inputRows (op : CompoundOp) (left right : List (List Core.Value)) : List (List Core.Value) :=
  match op with
  | .unionAll => left ++ right
  | .unionDistinct => right ++ left
  | .intersect => left.filter (fun row => distinctRowKey row ∈ right.map distinctRowKey)
  | .except => left.filter (fun row => distinctRowKey row ∉ right.map distinctRowKey)

def combine (op : CompoundOp) (left right : List (List Core.Value)) : List (List Core.Value) :=
  if op = .unionAll then left ++ right
  else ordered (representatives (inputRows op left right))

theorem mem_representatives_keys (rows : List (List Core.Value)) (key : List Core.Value) :
    key ∈ (representatives rows).map distinctRowKey ↔ key ∈ rows.map distinctRowKey :=
  mem_keys_stableDistinctBy distinctRowKey rows key

theorem representatives_subset (rows : List (List Core.Value)) :
    representatives rows ⊆ rows := stableDistinctBy_subset distinctRowKey rows

theorem representatives_keys_nodup (rows : List (List Core.Value)) :
    ((representatives rows).map distinctRowKey).Nodup :=
  stableDistinctBy_key_nodup distinctRowKey rows

theorem inputRows_subset (op : CompoundOp) (left right : List (List Core.Value)) :
    inputRows op left right ⊆ left ++ right := by
  intro row member
  cases op with
  | unionAll => exact member
  | unionDistinct => simpa only [inputRows, List.mem_append, or_comm] using member
  | intersect | except =>
      exact List.mem_append_left _ (List.mem_filter.mp member).1

theorem combine_subset (op : CompoundOp) (left right : List (List Core.Value)) :
    combine op left right ⊆ left ++ right := by
  intro row member
  unfold combine at member
  split at member
  · exact member
  · have kept := (List.mergeSort_perm _ _).mem_iff.mp member
    exact inputRows_subset _ _ _ (representatives_subset _ kept)

theorem inputRows_keys (op : CompoundOp) (left right : List (List Core.Value)) (key : List Core.Value) :
    key ∈ (inputRows op left right).map distinctRowKey ↔
      match op with
      | .unionAll | .unionDistinct => key ∈ left.map distinctRowKey ∨ key ∈ right.map distinctRowKey
      | .intersect => key ∈ left.map distinctRowKey ∧ key ∈ right.map distinctRowKey
      | .except => key ∈ left.map distinctRowKey ∧ key ∉ right.map distinctRowKey := by
  cases op <;> simp only [inputRows, List.map_append, List.mem_append, or_comm]
  all_goals
    simp only [List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨row, ⟨member, predicate⟩, equal⟩
      subst key
      exact ⟨⟨row, member, rfl⟩, by simpa only [decide_eq_true_eq] using predicate⟩
    · rintro ⟨⟨row, member, equal⟩, predicate⟩
      subst key
      exact ⟨row, ⟨member, by simpa only [decide_eq_true_eq] using predicate⟩, rfl⟩

theorem combine_keys (op : CompoundOp) (left right : List (List Core.Value)) (key : List Core.Value) :
    key ∈ (combine op left right).map distinctRowKey ↔
      match op with
      | .unionAll | .unionDistinct => key ∈ left.map distinctRowKey ∨ key ∈ right.map distinctRowKey
      | .intersect => key ∈ left.map distinctRowKey ∧ key ∈ right.map distinctRowKey
      | .except => key ∈ left.map distinctRowKey ∧ key ∉ right.map distinctRowKey := by
  unfold combine
  split
  · next all => subst op; simp
  · unfold ordered
    rw [((List.mergeSort_perm _ _).map distinctRowKey).mem_iff,
      mem_representatives_keys]
    exact inputRows_keys op left right key

theorem combine_keys_nodup (op : CompoundOp) (left right : List (List Core.Value))
    (notAll : op ≠ .unionAll) : ((combine op left right).map distinctRowKey).Nodup := by
  simp only [combine, notAll, ↓reduceIte]
  exact ((List.mergeSort_perm _ _).map distinctRowKey).nodup_iff.mpr
    (representatives_keys_nodup _)

/-- Multiplicity denotation over SQL comparison keys. UNION ALL preserves
counts; the other operations are ordinary sets of SQL-equivalent tuples. -/
def denotation (op : CompoundOp) (left right : KRelation.Relation (List Core.Value)) :
    KRelation.Relation (List Core.Value) :=
  match op with
  | .unionAll => KRelation.unionAll left right
  | .unionDistinct => KRelation.distinct (KRelation.unionAll left right)
  | .intersect => KRelation.intersect (KRelation.distinct left) (KRelation.distinct right)
  | .except => KRelation.except (KRelation.distinct left) (KRelation.distinct right)

private theorem multiplicity_nodup {α : Type} [DecidableEq α] (rows : List α)
    (nodup : rows.Nodup) (target : α) :
    RelationalAlgebra.listMultiplicity target rows = if target ∈ rows then 1 else 0 := by
  rw [RelationalAlgebra.listMultiplicity_eq_count, List.Nodup.count nodup]

theorem combine_denotes (op : CompoundOp) (left right : List (List Core.Value)) :
    RelationalAlgebra.ofList ((combine op left right).map distinctRowKey) =
      denotation op (RelationalAlgebra.ofList (left.map distinctRowKey))
        (RelationalAlgebra.ofList (right.map distinctRowKey)) := by
  by_cases all : op = .unionAll
  · subst op
    simp only [combine, ↓reduceIte, List.map_append, denotation]
    exact RelationalAlgebra.ofList_append _ _
  · funext key
    simp only [RelationalAlgebra.ofList]
    rw [multiplicity_nodup _ (combine_keys_nodup op left right all)]
    have leftZero := RelationalAlgebra.listMultiplicity_eq_zero_iff key (left.map distinctRowKey)
    have rightZero := RelationalAlgebra.listMultiplicity_eq_zero_iff key (right.map distinctRowKey)
    cases op <;> simp only [denotation, KRelation.unionAll, KRelation.distinct,
      KRelation.intersect, KRelation.except, RelationalAlgebra.ofList,
      Nat.add_eq_zero_iff, leftZero, rightZero]
    · exact (all rfl).elim
    all_goals
      by_cases inLeft : key ∈ left.map distinctRowKey <;>
      by_cases inRight : key ∈ right.map distinctRowKey <;>
      simp only [combine_keys, inLeft, inRight, not_true_eq_false, not_false_eq_true,
        and_self, true_or, false_or, true_and, false_and, ↓reduceIte, Nat.min_self,
        Nat.zero_sub, Nat.sub_self, Nat.sub_zero, Nat.min_zero, Nat.zero_min]

end SQLeanite.CoreCompound
