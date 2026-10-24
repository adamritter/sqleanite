import SQLeanite.Core
import SQLeanite.Binary64

namespace SQLeanite.Core

/-- Comparison-only key for BINARY DISTINCT. Integral REALs in the signed-64
range share their INTEGER key; signed zeros therefore share zero. This uses
exact binary64 significands and powers of two, never a rounded Float cast.
The original value (including its storage class) remains the output. -/
def distinctValueKey : Value → Value
  | original@(.realBits bits) => Id.run do
      let exponent := Binary64.exponent bits
      if exponent == 2047 then return original
      let significand := if exponent = 0 then Binary64.fraction bits
        else Binary64.fractionModulus + Binary64.fraction bits
      let effective := if exponent = 0 then 1 else exponent
      let magnitude ← if effective ≥ 1075 then
          pure (significand * 2 ^ (effective - 1075))
        else do
          let denominator := 2 ^ (1075 - effective)
          if significand % denominator != 0 then return original
          pure (significand / denominator)
      let integer := if Binary64.sign bits then -(Int.ofNat magnitude) else Int.ofNat magnitude
      if lower : -(Int.ofNat FileFormat.IntegerWidth.eight.midpoint) ≤ integer then
        if upper : integer < Int.ofNat FileFormat.IntegerWidth.eight.midpoint then
          return .integer ⟨integer, lower, upper⟩
        else return original
      else return original
  | value => value

def distinctRowKey (row : List Value) : List Value := row.map distinctValueKey

/-- First representatives of equal keys, in input order. Keys affect only
membership; every emitted row is an unchanged input row. -/
def stableDistinctBy [DecidableEq κ] (key : α → κ) : List α → List α
  | [] => []
  | row :: rows => row :: (stableDistinctBy key rows).filter (fun next => key next != key row)

theorem mem_stableDistinctBy [DecidableEq κ] (key : α → κ) (rows : List α) (row : α) :
    row ∈ stableDistinctBy key rows ↔
      rows.find? (fun candidate => decide (key candidate = key row)) = some row := by
  induction rows with
  | nil => simp [stableDistinctBy]
  | cons head tail ih =>
      by_cases equal : key head = key row
      · simp [stableDistinctBy, equal, List.mem_filter, ih, eq_comm]
      · have different : row ≠ head := by intro h; exact equal (h ▸ rfl)
        simp [stableDistinctBy, equal, List.mem_filter, ih,
          Ne.symm equal, different]

theorem stableDistinctBy_subset [DecidableEq κ] (key : α → κ) (rows : List α) :
    stableDistinctBy key rows ⊆ rows := by
  intro row member
  exact List.mem_of_find?_eq_some ((mem_stableDistinctBy key rows row).mp member)

/-- Every input key still has an original representative. -/
theorem stableDistinctBy_coverage [DecidableEq κ] (key : α → κ) (rows : List α)
    (row : α) (member : row ∈ rows) :
    ∃ chosen ∈ stableDistinctBy key rows, key chosen = key row := by
  induction rows with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with equal | inTail
      · subst row; exact ⟨head, by simp [stableDistinctBy], rfl⟩
      · obtain ⟨chosen, kept, equal⟩ := ih inTail
        by_cases same : key chosen = key head
        · exact ⟨head, by simp [stableDistinctBy], same.symm.trans equal⟩
        · exact ⟨chosen, by simp [stableDistinctBy, kept, same], equal⟩

theorem mem_keys_stableDistinctBy [DecidableEq κ] (key : α → κ)
    (rows : List α) (target : κ) :
    target ∈ (stableDistinctBy key rows).map key ↔ target ∈ rows.map key := by
  constructor
  · rintro member
    obtain ⟨row, kept, equal⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨row, stableDistinctBy_subset key rows kept, equal⟩
  · rintro member
    obtain ⟨row, original, equal⟩ := List.mem_map.mp member
    obtain ⟨chosen, kept, same⟩ := stableDistinctBy_coverage key rows row original
    exact List.mem_map.mpr ⟨chosen, kept, same.trans equal⟩

theorem stableDistinctBy_key_nodup [DecidableEq κ] (key : α → κ) (rows : List α) :
    ((stableDistinctBy key rows).map key).Nodup := by
  induction rows with
  | nil => simp [stableDistinctBy]
  | cons head tail ih =>
      simp only [stableDistinctBy, List.map_cons, List.nodup_cons]
      constructor
      · simp only [List.mem_map, List.mem_filter]
        rintro ⟨row, ⟨_, different⟩, equal⟩
        simp [equal] at different
      · exact (List.filter_sublist).map key |>.nodup ih

theorem stableDistinctBy_nodup [DecidableEq κ] (key : α → κ) (rows : List α) :
    (stableDistinctBy key rows).Nodup :=
  List.Pairwise.of_map key (fun _ _ h equal => h (congrArg key equal)) (stableDistinctBy_key_nodup key rows)

theorem stableDistinctBy_map [DecidableEq κ] [DecidableEq ι]
    (key : α → κ) (other : β → ι) (f : α → β)
    (preserves : ∀ a b, other (f a) = other (f b) ↔ key a = key b) (rows : List α) :
    stableDistinctBy other (rows.map f) = (stableDistinctBy key rows).map f := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, stableDistinctBy, ih]
      rw [List.filter_map]
      congr 2
      apply List.filter_congr
      intro row _
      apply Bool.eq_iff_iff.mpr
      simp [preserves]

end SQLeanite.Core
