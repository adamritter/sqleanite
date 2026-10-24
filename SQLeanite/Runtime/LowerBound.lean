import Std

namespace SQLeanite.Runtime.LowerBound

/-- SQLite-style interval halving. `count` is a conservative termination
budget; the interval shrinks by half at each nonterminal step. -/
def search (p : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if p mid then search p fuel lo mid
        else search p fuel (mid + 1) hi
      else lo

theorem search_partition (p : Nat → Bool) (size : Nat)
    (mono : ∀ i j, i ≤ j → j < size → p i = true → p j = true)
    (fuel lo hi : Nat) (bounds : lo ≤ hi ∧ hi ≤ size)
    (enough : hi - lo ≤ fuel)
    (below : ∀ i, i < lo → p i = false)
    (above : ∀ i, hi ≤ i → i < size → p i = true) :
    lo ≤ search p fuel lo hi ∧ search p fuel lo hi ≤ hi ∧
      (∀ i, i < search p fuel lo hi → p i = false) ∧
      (∀ i, search p fuel lo hi ≤ i → i < size → p i = true) := by
  induction fuel generalizing lo hi with
  | zero =>
      have eq : lo = hi := by omega
      simp only [search]
      exact ⟨by omega, by omega, below, by simpa [eq] using above⟩
  | succ fuel ih =>
      simp only [search]
      split
      next nonempty =>
        let mid := (lo + hi) / 2
        have midBounds : lo ≤ mid ∧ mid < hi := by dsimp [mid]; omega
        split
        next hit =>
          have h := ih lo mid ⟨midBounds.1, by omega⟩ (by omega) below
            (fun i hmi his => mono mid i hmi his hit)
          exact ⟨h.1, Nat.le_trans h.2.1 (by omega), h.2.2⟩
        next miss =>
          have lower : ∀ i, i < mid + 1 → p i = false := by
            intro i hi
            cases hp : p i with
            | false => rfl
            | true =>
                have hm := mono i mid (by omega) (by omega) hp
                exact False.elim (miss hm)
          have h := ih (mid + 1) hi ⟨by omega, bounds.2⟩ (by omega) lower above
          exact ⟨Nat.le_trans (by omega) h.1, h.2⟩
      next empty =>
        have eq : lo = hi := by omega
        exact ⟨by omega, by omega, below, by simpa [eq] using above⟩

/-- Exact agreement with the first matching index of a linear scan. The
monotonicity premise must come from the checked page view, not a file stamp. -/
theorem search_eq_findIdx (p : Nat → Bool) (size : Nat)
    (mono : ∀ i j, i ≤ j → j < size → p i = true → p j = true) :
    search p size 0 size = (List.range size).findIdx p := by
  have h := search_partition p size mono size 0 size ⟨by omega, by omega⟩
    (by omega) (by intro i hi; omega) (by intro i hi hn; omega)
  let result := search p size 0 size
  by_cases inside : result < size
  · symm
    apply (List.findIdx_eq (by simpa using inside)).mpr
    constructor
    · simpa using h.2.2.2 result (by omega) inside
    · intro j hj
      simpa using h.2.2.1 j hj
  · have eq : result = size := by dsimp [result] at *; omega
    change result = _
    rw [eq]
    symm
    have nohit : ∀ i ∈ List.range size, p i = false := by
      intro i hi
      apply h.2.2.1 i
      have his : i < size := List.mem_range.mp hi
      change i < result
      omega
    simpa using List.findIdx_eq_length_of_false nohit

end SQLeanite.Runtime.LowerBound

namespace SQLeanite.Runtime.CheckedOrder

/-- Linear-time validation of the neighboring keys of a physical page. -/
def adjacent (key : Nat → Int) : Nat → Nat → Bool
  | 0, _ => true
  | count + 1, start =>
      decide (key start ≤ key (start + 1)) && adjacent key count (start + 1)

theorem adjacent_spec (key : Nat → Int) (count start : Nat)
    (checked : adjacent key count start = true) :
    ∀ i, start ≤ i → i < start + count → key i ≤ key (i + 1) := by
  induction count generalizing start with
  | zero => intro i lo hi; omega
  | succ count ih =>
      simp only [adjacent, Bool.and_eq_true, decide_eq_true_eq] at checked
      intro i lo hi
      by_cases eq : i = start
      · simpa [eq] using checked.1
      · exact ih (start + 1) checked.2 i (by omega) (by omega)

/-- The binary-search premise follows from an executed O(n) adjacency check. -/
theorem monotone_of_checked (key : Nat → Int) (size : Nat)
    (checked : adjacent key (size - 1) 0 = true) :
    ∀ i j, i ≤ j → j < size → key i ≤ key j := by
  have adj := adjacent_spec key (size - 1) 0 checked
  intro i j ij js
  have chain : ∀ d, i + d < size → key i ≤ key (i + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
        intro bound
        have prior := ih (by omega)
        have step := adj (i + d) (by omega) (by omega)
        simpa [Nat.add_assoc] using Int.le_trans prior step
  have result := chain (j - i) (by omega)
  simpa [Nat.add_sub_of_le ij] using result

end SQLeanite.Runtime.CheckedOrder
