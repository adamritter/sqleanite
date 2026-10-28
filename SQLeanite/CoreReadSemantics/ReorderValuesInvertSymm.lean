import SQLeanite.CoreReadSemantics.CoreRow

namespace SQLeanite
namespace CoreReadSemantics
open QuerySemantics

theorem reorderValues_invert_symm {positions : List Nat}
    (perm : positions.Perm (List.range positions.length))
    (values : List Core.Value) :
    reorderValues positions (reorderValues (invertPositions positions) values) =
      values := by
  by_cases width : values.length = positions.length
  · have nodup : positions.Nodup := perm.nodup_iff.mpr (List.nodup_range)
    have innerWidth : values.length = (invertPositions positions).length := by
      rw [invertPositions_length]; exact width
    have innerLength :=
      reorderValues_length_of_width (positions := invertPositions positions)
        (values := values) innerWidth
    have outerWidth :
        (reorderValues (invertPositions positions) values).length =
          positions.length := by
      rw [innerLength, invertPositions_length]
    apply List.ext_getElem?
    intro index
    by_cases bounded : index < positions.length
    · have slotFound : positions[index]? = some positions[index] :=
        List.getElem?_eq_getElem bounded
      have slotBounded : positions[index] < positions.length :=
        lt_of_mem_positions perm (List.getElem_mem bounded)
      have inner := reorderValues_getElem?
        (positions := invertPositions positions) (values := values) innerWidth
        (invertPositions_getElem? slotBounded)
      rw [reorderValues_getElem? (positions := positions)
        (values := reorderValues (invertPositions positions) values)
        outerWidth slotFound]
      rw [valueAt, inner]
      have recovered : positions.idxOf positions[index] = index :=
        idxOf_eq_of_getElem? nodup slotFound
      rw [recovered, valueAt]
      have : index < values.length := by rw [width]; exact bounded
      rw [List.getElem?_eq_getElem this]
      rfl
    · have beyondLeft :
          (reorderValues positions
            (reorderValues (invertPositions positions) values))[index]? = none := by
        apply List.getElem?_eq_none
        rw [reorderValues_length_of_width (positions := positions)
          (values := reorderValues (invertPositions positions) values) outerWidth]
        omega
      have beyondRight : values[index]? = none := by
        apply List.getElem?_eq_none
        rw [width]
        omega
      rw [beyondLeft, beyondRight]
  · have identity : reorderValues (invertPositions positions) values = values := by
      rw [reorderValues, if_neg (by rw [invertPositions_length]; exact width)]
    rw [identity, reorderValues, if_neg width]

theorem distinctRowKey_reorder (positions : List Nat) (values : List Core.Value) :
    Core.distinctRowKey (reorderValues positions values) =
      reorderValues positions (Core.distinctRowKey values) := by
  have lookupKey (index : Nat) :
      valueAt (Core.distinctRowKey values) index = Core.distinctValueKey (valueAt values index) := by
    cases found : values[index]? <;>
      simp [Core.distinctRowKey, valueAt, List.getElem?_map, found, Core.distinctValueKey]
  by_cases width : values.length = positions.length
  · simp only [Core.distinctRowKey, reorderValues, List.length_map, width, if_true, List.map_map]
    apply List.map_congr_left
    intro index _
    exact (lookupKey index).symm
  · simp [Core.distinctRowKey, reorderValues, width]

/-- A permutation of `range columns.length` is a permutation of
`range positions.length`, because permutations preserve length.  Stated
separately so the bijection below can be built from the permutation a caller
naturally has: one against the *source* column list. -/
private theorem perm_range_self {positions columns : List Nat}
    (perm : positions.Perm (List.range columns.length)) :
    positions.Perm (List.range positions.length) := by
  have lengths : positions.length = columns.length := by
    simpa using perm.length_eq
  rw [lengths]
  exact perm

/-- A column permutation of the live projection, as an algebra `Bijection` on
output tuples. -/
def columnBijection {positions columns : List Nat}
    (perm : positions.Perm (List.range columns.length)) :
    RelationalAlgebra.Bijection (List Core.Value) (List Core.Value) where
  forward := reorderValues positions
  backward := reorderValues (invertPositions positions)
  leftInverse := reorderValues_invert (perm_range_self perm)
  rightInverse := reorderValues_invert_symm (perm_range_self perm)

theorem columnBijection_forward {positions columns : List Nat}
    (perm : positions.Perm (List.range columns.length)) :
    (columnBijection perm).forward = reorderValues positions := rfl

/-- The permuted column list projects to the reordered tuple. This is the step
that ties a *syntactic* column reordering to the tuple-level permutation. -/
theorem permutedColumns_map_value {columns positions : List Nat}
    (perm : positions.Perm (List.range columns.length))
    (row : Core.Row) :
    (positions.map (fun index => columns.getD index 0)).map row.value =
      reorderValues positions (columns.map row.value) := by
  have lengths : positions.length = columns.length := by
    have := perm.length_eq
    simpa using this
  have width : (columns.map row.value).length = positions.length := by
    rw [List.length_map, lengths]
  rw [reorderValues, if_pos width, List.map_map]
  apply List.map_congr_left
  intro index member
  have bounded : index < columns.length := by
    have inRange : index ∈ List.range columns.length := perm.mem_iff.mp member
    simpa using inRange
  have found : columns[index]? = some columns[index] :=
    List.getElem?_eq_getElem bounded
  have projected : (columns.map row.value)[index]? =
      some (row.value columns[index]) := by
    rw [List.getElem?_map, found]
    rfl
  show row.value (columns.getD index 0) = valueAt (columns.map row.value) index
  rw [valueAt, projected, List.getD_eq_getElem?_getD, found]
  rfl

/-- **POPL'10 permutation parity, reached from the live executor.**

Permuting a live query's column list denotes exactly `RelationalAlgebra.permute`
of the unpermuted query's denotation. Both `DISTINCT` and non-`DISTINCT` queries
are covered: duplicate elimination commutes with a bijective relabelling.

This is the theorem that upgrades "the algebra module has a permutation
operator" to "the projection the shipped read path performs *is* that operator".
-/
theorem permuted_projection_denotes (query : Core.Query) {positions : List Nat}
    (perm : positions.Perm (List.range query.columns.length))
    (rows : List Core.Row) :
    queryDenotation
        { query with
          columns := positions.map (fun index => query.columns.getD index 0) }
        rows =
      RelationalAlgebra.eval
        (RelationalAlgebra.permute (columnBijection perm)
          (.relation (queryDenotation query rows))) := by
  rw [← query_eval_denotes, ← query_eval_denotes]
  have projected :
      Core.Query.projectedRows
          { query with
            columns := positions.map (fun index => query.columns.getD index 0) }
          rows =
        (query.projectedRows rows).map (reorderValues positions) := by
    unfold Core.Query.projectedRows Core.Query.selectedRows
    rw [List.map_map]
    apply List.map_congr_left
    intro row _
    simpa [Function.comp_def] using permutedColumns_map_value perm row
  -- The permuted query differs from the original in `columns` only, so the two
  -- `distinct` flags and the two selected-row lists are literally the same.
  have samePermuted :
      Core.Query.eval
          { query with
            columns := positions.map (fun index => query.columns.getD index 0) }
          rows =
        if query.distinct then
          Core.limitRows query.limit (Core.stableDistinctBy Core.distinctRowKey ((query.projectedRows rows).map
            (reorderValues positions)))
        else (query.projectedRows rows).map (reorderValues positions) := by
    unfold Core.Query.eval
    rw [projected]
  rw [samePermuted, Core.Query.eval]
  cases flag : query.distinct with
  | true =>
      simp only [flag, if_true]
      have injective : Function.Injective (columnBijection perm).forward := by
        intro a b equal
        have recovered := congrArg (columnBijection perm).backward equal
        simpa only [(columnBijection perm).leftInverse] using recovered
      have preserves (a b : List Core.Value) :
          Core.distinctRowKey ((columnBijection perm).forward a) =
            Core.distinctRowKey ((columnBijection perm).forward b) ↔
          Core.distinctRowKey a = Core.distinctRowKey b := by
        simp only [columnBijection_forward, distinctRowKey_reorder]
        exact injective.eq_iff
      rw [← columnBijection_forward perm,
        Core.stableDistinctBy_map _ _ _ preserves, Core.limitRows_map]
      exact RelationalAlgebra.ofList_map_permute (columnBijection perm)
        (Core.limitRows query.limit (Core.stableDistinctBy Core.distinctRowKey (query.projectedRows rows)))
  | false =>
      simp only [flag, if_false, Bool.false_eq_true]
      rw [← columnBijection_forward perm]
      exact RelationalAlgebra.ofList_map_permute (columnBijection perm)
        (query.projectedRows rows)

end CoreReadSemantics

end SQLeanite
