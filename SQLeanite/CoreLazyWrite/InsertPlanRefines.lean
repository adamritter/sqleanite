import SQLeanite.CoreLazyWrite.TreeDisjoint

namespace SQLeanite
namespace CoreLazyWrite

/-- **The top-level refinement.** The plan the executable computes, applied to the
file, denotes exactly the table with the row inserted -- which is what
`Core.execute` produces for that `INSERT`.

This is the statement `executeInsert?` must be gated on before the page-local path
may be reachable from a shipped build. -/
theorem insertPlan_refines (schema : Core.Schema)
    (source : CoreDecode.PageSource) (rootPage : Nat) (row : Core.Row)
    (leafPage : Nat) (encoded : CoreFile.Page) (rows : List Core.Row)
    (wellFormed : WellFormedTree schema source (source.pageCount + 1) rootPage)
    (decoded : CoreDecode.decodeSubtreeRowsFrom schema source
      (source.pageCount + 1) rootPage = some rows)
    (rowsEncodable : ∀ candidate ∈ rows,
      candidate.WellFormed schema ∧ CoreOverflow.RowInline schema candidate)
    (rowEncodable : row.WellFormed schema ∧ CoreOverflow.RowInline schema row)
    (planned : insertPlan? schema source rootPage row = some (leafPage, encoded)) :
    CoreDecode.decodeSubtreeRowsFrom schema
        (CorePageSource.write source ⟨leafPage - 1, encoded.storage⟩)
        (source.pageCount + 1) rootPage
      = some (Core.orderedUpsert row rows) := by
  rw [insertPlan?] at planned
  split at planned
  · exact absurd planned (by simp)
  rename_i planLeaf locatedPlan
  split at planned
  · exact absurd planned (by simp)
  rename_i oldLeaf oldRead
  split at planned
  · exact absurd planned (by simp)
  rename_i leafRows leafDecoded
  split at planned
  · exact absurd planned (by simp)
  split at planned
  · exact absurd planned (by simp)
  rename_i encodedPage encodedResult
  obtain ⟨targetEq, encodedEq⟩ : planLeaf = leafPage ∧ encodedPage = encoded := by
    have injected := Option.some.inj planned
    exact ⟨congrArg Prod.fst injected, congrArg Prod.snd injected⟩
  subst targetEq
  subst encodedEq
  -- The written page is a real page of the file, which fixes the renumbering.
  have leafPos : 0 < planLeaf := by
    rcases Nat.eq_zero_or_pos planLeaf with zero | positive
    · rw [zero, wellFormed.bounded 0 (Or.inl rfl)] at oldRead
      exact absurd oldRead (by simp)
    · exact positive
  have leafLe : planLeaf ≤ source.pageCount := by
    rcases Nat.lt_or_ge source.pageCount planLeaf with beyond | within
    · rw [wellFormed.bounded planLeaf (Or.inr beyond)] at oldRead
      exact absurd oldRead (by simp)
    · exact within
  have countEq : max source.pageCount (planLeaf - 1 + 1) = source.pageCount := by omega
  -- Inline leaves decode the same from either source, which is the frame premise.
  have leafAgrees : ∀ p bytes, source.readPage p = some bytes →
      CoreDecode.decodeRowsFrom schema source bytes
        = CoreDecode.decodeRowsFrom schema
            (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩) bytes := by
    intro p bytes read
    exact decodeRowsFrom_congr schema source _ bytes (wellFormed.inline p bytes read)
      (LeafInline_congr schema source _ bytes (wellFormed.inline p bytes read))
  have offTarget : ∀ p, p ≠ planLeaf → source.readPage p
      = (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩).readPage p := by
    intro p notTarget
    simp only [CorePageSource.write, countEq]
    by_cases zero : p = 0
    · simp [zero, wellFormed.bounded 0 (Or.inl rfl)]
    by_cases beyond : source.pageCount < p
    · simp [zero, beyond, wellFormed.bounded p (Or.inr beyond)]
    · have notWritten : ¬ (p = planLeaf - 1 + 1) := by omega
      simp [zero, beyond, notWritten]
  have newRead :
      (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩).readPage planLeaf
        = some encodedPage.bytes := by
    simp only [CorePageSource.write, countEq]
    have notZero : ¬ (planLeaf = 0) := by omega
    have notBeyond : ¬ (source.pageCount < planLeaf) := by omega
    have isWritten : planLeaf = planLeaf - 1 + 1 := by omega
    simp [notZero, notBeyond, ← isWritten, CoreFile.Page.storage]
  -- The leaf's rows are a segment of the table's, so they inherit encodability.
  rcases locateLeaf_routedSplit schema source row.treeKey row rfl
      (source.pageCount + 1) rootPage planLeaf rows wellFormed.separators decoded
      locatedPlan with ⟨routed⟩
  have leafSubset : ∀ candidate ∈ leafRows, candidate ∈ rows := by
    intro candidate member
    have leafEq : routed.leafRows = leafRows :=
      Option.some.inj ((routed.leafDecodes oldLeaf oldRead).symm.trans leafDecoded)
    rw [routed.decomposition, leafEq]
    exact List.mem_append_left _ (List.mem_append_right _ member)
  have newRowsEncodable : ∀ candidate ∈ Core.orderedUpsert row leafRows,
      candidate.WellFormed schema ∧ CoreOverflow.RowInline schema candidate := by
    intro candidate member
    rcases mem_orderedUpsert row leafRows candidate member with isRow | inLeaf
    · rw [isRow]; exact rowEncodable
    · exact rowsEncodable candidate (leafSubset candidate inLeaf)
  have chunkEncoded : CorePageCodec.encodeChunkLeaf schema
      [(0, Core.orderedUpsert row leafRows)] = some encodedPage := encodedResult
  have newIsLeaf : CoreDecode.interiorChildren? encodedPage.bytes = none :=
    CorePageCodec.interiorChildren_encodeChunkLeaf schema _ encodedPage chunkEncoded
  have newDecoded : CoreDecode.decodeRowsFrom schema
      (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩) encodedPage.bytes
        = some (Core.orderedUpsert row leafRows) := by
    have inverse := CoreWidePageInverse.decodeRowsFrom_encodeChunkLeaf schema
      [(0, Core.orderedUpsert row leafRows)] encodedPage
      (by
        intro entry entryMem candidate candidateMem
        simp only [List.mem_singleton] at entryMem
        subst entryMem
        exact (newRowsEncodable candidate candidateMem).1)
      (by
        intro entry entryMem candidate candidateMem
        simp only [List.mem_singleton] at entryMem
        subst entryMem
        exact (newRowsEncodable candidate candidateMem).2)
      chunkEncoded
      (CorePageSource.write source ⟨planLeaf - 1, encodedPage.storage⟩)
    simpa using inverse
  exact locateLeaf_write_refines schema source _ row.treeKey row rfl planLeaf leafRows
    leafAgrees offTarget
    (fun candidate read => by
      rw [oldRead] at read
      rw [← Option.some.inj read]
      exact leafDecoded)
    encodedPage.bytes newRead newIsLeaf newDecoded
    (source.pageCount + 1) rootPage rows wellFormed.pages wellFormed.separators
    wellFormed.disjoint wellFormed.enumerated decoded locatedPlan

end CoreLazyWrite

end SQLeanite
