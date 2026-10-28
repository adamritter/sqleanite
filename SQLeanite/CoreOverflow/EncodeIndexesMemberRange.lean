import SQLeanite.CoreOverflow.ResolvePlansNextPage

namespace SQLeanite
namespace CoreOverflow
open FileFormat

theorem encodeIndexes_member_range : ∀ (nextPage : Nat)
    (indexes : List (Core.Table × Core.Index))
    (encodings : List IndexEncoding),
    encodeIndexes nextPage indexes = some encodings →
    ∀ encoding ∈ encodings,
      nextPage ≤ encoding.rootPage ∧
      encoding.rootPage + encoding.pages.length ≤
        nextPage + (indexPagesOf encodings).length
  | _, [], encodings, encoded => by
      simp only [encodeIndexes, Option.some.injEq] at encoded
      subst encodings
      simp
  | nextPage, indexed :: indexes, encodings, encoded => by
      simp only [encodeIndexes, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeIndex nextPage indexed.1 indexed.2 with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : encodeIndexes
            (nextPage + head.pages.length) indexes with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          intro encoding member
          simp only [List.mem_cons] at member
          have identity := encodeIndex_identity headResult
          simp only [indexPagesOf, List.flatMap_cons, List.length_append]
          rcases member with rfl | tailMember
          · constructor <;> omega
          · have range := encodeIndexes_member_range
                (nextPage + head.pages.length) indexes tail tailResult
                encoding tailMember
            simp only [indexPagesOf] at range
            constructor <;> omega

def indexEntriesOf (encodings : List IndexEncoding) : List CoreFile.CatalogEntry :=
  encodings.map IndexEncoding.catalogEntry

/-- Grouping wrapper for database reconstruction proofs. It preserves the
flat physical order but makes each table's contiguous index run explicit. -/
def encodeIndexTableGroups : Nat → List Core.Table →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let current ← encodeIndexes nextPage
        (table.indexes.map fun index => (table, index))
      let remaining ← encodeIndexTableGroups
        (nextPage + (indexPagesOf current).length) tables
      some (current ++ remaining)

theorem encodeIndexTableGroups_pairs : ∀ (nextPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups nextPage tables = some encodings →
    encodings.map (fun encoding => (encoding.table, encoding.index)) =
      tables.flatMap fun table => table.indexes.map fun index => (table, index)
  | _, [], encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.some.injEq] at encoded
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind]
        at encoded
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : encodeIndexTableGroups
            (nextPage + (indexPagesOf current).length) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult, Option.some.injEq] at encoded
          subst encodings
          simp only [List.map_append, List.flatMap_cons]
          rw [encodeIndexes_pairs nextPage _ current currentResult,
            encodeIndexTableGroups_pairs
              (nextPage + (indexPagesOf current).length) tables remaining
              remainingResult]

theorem encodeIndexTableGroups_tables {nextPage : Nat}
    {tables : List Core.Table} {encodings : List IndexEncoding}
    (encoded : encodeIndexTableGroups nextPage tables = some encodings) :
    ∀ encoding ∈ encodings, encoding.table ∈ tables := by
  have pairs := encodeIndexTableGroups_pairs nextPage tables encodings encoded
  intro encoding member
  have pairMember : (encoding.table, encoding.index) ∈
      encodings.map (fun candidate => (candidate.table, candidate.index)) :=
    List.mem_map_of_mem member
  rw [pairs] at pairMember
  simp only [List.mem_flatMap, List.mem_map] at pairMember
  rcases pairMember with ⟨table, tableMember, index, _, equal⟩
  injection equal with tableEqual
  simpa [tableEqual] using tableMember

theorem encodeIndexTableGroups_member_range : ∀ (nextPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups nextPage tables = some encodings →
    ∀ encoding ∈ encodings,
      nextPage ≤ encoding.rootPage ∧
      encoding.rootPage + encoding.pages.length ≤
        nextPage + (indexPagesOf encodings).length
  | _, [], encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.some.injEq] at encoded
      subst encodings
      simp
  | nextPage, table :: tables, encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind]
        at encoded
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : encodeIndexTableGroups
            (nextPage + (indexPagesOf current).length) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult, Option.some.injEq] at encoded
          subst encodings
          intro encoding member
          simp only [List.mem_append] at member
          simp only [indexPagesOf, List.flatMap_append, List.length_append]
          rcases member with currentMember | remainingMember
          · have range := encodeIndexes_member_range nextPage _ current
                currentResult encoding currentMember
            simp only [indexPagesOf] at range
            constructor <;> omega
          · have range := encodeIndexTableGroups_member_range
                (nextPage + (List.flatMap IndexEncoding.pages current).length)
                tables remaining remainingResult encoding remainingMember
            simp only [indexPagesOf] at range
            constructor <;> omega

end CoreOverflow

end SQLeanite
