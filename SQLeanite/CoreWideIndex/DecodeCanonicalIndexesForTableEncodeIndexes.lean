import SQLeanite.CoreDecode.ValidateCanonicalIndexGroupsFromEncodeOverflowIndexTableGroups
import SQLeanite.CoreWideIndex.IndexRowsInline

namespace SQLeanite
namespace CoreWideIndex

theorem decodeCanonicalIndexesForTable_encodeIndexes
    (table : Core.Table) : ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List IndexEncoding)
      (suffix : List CoreDecode.CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      encodeIndexes nextPage
          (indexes.map fun index => (table, index)) = some encodings →
      CoreDecode.decodeCanonicalIndexesForTable table.schema table.schema.name
        (encodings.map (fun encoding =>
          CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (indexes, suffix)
  | _, [], encodings, suffix, _, boundary, encoded => by
      simp only [List.map_nil, encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold CoreDecode.decodeCanonicalIndexesForTable
          exact dif_neg (boundary entry (by simp))
  | nextPage, index :: indexes, encodings, suffix, members, boundary,
      encoded => by
      simp only [List.map_cons, encodeIndexes, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeIndex nextPage table index with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeIndexes head.nextPage
              (indexes.map fun candidate => (table, candidate)) with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encodings
              simp only [List.map_cons, List.cons_append]
              unfold CoreDecode.decodeCanonicalIndexesForTable
              have identity := encodeIndex_identity headResult
              have sameTable :
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry).table =
                    table.schema.name := by
                simp [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded, identity.2.1]
              rw [dif_pos sameTable]
              have decoded : CoreDecode.decodeCanonicalIndex table.schema
                  table.schema.name
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry) =
                    some index := by
                simpa [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded, identity.2.1,
                  identity.2.2] using
                    (CoreDecode.decodeCanonicalIndex_encoded table index
                      (members index (by simp)) head.rootPage)
              rw [decoded]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [decodeCanonicalIndexesForTable_encodeIndexes table
                head.nextPage indexes tail suffix
                (fun candidate member => members candidate (by simp [member]))
                boundary tailResult]

theorem restoreCanonicalIndexes_encodeIndexTableGroups :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List IndexEncoding)
      (suffix : List CoreDecode.CatalogEntry),
      Core.TablesWellFormed tables →
      (∀ entry ∈ suffix, ∀ table ∈ tables,
        entry.table ≠ table.schema.name) →
      encodeIndexTableGroups nextPage tables = some encodings →
      CoreDecode.restoreCanonicalIndexes
          (tables.map Core.Table.withoutIndexes)
          (encodings.map (fun encoding =>
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
        some (tables.map Core.Table.canonicalize, suffix)
  | _, [], encodings, suffix, _, _, encoded => by
      simp only [encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, suffix, wellFormed, boundary,
      encoded => by
      simp only [Core.TablesWellFormed, Core.namesUnique, List.map_cons,
        List.pairwise_cons] at wellFormed
      rcases wellFormed with ⟨headDistinct, tailWellFormed⟩
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
              simp only [List.map_cons, List.map_append, List.append_assoc]
              unfold CoreDecode.restoreCanonicalIndexes
              have remainingBelongs := encodeIndexTableGroups_tables
                remainingResult
              have currentBoundary : ∀ entry ∈
                  (remaining.map (fun encoding =>
                    CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++
                      suffix),
                  entry.table ≠ table.schema.name := by
                intro entry member
                simp only [List.mem_append] at member
                rcases member with encodedMember | suffixMember
                · rcases List.mem_map.mp encodedMember with
                    ⟨encoding, encodingMember, equal⟩
                  subst entry
                  have tableMember := remainingBelongs encoding encodingMember
                  have distinct := headDistinct encoding.table.schema.name
                    (List.mem_map_of_mem tableMember)
                  simpa [IndexEncoding.catalogEntry,
                    CoreDecode.CatalogEntry.ofEncoded] using distinct.symm
                · exact boundary entry suffixMember table (by simp)
              simp only [Core.Table.withoutIndexes_schema,
                Core.Table.withoutIndexes_rows, Core.Table.withoutIndexes_catalogSource]
              rw [decodeCanonicalIndexesForTable_encodeIndexes table nextPage
                table.indexes current
                (remaining.map (fun encoding =>
                  CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++
                    suffix)
                (by simp) currentBoundary currentResult]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [Core.Table.rebuild_self]
              simp only [Except.toOption]
              have tailBoundary : ∀ entry ∈ suffix,
                  ∀ candidate ∈ tables,
                    entry.table ≠ candidate.schema.name := by
                intro entry entryMember candidate candidateMember
                exact boundary entry entryMember candidate
                  (by simp [candidateMember])
              rw [restoreCanonicalIndexes_encodeIndexTableGroups
                (nextPage + (indexPagesOf current).length) tables remaining
                suffix tailWellFormed tailBoundary remainingResult]

theorem rebuildCanonicalDatabase_encoded (database : Core.Database)
    (nextPage : Nat) (encodings : List IndexEncoding)
    (encoded : encodeIndexTableGroups nextPage database.tables =
      some encodings) :
    CoreDecode.rebuildCanonicalDatabase
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry)) =
          some database.canonicalize := by
  unfold CoreDecode.rebuildCanonicalDatabase
  have restored := restoreCanonicalIndexes_encodeIndexTableGroups nextPage
    database.tables encodings [] database.tablesWellFormed (by simp) encoded
  simp only [List.append_nil] at restored
  rw [restored]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]
  have rebuilt := Core.Database.rebuild_self database.canonicalize
  change Core.Database.rebuild
      (database.tables.map Core.Table.canonicalize) =
        .ok database.canonicalize at rebuilt
  rw [rebuilt]
  rfl

theorem validateCanonicalIndexesForTableFrom_encodeIndexes
    (source : CoreDecode.PageSource) (table : Core.Table) :
    ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List IndexEncoding)
      (suffix : List CoreDecode.CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      encodeIndexes nextPage
          (indexes.map fun index => (table, index)) = some encodings →
      (∀ encoding ∈ encodings,
        CorePageCodec.PageSourceContains source encoding.numberedPages) →
      (∀ encoding ∈ encodings,
        encoding.numberedPages.length < source.pageCount + 1) →
      CoreDecode.validateCanonicalIndexesForTableFrom source
        table.withoutIndexes
        (encodings.map (fun encoding =>
          CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some suffix
  | _, [], encodings, suffix, _, boundary, encoded, _, _ => by
      simp only [List.map_nil, encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold CoreDecode.validateCanonicalIndexesForTableFrom
          rw [dif_neg (by simpa using boundary entry (by simp))]
  | nextPage, index :: indexes, encodings, suffix, members, boundary,
      encoded, contains, pagesBound => by
      simp only [List.map_cons, encodeIndexes, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : encodeIndex nextPage table index with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeIndexes head.nextPage
              (indexes.map fun candidate => (table, candidate)) with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encodings
              simp only [List.map_cons, List.cons_append]
              unfold CoreDecode.validateCanonicalIndexesForTableFrom
              have identity := encodeIndex_identity headResult
              have sameTable :
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry).table =
                    table.withoutIndexes.schema.name := by
                simp [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded, identity.2.1]
              rw [dif_pos sameTable]
              have metadata : CoreDecode.decodeCanonicalIndex
                  table.withoutIndexes.schema table.withoutIndexes.schema.name
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry) =
                    some index := by
                simp only [Core.Table.withoutIndexes_schema]
                simpa [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded, identity.2.1,
                  identity.2.2] using
                    (CoreDecode.decodeCanonicalIndex_encoded table index
                      (members index (by simp)) head.rootPage)
              rw [metadata]
              simp only [Option.bind_eq_bind, Option.bind]
              have physical := head.decode_exact source
                (contains head (by simp)) (pagesBound head (by simp))
              have physical' :
                  CoreDecode.decodeIndexSubtreeFrom source
                      (source.pageCount + 1) head.rootPage =
                    some (CoreDecode.expectedIndexEntries table index) := by
                simpa [identity.2.1, identity.2.2] using physical
              have catalogRoot :
                  (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry).rootPage =
                    head.rootPage := by
                simp [IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded]
              rw [catalogRoot, physical']
              simp only [Option.bind_eq_bind, Option.bind]
              rw [dif_pos (by
                simpa [CoreDecode.expectedIndexEntries] using
                  (CoreDecode.expectedIndexEntries_withoutIndexes table index).symm)]
              exact validateCanonicalIndexesForTableFrom_encodeIndexes
                source table head.nextPage indexes tail suffix
                (fun candidate member => members candidate (by simp [member]))
                boundary tailResult
                (fun encoding member => contains encoding (by simp [member]))
                (fun encoding member => pagesBound encoding (by simp [member]))

theorem validateCanonicalIndexGroupsFrom_encodeIndexTableGroups
    (source : CoreDecode.PageSource) :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List IndexEncoding)
      (suffix : List CoreDecode.CatalogEntry),
      Core.TablesWellFormed tables →
      (∀ entry ∈ suffix, ∀ table ∈ tables,
        entry.table ≠ table.schema.name) →
      encodeIndexTableGroups nextPage tables = some encodings →
      (∀ encoding ∈ encodings,
        CorePageCodec.PageSourceContains source encoding.numberedPages) →
      (∀ encoding ∈ encodings,
        encoding.numberedPages.length < source.pageCount + 1) →
      CoreDecode.validateCanonicalIndexGroupsFrom source
        (tables.map Core.Table.withoutIndexes)
        (encodings.map (fun encoding =>
          CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some suffix
  | _, [], encodings, suffix, _, _, encoded, _, _ => by
      simp only [encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, suffix, wellFormed, boundary,
      encoded, contains, pagesBound => by
      simp only [Core.TablesWellFormed, Core.namesUnique, List.map_cons,
        List.pairwise_cons] at wellFormed
      rcases wellFormed with ⟨headDistinct, tailWellFormed⟩
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
              simp only [List.map_cons, List.map_append, List.append_assoc]
              unfold CoreDecode.validateCanonicalIndexGroupsFrom
              have remainingBelongs := encodeIndexTableGroups_tables
                remainingResult
              have currentBoundary : ∀ entry ∈
                  (remaining.map (fun encoding =>
                    CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++
                      suffix),
                  entry.table ≠ table.schema.name := by
                intro entry member
                simp only [List.mem_append] at member
                rcases member with encodedMember | suffixMember
                · rcases List.mem_map.mp encodedMember with
                    ⟨encoding, encodingMember, equal⟩
                  subst entry
                  have tableMember := remainingBelongs encoding encodingMember
                  have distinct := headDistinct encoding.table.schema.name
                    (List.mem_map_of_mem tableMember)
                  simpa [IndexEncoding.catalogEntry,
                    CoreDecode.CatalogEntry.ofEncoded] using distinct.symm
                · exact boundary entry suffixMember table (by simp)
              rw [validateCanonicalIndexesForTableFrom_encodeIndexes source
                table nextPage table.indexes current
                (remaining.map (fun encoding =>
                  CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ++
                    suffix)
                (by simp) currentBoundary currentResult
                (fun encoding member => contains encoding (by simp [member]))
                (fun encoding member => pagesBound encoding (by simp [member]))]
              have tailBoundary : ∀ entry ∈ suffix,
                  ∀ candidate ∈ tables,
                    entry.table ≠ candidate.schema.name := by
                intro entry entryMember candidate candidateMember
                exact boundary entry entryMember candidate
                  (by simp [candidateMember])
              exact validateCanonicalIndexGroupsFrom_encodeIndexTableGroups
                source (nextPage + (indexPagesOf current).length) tables
                remaining suffix tailWellFormed tailBoundary remainingResult
                (fun encoding member => contains encoding (by simp [member]))
                (fun encoding member => pagesBound encoding (by simp [member]))

theorem applyIndexesForOpen_encoded (source : CoreDecode.PageSource)
    (database : Core.Database) (nextPage : Nat)
    (encodings : List IndexEncoding)
    (encoded : encodeIndexTableGroups nextPage database.tables =
      some encodings)
    (contains : ∀ encoding ∈ encodings,
      CorePageCodec.PageSourceContains source encoding.numberedPages)
    (pagesBound : ∀ encoding ∈ encodings,
      encoding.numberedPages.length < source.pageCount + 1) :
    CoreDecode.applyIndexesForOpen source database.withoutIndexes
      (encodings.map (fun encoding =>
        CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry)) =
          some database.canonicalize := by
  unfold CoreDecode.applyIndexesForOpen
  have validated :=
    validateCanonicalIndexGroupsFrom_encodeIndexTableGroups source nextPage
      database.tables encodings [] database.tablesWellFormed (by simp)
      encoded contains pagesBound
  simp only [List.append_nil] at validated
  have validation : CoreDecode.validateCanonicalIndexesFrom source
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry)) = some () := by
    unfold CoreDecode.validateCanonicalIndexesFrom
    rw [validated]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [dif_pos True.intro]
  simp only [Core.Database.withoutIndexes]
  rw [validation]
  exact rebuildCanonicalDatabase_encoded database nextPage encodings encoded

end CoreWideIndex

end SQLeanite
