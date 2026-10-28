import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeCanonicalCatalogSchemaPageForEntries
import SQLeanite.CoreOverflow.EncodeIndexesMemberRange

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

/-- Every table returned by the canonical metadata rebuilder is an exact
canonicalization fixed point.  The proof follows the executable recursion and
uses the checked `Table.rebuild` result at each table. -/
theorem restoreCanonicalIndexes_fixed :
    ∀ (tables : List Core.Table) (entries restored : List CatalogEntry)
      (resultTables : List Core.Table),
      restoreCanonicalIndexes tables entries =
        some (resultTables, restored) →
      ∀ table ∈ resultTables, table.canonicalize = table
  | [], entries, restored, resultTables, success => by
      simp only [restoreCanonicalIndexes, Option.some.injEq] at success
      injection success with tablesEqual
      subst resultTables
      simp
  | input :: inputs, entries, restored, resultTables, success => by
      simp only [restoreCanonicalIndexes, Option.bind_eq_bind, Option.bind]
        at success
      cases metadataResult : decodeCanonicalIndexesForTable input.schema
          input.schema.name entries with
      | none => simp [metadataResult] at success
      | some metadata =>
          rcases metadata with ⟨indexes, remaining⟩
          simp only [metadataResult] at success
          cases rebuiltResult :
              (Core.Table.rebuild input.schema indexes input.rows input.catalogSource).toOption with
          | none => simp [rebuiltResult] at success
          | some table =>
              simp only [rebuiltResult] at success
              cases tailResult : restoreCanonicalIndexes inputs remaining with
              | none => simp [tailResult] at success
              | some tail =>
                  rcases tail with ⟨tailTables, suffix⟩
                  simp only [tailResult, Option.some.injEq] at success
                  injection success with tablesEqual suffixEqual
                  subst resultTables
                  subst restored
                  intro candidate member
                  simp only [List.mem_cons] at member
                  cases member with
                  | inl equal =>
                      subst candidate
                      cases rebuild : Core.Table.rebuild input.schema indexes
                          input.rows input.catalogSource with
                      | error message =>
                          rw [rebuild] at rebuiltResult
                          cases rebuiltResult
                      | ok value =>
                          rw [rebuild] at rebuiltResult
                          have valueEqual : value = table := by
                            simpa only [Except.toOption,
                              Option.some.injEq] using rebuiltResult
                          subst table
                          exact Core.Table.rebuild_canonicalize_fixed rebuild
                  | inr tailMember =>
                      exact restoreCanonicalIndexes_fixed inputs remaining
                        suffix tailTables tailResult candidate tailMember

private theorem map_canonicalize_eq_self (tables : List Core.Table)
    (fixed : ∀ table ∈ tables, table.canonicalize = table) :
    tables.map Core.Table.canonicalize = tables := by
  induction tables with
  | nil => rfl
  | cons table tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨fixed table (by simp), induction (fun candidate member =>
        fixed candidate (by simp [member]))⟩

/-- `rebuildCanonicalDatabase` deserves its name extensionally as well as
logically: every successful result is already a fixed point of the public
canonicalization operation. -/
theorem rebuildCanonicalDatabase_fixed
    {tables : List Core.Table} {entries : List CatalogEntry}
    {database : Core.Database}
    (success : rebuildCanonicalDatabase tables entries = some database) :
    database.canonicalize = database := by
  unfold rebuildCanonicalDatabase at success
  cases restoredResult : restoreCanonicalIndexes tables entries with
  | none => simp [restoredResult] at success
  | some restored =>
      rcases restored with ⟨resultTables, suffix⟩
      simp only [restoredResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next consumed =>
        cases rebuilt : Core.Database.rebuild resultTables with
        | error message =>
          rw [rebuilt] at success
          cases success
        | ok value =>
          rw [rebuilt] at success
          have equal : value = database := by
            simpa only [Except.toOption, Option.some.injEq] using success
          subst database
          have tablesEqual : value.tables = resultTables :=
            Core.Database.rebuild_tables rebuilt
          cases value with
          | mk valueTables valueWellFormed =>
              simp only [Core.Database.canonicalize]
              congr 1
              have fixed : ∀ table ∈ valueTables,
                  table.canonicalize = table := by
                intro table member
                exact restoreCanonicalIndexes_fixed tables entries suffix
                  resultTables restoredResult table (by
                    rw [← tablesEqual]
                    exact member)
              exact map_canonicalize_eq_self valueTables fixed
      next => contradiction

theorem decodeCanonicalIndexesForTable_encodeIndexes (table : Core.Table) :
    ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List CoreFile.IndexEncoding) (suffix : List CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      CoreFile.encodeIndexes nextPage (indexes.map fun index => (table, index)) =
        some encodings →
      decodeCanonicalIndexesForTable table.schema table.schema.name
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (indexes, suffix)
  | _, [], encodings, suffix, _, boundary, encoded => by
      simp only [List.map_nil, CoreFile.encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold decodeCanonicalIndexesForTable
          exact dif_neg (boundary entry (by simp))
  | nextPage, index :: indexes, encodings, suffix, members, boundary, encoded => by
      simp only [List.map_cons, CoreFile.encodeIndexes,
        Option.bind_eq_bind, Option.bind] at encoded
      cases leavesResult : CoreFile.indexLeaves table index with
      | none => simp [leavesResult] at encoded
      | some leaves =>
        simp only [leavesResult] at encoded
        let layout : CoreFile.IndexLayout := ⟨nextPage, leaves⟩
        cases pagesResult : CoreFile.indexPages? layout.rootPage layout.leaves with
        | none => simp [layout, pagesResult] at encoded
        | some physicalPages =>
          simp only [layout, pagesResult] at encoded
          cases remainingResult : CoreFile.encodeIndexes
              (nextPage + CoreFile.tableFootprint leaves)
              (indexes.map fun candidate => (table, candidate)) with
          | none => simp [remainingResult] at encoded
          | some remaining =>
            simp only [remainingResult] at encoded
            injection encoded with equal
            subst encodings
            simp only [List.map_cons, List.cons_append]
            unfold decodeCanonicalIndexesForTable
            have sameTable :
                (CatalogEntry.ofEncoded
                  (CoreFile.IndexEncoding.catalogEntry
                    (⟨table, index, layout, physicalPages⟩ :
                      CoreFile.IndexEncoding))).table =
                  table.schema.name := rfl
            rw [dif_pos sameTable]
            have decoded :
                decodeCanonicalIndex table.schema table.schema.name
                  (CatalogEntry.ofEncoded
                    (CoreFile.IndexEncoding.catalogEntry
                      (⟨table, index, layout, physicalPages⟩ :
                        CoreFile.IndexEncoding))) = some index := by
              change decodeCanonicalIndex table.schema table.schema.name
                (CatalogEntry.ofEncoded ({
                  kind := "index"
                  name := index.name
                  table := table.schema.name
                  rootPage := layout.rootPage
                  sql := CoreFile.indexSQL table index
                  sqlIsNull := index.isImplicitPrimary table.schema
                } : CoreFile.CatalogEntry)) = some index
              exact decodeCanonicalIndex_encoded table index
                (members index (by simp)) layout.rootPage
            rw [decoded]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [decodeCanonicalIndexesForTable_encodeIndexes table
              (nextPage + CoreFile.tableFootprint leaves) indexes remaining suffix
              (fun candidate member => members candidate (by simp [member]))
              boundary remainingResult]

theorem restoreCanonicalIndexes_encodeIndexTableGroups :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreFile.IndexEncoding) (suffix : List CatalogEntry),
      Core.TablesWellFormed tables →
      (∀ entry ∈ suffix, ∀ table ∈ tables,
        entry.table ≠ table.schema.name) →
      CoreFile.encodeIndexTableGroups nextPage tables = some encodings →
      restoreCanonicalIndexes (tables.map Core.Table.withoutIndexes)
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (tables.map Core.Table.canonicalize, suffix)
  | _, [], encodings, suffix, _, _, encoded => by
      simp only [CoreFile.encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, suffix, wellFormed, boundary,
      encoded => by
      simp only [Core.TablesWellFormed, Core.namesUnique, List.map_cons,
        List.pairwise_cons] at wellFormed
      rcases wellFormed with ⟨headDistinct, tailWellFormed⟩
      simp only [CoreFile.encodeIndexTableGroups,
        Option.bind_eq_bind, Option.bind] at encoded
      cases currentResult : CoreFile.encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : CoreFile.encodeIndexTableGroups
            (CoreFile.indexEndPage nextPage current) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult] at encoded
          injection encoded with equal
          subst encodings
          simp only [List.map_cons, List.map_append, List.append_assoc]
          unfold restoreCanonicalIndexes
          have remainingBelongs := CoreFile.encodeIndexTableGroups_tables
            (CoreFile.indexEndPage nextPage current) tables remaining
            remainingResult
          have currentBoundary : ∀ entry ∈
              (remaining.map (fun encoding =>
                CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix),
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
              simpa [CoreFile.IndexEncoding.catalogEntry,
                CatalogEntry.ofEncoded] using distinct.symm
            · exact boundary entry suffixMember table (by simp)
          simp only [Core.Table.withoutIndexes_schema,
            Core.Table.withoutIndexes_rows, Core.Table.withoutIndexes_catalogSource]
          rw [decodeCanonicalIndexesForTable_encodeIndexes table nextPage
            table.indexes current
            (remaining.map (fun encoding =>
              CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix)
            (by simp) currentBoundary currentResult]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [Core.Table.rebuild_self]
          simp only [Except.toOption]
          have tailBoundary : ∀ entry ∈ suffix, ∀ candidate ∈ tables,
              entry.table ≠ candidate.schema.name := by
            intro entry entryMember candidate candidateMember
            exact boundary entry entryMember candidate (by simp [candidateMember])
          rw [restoreCanonicalIndexes_encodeIndexTableGroups
            (CoreFile.indexEndPage nextPage current) tables remaining suffix
            tailWellFormed tailBoundary remainingResult]

theorem rebuildCanonicalDatabase_encoded (database : Core.Database)
    (nextPage : Nat) (encodings : List CoreFile.IndexEncoding)
    (encoded : CoreFile.encodeIndexTableGroups nextPage database.tables =
      some encodings) :
    rebuildCanonicalDatabase
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CatalogEntry.ofEncoded encoding.catalogEntry)) =
          some database.canonicalize := by
  unfold rebuildCanonicalDatabase
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
  simp only [Except.toOption]

theorem decodeCanonicalIndexesForTable_encodeOverflowIndexes
    (table : Core.Table) :
    ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List CoreOverflow.IndexEncoding)
      (suffix : List CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      CoreOverflow.encodeIndexes nextPage
          (indexes.map fun index => (table, index)) = some encodings →
      decodeCanonicalIndexesForTable table.schema table.schema.name
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (indexes, suffix)
  | _, [], encodings, suffix, _, boundary, encoded => by
      simp only [List.map_nil, CoreOverflow.encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold decodeCanonicalIndexesForTable
          exact dif_neg (boundary entry (by simp))
  | nextPage, index :: indexes, encodings, suffix, members, boundary,
      encoded => by
      simp only [List.map_cons, CoreOverflow.encodeIndexes,
        Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : CoreOverflow.encodeIndex nextPage table index with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : CoreOverflow.encodeIndexes
            (nextPage + head.pages.length)
            (indexes.map fun candidate => (table, candidate)) with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          simp only [List.map_cons, List.cons_append]
          unfold decodeCanonicalIndexesForTable
          have identity := CoreOverflow.encodeIndex_identity headResult
          have sameTable :
              (CatalogEntry.ofEncoded head.catalogEntry).table =
                table.schema.name := by
            simp [CoreOverflow.IndexEncoding.catalogEntry,
              CatalogEntry.ofEncoded, identity.1]
          rw [dif_pos sameTable]
          have decoded : decodeCanonicalIndex table.schema table.schema.name
              (CatalogEntry.ofEncoded head.catalogEntry) = some index := by
            rw [show head = {
              table := table
              index := index
              rootPage := nextPage
              topology := head.topology
              treePages := head.treePages
              overflowPages := head.overflowPages
            } from by cases head; simp_all]
            change decodeCanonicalIndex table.schema table.schema.name
              (CatalogEntry.ofEncoded ({
                kind := "index"
                name := index.name
                table := table.schema.name
                rootPage := nextPage
                sql := CoreFile.indexSQL table index
                sqlIsNull := index.isImplicitPrimary table.schema
              } : CoreFile.CatalogEntry)) = some index
            exact decodeCanonicalIndex_encoded table index
              (members index (by simp)) nextPage
          rw [decoded]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [decodeCanonicalIndexesForTable_encodeOverflowIndexes table
            (nextPage + head.pages.length) indexes tail suffix
            (fun candidate member => members candidate (by simp [member]))
            boundary tailResult]

theorem restoreCanonicalIndexes_encodeOverflowIndexTableGroups :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreOverflow.IndexEncoding)
      (suffix : List CatalogEntry),
      Core.TablesWellFormed tables →
      (∀ entry ∈ suffix, ∀ table ∈ tables,
        entry.table ≠ table.schema.name) →
      CoreOverflow.encodeIndexTableGroups nextPage tables = some encodings →
      restoreCanonicalIndexes (tables.map Core.Table.withoutIndexes)
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (tables.map Core.Table.canonicalize, suffix)
  | _, [], encodings, suffix, _, _, encoded => by
      simp only [CoreOverflow.encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, suffix, wellFormed, boundary,
      encoded => by
      simp only [Core.TablesWellFormed, Core.namesUnique, List.map_cons,
        List.pairwise_cons] at wellFormed
      rcases wellFormed with ⟨headDistinct, tailWellFormed⟩
      simp only [CoreOverflow.encodeIndexTableGroups,
        Option.bind_eq_bind, Option.bind] at encoded
      cases currentResult : CoreOverflow.encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : CoreOverflow.encodeIndexTableGroups
            (nextPage + (CoreOverflow.indexPagesOf current).length) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult, Option.some.injEq] at encoded
          subst encodings
          simp only [List.map_cons, List.map_append, List.append_assoc]
          unfold restoreCanonicalIndexes
          have remainingBelongs := CoreOverflow.encodeIndexTableGroups_tables
            remainingResult
          have currentBoundary : ∀ entry ∈
              (remaining.map (fun encoding =>
                CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix),
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
              simpa [CoreOverflow.IndexEncoding.catalogEntry,
                CatalogEntry.ofEncoded] using distinct.symm
            · exact boundary entry suffixMember table (by simp)
          simp only [Core.Table.withoutIndexes_schema,
            Core.Table.withoutIndexes_rows, Core.Table.withoutIndexes_catalogSource]
          rw [decodeCanonicalIndexesForTable_encodeOverflowIndexes table
            nextPage table.indexes current
            (remaining.map (fun encoding =>
              CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix)
            (by simp) currentBoundary currentResult]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [Core.Table.rebuild_self]
          simp only [Except.toOption]
          have tailBoundary : ∀ entry ∈ suffix, ∀ candidate ∈ tables,
              entry.table ≠ candidate.schema.name := by
            intro entry entryMember candidate candidateMember
            exact boundary entry entryMember candidate (by simp [candidateMember])
          rw [restoreCanonicalIndexes_encodeOverflowIndexTableGroups
            (nextPage + (CoreOverflow.indexPagesOf current).length) tables
            remaining suffix tailWellFormed tailBoundary remainingResult]

theorem rebuildCanonicalDatabase_overflowEncoded (database : Core.Database)
    (nextPage : Nat) (encodings : List CoreOverflow.IndexEncoding)
    (encoded : CoreOverflow.encodeIndexTableGroups nextPage database.tables =
      some encodings) :
    rebuildCanonicalDatabase
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CatalogEntry.ofEncoded encoding.catalogEntry)) =
          some database.canonicalize := by
  unfold rebuildCanonicalDatabase
  have restored := restoreCanonicalIndexes_encodeOverflowIndexTableGroups
    nextPage database.tables encodings [] database.tablesWellFormed (by simp)
    encoded
  simp only [List.append_nil] at restored
  rw [restored]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]
  have rebuilt := Core.Database.rebuild_self database.canonicalize
  change Core.Database.rebuild
      (database.tables.map Core.Table.canonicalize) =
        .ok database.canonicalize at rebuilt
  rw [rebuilt]
  simp only [Except.toOption]

end CoreDecode

end SQLeanite
