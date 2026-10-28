import SQLeanite.CoreLocalizedRepresentation.TablesOnSourceTablesDecode

namespace SQLeanite
namespace CoreLocalizedRepresentation

theorem alignTables?_indexImages_none :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table}
      {aligned : CoreChunkPageDelta.AlignedTables target},
      CoreChunkPageDelta.alignTables? nextPage states target = some aligned →
      aligned.delta = none →
      TablesIndexImagesAligned
        (states.map fun state => state.table) target
  | _, [], target, aligned, success, noChange => by
      cases target <;> simp [CoreChunkPageDelta.alignTables?] at success
      subst aligned
      exact .nil
  | nextPage, old :: olds, target, aligned, success, noChange => by
      cases target with
      | nil => simp [CoreChunkPageDelta.alignTables?] at success
      | cons replacement replacements =>
        unfold CoreChunkPageDelta.alignTables? at success
        split at success
        next same =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          exact .cons (TableIndexImageEq.ofEquiv same)
            (alignTables?_indexImages_none tailResult noChange)
        next =>
          split at success
          next => contradiction
          next head headResult =>
            split at success
            next => contradiction
            next tail tailResult =>
              split at success
              next =>
                injection success with equal
                subst aligned
                simp at noChange
              next => contradiction

theorem alignTables?_indexImages_changed :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table}
      {aligned : CoreChunkPageDelta.AlignedTables target}
      {delta : CoreChunkPageDelta.TableDelta},
      CoreChunkPageDelta.alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.tablePagesSufficient = true →
      TablesIndexImagesAligned
        (states.map fun state => state.table) target
  | _, [], target, aligned, delta, success, selected, sufficient => by
      cases target <;> simp [CoreChunkPageDelta.alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, old :: olds, target, aligned, delta, success, selected,
      sufficient => by
      cases target with
      | nil => simp [CoreChunkPageDelta.alignTables?] at success
      | cons replacement replacements =>
        unfold CoreChunkPageDelta.alignTables? at success
        split at success
        next same =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          exact .cons (TableIndexImageEq.ofEquiv same)
            (alignTables?_indexImages_changed tailResult selected sufficient)
        next =>
          split at success
          next => contradiction
          next head headResult =>
            split at success
            next => contradiction
            next tail tailResult =>
              split at success
              next onlyChange =>
                injection success with equal
                subst aligned
                have headEqual : head = delta := Option.some.inj selected
                subst head
                have tailNone : tail.delta = none := by
                  cases tailDelta : tail.delta with
                  | none => rfl
                  | some value => simp [tailDelta] at onlyChange
                have headAligned := TableIndexImageEq.ofDelta delta sufficient
                rw [CoreChunkPageDelta.replaceBetween?_before headResult,
                  CoreChunkPageDelta.replaceBetween?_table headResult]
                    at headAligned
                exact .cons headAligned
                  (alignTables?_indexImages_none tailResult tailNone)
              next => contradiction

theorem updateState?_indexImagesAligned
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (updated : CoreChunkPageDelta.updateState? state database = some delta) :
    TablesIndexImagesAligned state.database.tables database.tables := by
  rcases CoreChunkPageDelta.updateState?_alignment updated with
    ⟨aligned, alignment, _, selected⟩
  have result := alignTables?_indexImages_changed alignment selected
    (CoreChunkPageDelta.updateState?_tablePagesSufficient updated)
  rw [state.tables_eq] at result
  exact result

def IndexOnSource.retarget
    {source : CoreDecode.PageSource} {before after : Core.Table}
    {entry : CoreDecode.CatalogEntry} {index : Core.Index}
    (owned : IndexOnSource source before entry index)
    (aligned : TableIndexImageEq before after) :
    IndexOnSource source after entry index := by
  rcases owned with ⟨reference, encoding, sameTable, sameRoot, metadata,
    member, encoded, reads, rootPositive, pageBound, withinSource, logical⟩
  refine ⟨reference, encoding, ?_, sameRoot, ?_, ?_, encoded, reads,
    rootPositive, pageBound, withinSource, ?_⟩
  · simpa [← aligned.1] using sameTable
  · simpa [← aligned.1] using metadata
  · simpa [← aligned.2.1] using member
  · exact logical.trans (aligned.2.2 index member)

def IndexesOnSource.retarget
    {source : CoreDecode.PageSource} {before after : Core.Table}
    {entries : List CoreDecode.CatalogEntry}
    (owned : IndexesOnSource source before entries)
    (aligned : TableIndexImageEq before after) :
    IndexesOnSource source after entries := by
  induction owned with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (head.retarget aligned) induction

def IndexGroupsOnSource.retarget
    {source : CoreDecode.PageSource} {before after : List Core.Table}
    {entries : List CoreDecode.CatalogEntry}
    (owned : IndexGroupsOnSource source before entries)
    (aligned : TablesIndexImagesAligned before after) :
    IndexGroupsOnSource source after entries := by
  induction owned generalizing after with
  | nil =>
      cases aligned
      exact .nil
  | cons current boundary tail induction =>
      cases aligned with
      | cons headAligned tailAligned =>
          exact .cons (current.retarget headAligned)
            (by
              intro entry member equal
              exact boundary entry member (equal.trans
                (congrArg Core.Schema.name headAligned.1).symm))
            (induction tailAligned)

theorem IndexGroupsDecode.validateGroups
    {source : CoreDecode.PageSource} {tables : List Core.Table}
    {entries : List CoreDecode.CatalogEntry}
    (decoded : IndexGroupsDecode source tables entries) :
    CoreDecode.validateCanonicalIndexGroupsFrom source tables entries =
      some [] := by
  induction decoded with
  | nil => rfl
  | cons current boundary tail induction =>
      unfold CoreDecode.validateCanonicalIndexGroupsFrom
      rw [current.validateForTable _ boundary]
      simp only [Option.bind_eq_bind, Option.bind]
      exact induction

theorem IndexGroupsDecode.validate
    {source : CoreDecode.PageSource} {tables : List Core.Table}
    {entries : List CoreDecode.CatalogEntry}
    (decoded : IndexGroupsDecode source tables entries) :
    CoreDecode.validateCanonicalIndexesFrom source tables entries = some () := by
  unfold CoreDecode.validateCanonicalIndexesFrom
  rw [decoded.validateGroups]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]

/-- Catalog metadata for one table's contiguous canonical index run.  This is
deliberately separate from `IndexesDecode`: metadata can remain unchanged
while the corresponding index pages are replaced by a localized mutation. -/
inductive IndexMetadataDecode (table : Core.Table) :
    List CoreDecode.CatalogEntry → List Core.Index → Prop where
  | nil : IndexMetadataDecode table [] []
  | cons {entry : CoreDecode.CatalogEntry}
      {entries : List CoreDecode.CatalogEntry} {index : Core.Index}
      {indexes : List Core.Index}
      (sameTable : entry.table = table.schema.name)
      (metadata : CoreDecode.decodeCanonicalIndex table.schema
        table.schema.name entry = some index)
      (tail : IndexMetadataDecode table entries indexes) :
      IndexMetadataDecode table (entry :: entries) (index :: indexes)

theorem IndexMetadataDecode.decode
    {table : Core.Table} {entries : List CoreDecode.CatalogEntry}
    {indexes : List Core.Index}
    (decoded : IndexMetadataDecode table entries indexes)
    (suffix : List CoreDecode.CatalogEntry)
    (boundary : ∀ entry ∈ suffix,
      entry.table ≠ table.schema.name) :
    CoreDecode.decodeCanonicalIndexesForTable table.schema
      table.schema.name (entries ++ suffix) = some (indexes, suffix) := by
  induction decoded with
  | nil =>
      simp only [List.nil_append]
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          unfold CoreDecode.decodeCanonicalIndexesForTable
          rw [dif_neg (boundary entry (by simp))]
  | cons sameTable metadata tail induction =>
      simp only [List.cons_append]
      unfold CoreDecode.decodeCanonicalIndexesForTable
      rw [dif_pos sameTable, metadata]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [induction]

/-- Exact metadata runs for all tables, in the order consumed by the canonical
database rebuilder. -/
inductive IndexMetadataGroups :
    List Core.Table → List CoreDecode.CatalogEntry → Prop where
  | nil : IndexMetadataGroups [] []
  | cons {table : Core.Table} {tables : List Core.Table}
      {entries remaining : List CoreDecode.CatalogEntry}
      (current : IndexMetadataDecode table entries table.indexes)
      (boundary : ∀ entry ∈ remaining,
        entry.table ≠ table.schema.name)
      (tail : IndexMetadataGroups tables remaining) :
      IndexMetadataGroups (table :: tables) (entries ++ remaining)

/-- Catalog metadata decoding depends on a table's schema and declared index
list, not on its rows or persistent-tree topology. -/
theorem IndexMetadataDecode.retargetSchema
    {before after : Core.Table} {entries : List CoreDecode.CatalogEntry}
    {indexes : List Core.Index}
    (schemaEq : before.schema = after.schema)
    (decoded : IndexMetadataDecode before entries indexes) :
    IndexMetadataDecode after entries indexes := by
  induction decoded with
  | nil => exact .nil
  | cons sameTable metadata tail induction =>
      exact .cons (by simpa [← schemaEq] using sameTable)
        (by simpa [← schemaEq] using metadata) induction

/-- Transport every catalog metadata group through the declaration-preserving
table alignment proved by the live delta builder.  No catalog SQL is reparsed
at runtime; this theorem changes only the logical row-bearing table index of
the erased certificate. -/
theorem IndexMetadataGroups.retarget :
    ∀ {before after : List Core.Table}
      {entries : List CoreDecode.CatalogEntry},
      CoreChunkPageDelta.TablesMetadataAligned before after →
      IndexMetadataGroups before entries →
      IndexMetadataGroups after entries
  | [], [], entries, .nil, decoded => by
      cases decoded
      exact .nil
  | beforeTable :: beforeTables, afterTable :: afterTables, entries,
      .cons metadataEq aligned, decoded => by
      cases decoded with
      | cons current boundary tail =>
          have current' := current.retargetSchema metadataEq.1
          rw [metadataEq.2.1] at current'
          exact .cons current'
            (by
              intro entry member same
              have nameEq : beforeTable.schema.name =
                  afterTable.schema.name := congrArg Core.Schema.name metadataEq.1
              exact boundary entry member (same.trans nameEq.symm))
            (IndexMetadataGroups.retarget aligned tail)

theorem IndexMetadataDecode.entries_nil
    {table : Core.Table} {entries : List CoreDecode.CatalogEntry}
    (decoded : IndexMetadataDecode table entries []) : entries = [] := by
  cases decoded
  rfl

theorem IndexMetadataGroups.entries_nil_of_indexless :
    ∀ {tables : List Core.Table} {entries : List CoreDecode.CatalogEntry},
      (∀ table ∈ tables, table.indexes = []) →
      IndexMetadataGroups tables entries → entries = []
  | [], entries, indexless, decoded => by
      cases decoded
      rfl
  | table :: tables, entries, indexless, decoded => by
      cases decoded with
      | cons current boundary tail =>
          have indexesEmpty := indexless table (by simp)
          rw [indexesEmpty] at current
          have entriesEmpty := current.entries_nil
          have tailEmpty := entries_nil_of_indexless
            (fun candidate member => indexless candidate (by simp [member])) tail
          simp [entriesEmpty, tailEmpty]

/-- An indexless logical database has the unique empty physical index run on
every page source. -/
def IndexGroupsDecode.indexless (source : CoreDecode.PageSource) :
    ∀ tables : List Core.Table, IndexGroupsDecode source tables []
  | [] => .nil
  | table :: tables => .cons .nil (by simp) (indexless source tables)

def IndexGroupsOnSource.indexless (source : CoreDecode.PageSource) :
    ∀ tables : List Core.Table, IndexGroupsOnSource source tables []
  | [] => .nil
  | table :: tables => .cons .nil (by simp) (indexless source tables)

/-- One encoded index run establishes both its physical decoder equations and
its catalog-metadata reconstruction.  Keeping the pair together prevents the
two certificates from drifting to different index orders. -/
theorem indexCertificates_encodeIndexes
    (source : CoreDecode.PageSource) (table : Core.Table) :
    ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List CoreOverflow.IndexEncoding),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      CoreOverflow.encodeIndexes nextPage
        (indexes.map fun index => (table, index)) = some encodings →
      (∀ encoding ∈ encodings,
        CoreDecode.ReadsPagesFrom source encoding.rootPage encoding.pages) →
      (∀ encoding ∈ encodings, 0 < encoding.rootPage) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length < 2 ^ 32) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length ≤ source.pageCount + 1) →
      IndexesDecode source table.withoutIndexes
          (encodings.map fun encoding =>
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ∧
        IndexMetadataDecode table
          (encodings.map fun encoding =>
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) indexes ∧
        IndexesOnSource source table
          (encodings.map fun encoding =>
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry)
  | _, [], encodings, _, encoded, _, _, _, _ => by
      simp only [List.map_nil, CoreOverflow.encodeIndexes,
        Option.some.injEq] at encoded
      subst encodings
      exact ⟨.nil, .nil, .nil⟩
  | nextPage, index :: indexes, encodings, members, encoded, reads,
      positive, pageBound, sourceBound => by
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
          have identity := CoreOverflow.encodeIndex_identity headResult
          have headMember : index ∈ table.indexes := members index (by simp)
          have metadataOriginal := CoreDecode.decodeCanonicalIndex_encoded
            table index headMember nextPage
          have metadata : CoreDecode.decodeCanonicalIndex
              table.withoutIndexes.schema table.withoutIndexes.schema.name
              (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry) =
                some index := by
            simpa [CoreOverflow.IndexEncoding.catalogEntry, identity.1,
              identity.2.1, identity.2.2] using metadataOriginal
          have physicalOriginal := CoreDecode.decodeIndexSubtreeFrom_encodeIndex
            source headResult (by
              simpa [identity.2.2] using reads head (by simp))
            (by simpa [identity.2.2] using positive head (by simp))
            (by simpa [identity.2.2] using pageBound head (by simp))
            (by simpa [identity.2.2] using sourceBound head (by simp))
          have physical : CoreDecode.decodeIndexSubtreeFrom source
              (source.pageCount + 1)
              (CoreDecode.CatalogEntry.ofEncoded head.catalogEntry).rootPage =
                some (CoreDecode.expectedIndexEntries
                  table.withoutIndexes index) := by
            rw [show (CoreDecode.CatalogEntry.ofEncoded
                head.catalogEntry).rootPage = nextPage by
              simp [CoreOverflow.IndexEncoding.catalogEntry,
                CoreDecode.CatalogEntry.ofEncoded, identity.2.2]]
            calc
              _ = some (CoreDecode.expectedIndexEntries table index) := by
                simpa [CoreDecode.expectedIndexEntries] using physicalOriginal
              _ = some (CoreDecode.expectedIndexEntries
                    table.withoutIndexes index) :=
                congrArg some
                  (CoreDecode.expectedIndexEntries_withoutIndexes table index).symm
          have tailCertificates := indexCertificates_encodeIndexes source table
            (nextPage + head.pages.length) indexes tail
            (fun candidate member => members candidate (by simp [member]))
            tailResult
            (fun encoding member => reads encoding (by simp [member]))
            (fun encoding member => positive encoding (by simp [member]))
            (fun encoding member => pageBound encoding (by simp [member]))
            (fun encoding member => sourceBound encoding (by simp [member]))
          refine ⟨?_, ?_, ?_⟩
          · exact .cons (by
              change head.table.schema.name = table.schema.name
              rw [identity.1])
              metadata physical tailCertificates.1
          · exact .cons (by
              change head.table.schema.name = table.schema.name
              rw [identity.1])
              metadata tailCertificates.2.1
          · refine IndexesOnSource.cons ⟨table, head, ?_, ?_, ?_,
              headMember,
              (by simpa [identity.2.2] using headResult),
              reads head (by simp), positive head (by simp),
              pageBound head (by simp), sourceBound head (by simp), ?_⟩
              tailCertificates.2.2
            · change head.table.schema.name = table.schema.name
              simp [identity.1]
            · simp [CoreOverflow.IndexEncoding.catalogEntry,
                CoreDecode.CatalogEntry.ofEncoded, identity.2.2]
            · simpa [CoreOverflow.IndexEncoding.catalogEntry, identity.1,
                identity.2.1, identity.2.2] using metadataOriginal
            · rfl

end CoreLocalizedRepresentation

end SQLeanite
