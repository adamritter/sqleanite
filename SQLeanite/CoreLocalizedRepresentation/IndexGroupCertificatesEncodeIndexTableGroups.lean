import SQLeanite.CoreLocalizedRepresentation.AlignTablesIndexImagesNone

namespace SQLeanite
namespace CoreLocalizedRepresentation

/-- Lift the paired per-index certificates across all table groups in the
same contiguous order emitted by the physical encoder. -/
theorem indexGroupCertificates_encodeIndexTableGroups
    (source : CoreDecode.PageSource) :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreOverflow.IndexEncoding),
      Core.TablesWellFormed tables →
      CoreOverflow.encodeIndexTableGroups nextPage tables = some encodings →
      (∀ encoding ∈ encodings,
        CoreDecode.ReadsPagesFrom source encoding.rootPage encoding.pages) →
      (∀ encoding ∈ encodings, 0 < encoding.rootPage) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length < 2 ^ 32) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length ≤ source.pageCount + 1) →
      IndexGroupsDecode source (tables.map Core.Table.withoutIndexes)
          (encodings.map fun encoding =>
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ∧
        IndexMetadataGroups tables
          (encodings.map fun encoding =>
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) ∧
        IndexGroupsOnSource source tables
          (encodings.map fun encoding =>
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry)
  | _, [], encodings, _, encoded, _, _, _, _ => by
      simp only [CoreOverflow.encodeIndexTableGroups,
        Option.some.injEq] at encoded
      subst encodings
      exact ⟨.nil, .nil, .nil⟩
  | nextPage, table :: tables, encodings, wellFormed, encoded, reads,
      positive, pageBound, sourceBound => by
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
          have currentCertificates := indexCertificates_encodeIndexes
            source table nextPage table.indexes current (by simp)
            currentResult
            (fun encoding member => reads encoding (by simp [member]))
            (fun encoding member => positive encoding (by simp [member]))
            (fun encoding member => pageBound encoding (by simp [member]))
            (fun encoding member => sourceBound encoding (by simp [member]))
          have tailCertificates :=
            indexGroupCertificates_encodeIndexTableGroups source
              (nextPage + (CoreOverflow.indexPagesOf current).length)
              tables remaining tailWellFormed remainingResult
              (fun encoding member => reads encoding (by simp [member]))
              (fun encoding member => positive encoding (by simp [member]))
              (fun encoding member => pageBound encoding (by simp [member]))
              (fun encoding member => sourceBound encoding (by simp [member]))
          have remainingBelongs :=
            CoreOverflow.encodeIndexTableGroups_tables remainingResult
          have boundary : ∀ entry ∈
              remaining.map (fun encoding =>
                CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry),
              entry.table ≠ table.schema.name := by
            intro entry member
            rcases List.mem_map.mp member with
              ⟨encoding, encodingMember, rfl⟩
            have tableMember := remainingBelongs encoding encodingMember
            have distinct := headDistinct encoding.table.schema.name
              (List.mem_map_of_mem tableMember)
            simpa [CoreOverflow.IndexEncoding.catalogEntry,
              CoreDecode.CatalogEntry.ofEncoded] using distinct.symm
          refine ⟨?_, ?_, ?_⟩
          · simpa only [List.map_cons, List.map_append] using
              IndexGroupsDecode.cons currentCertificates.1 boundary
                tailCertificates.1
          · simpa only [List.map_append] using
              IndexMetadataGroups.cons currentCertificates.2.1 boundary
                tailCertificates.2.1
          · simpa only [List.map_append] using
              IndexGroupsOnSource.cons currentCertificates.2.2 boundary
                tailCertificates.2.2

theorem IndexMetadataGroups.restore
    {tables : List Core.Table} {entries : List CoreDecode.CatalogEntry}
    (decoded : IndexMetadataGroups tables entries) :
    CoreDecode.restoreCanonicalIndexes
      (tables.map Core.Table.withoutIndexes) entries =
        some (tables.map Core.Table.canonicalize, []) := by
  induction decoded with
  | nil => rfl
  | cons current boundary tail induction =>
      simp only [List.map_cons]
      unfold CoreDecode.restoreCanonicalIndexes
      simp only [Core.Table.withoutIndexes_schema,
        Core.Table.withoutIndexes_rows, Core.Table.withoutIndexes_catalogSource]
      rw [current.decode _ boundary]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [Core.Table.rebuild_self]
      simp only [Except.toOption]
      rw [induction]

theorem IndexMetadataGroups.rebuild
    (database : Core.Database) (entries : List CoreDecode.CatalogEntry)
    (decoded : IndexMetadataGroups database.tables entries) :
    CoreDecode.rebuildCanonicalDatabase
      (database.tables.map Core.Table.withoutIndexes) entries =
        some database.canonicalize := by
  unfold CoreDecode.rebuildCanonicalDatabase
  rw [decoded.restore]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]
  have rebuilt := Core.Database.rebuild_self database.canonicalize
  change Core.Database.rebuild
      (database.tables.map Core.Table.canonicalize) =
        .ok database.canonicalize at rebuilt
  rw [rebuilt]
  simp only [Except.toOption]

/-- Exact per-index page certificates plus exact catalog metadata reconstruction
close the `PageSourceRepresents.indexesRead` field.  The two obligations are
kept separate because a localized mutation changes physical pages while most
catalog metadata remains byte-identical. -/
theorem applyIndexesForOpen_of_indexGroups
    (source : CoreDecode.PageSource) (database : Core.Database)
    (entries : List CoreDecode.CatalogEntry)
    (decoded : IndexGroupsDecode source
      (database.tables.map Core.Table.withoutIndexes) entries)
    (rebuilt : CoreDecode.rebuildCanonicalDatabase
      (database.tables.map Core.Table.withoutIndexes) entries =
        some database.canonicalize) :
    CoreDecode.applyIndexesForOpen source database.withoutIndexes entries =
      some database.canonicalize := by
  unfold CoreDecode.applyIndexesForOpen
  simp only [Core.Database.withoutIndexes]
  rw [decoded.validate]
  exact rebuilt

/-- The physical and metadata certificates compose into the complete index
decoder equation required by `PageSourceRepresents`. -/
theorem applyIndexesForOpen_of_index_certificates
    (source : CoreDecode.PageSource) (database : Core.Database)
    (entries : List CoreDecode.CatalogEntry)
    (physical : IndexGroupsDecode source
      (database.tables.map Core.Table.withoutIndexes) entries)
    (metadata : IndexMetadataGroups database.tables entries) :
    CoreDecode.applyIndexesForOpen source database.withoutIndexes entries =
      some database.canonicalize := by
  exact applyIndexesForOpen_of_indexGroups source database entries physical
    (metadata.rebuild database entries)

/-- Canonical bulk images allocate every table-tree page before the first
index run.  Indexed ordinary updates preserve the complete table page-ID set,
so this compact separation invariant is enough to transport all unchanged
index bytes without inspecting them again. -/
def TablePagesBeforeIndexRoots
    (tables : List CoreChunkPageState.TableState)
    (entries : List CoreDecode.CatalogEntry) : Prop :=
  ∀ pageId ∈ CoreChunkPageState.tablePageIds tables,
    ∀ entry ∈ entries, pageId < entry.rootPage

/-- Complete physical state invariant below the SQLite header.  It combines
the store-owned table layout with exact index pages and catalog metadata, and
records the executable catalog partition explicitly.  This is the invariant
that bulk encoding establishes and localized mutation preserves. -/
structure DatabaseOnSource (source : CoreDecode.PageSource)
    (state : CoreChunkPageState.State) : Prop where
  components : ∃ (catalog tableEntries indexEntries :
      List CoreDecode.CatalogEntry),
    (source.readPage 1 >>= CoreDecode.decodeCatalogForOpen = some catalog) ∧
    (catalog.filter (fun entry => entry.kind == "table") = tableEntries) ∧
    (catalog.filter (fun entry => entry.kind == "index") = indexEntries) ∧
    TablesOnSource source tableEntries state.tables ∧
    IndexGroupsOnSource source
      state.database.tables indexEntries ∧
    IndexMetadataGroups state.database.tables indexEntries ∧
    TablePagesBeforeIndexRoots state.tables indexEntries

/-- Project the strong database invariant to the exact physical witness for
any allocator-owned table state. -/
theorem DatabaseOnSource.exists_table
    {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.State}
    (physical : DatabaseOnSource source state) :
    ∀ table ∈ state.tables, ∃ _witness : TableOnSource source table, True := by
  rcases physical.components with
    ⟨catalog, tableEntries, indexEntries, catalogRead, tableFilter,
      indexFilter, tables, indexes, metadata, separation⟩
  exact tables.exists_table

/-- Any represented table supplies an in-bounds root page, hence the backing
storage image is nonempty.  Localized header/catalog frame proofs use this
instead of accepting positivity as a separate caller premise. -/
theorem DatabaseOnSource.pageCount_pos_of_table
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    {state : CoreChunkPageState.State}
    (physical : DatabaseOnSource (CorePageSource.ofStorageImage image) state)
    (table : CoreChunkPageState.TableState) (member : table ∈ state.tables) :
    0 < image.pageCount := by
  let represented := Classical.choose (physical.exists_table table member)
  have rootMember : table.tree.root.rootId ∈ table.tree.root.pageIds :=
    PersistentPageTree.Node.rootId_mem_pageIds _
  rw [← CorePageCodec.encodeChunkNodeWithOverflow_pageNumbers
    table.table.schema table.tree.root represented.nextOverflow
      represented.encoding represented.encoded] at rootMember
  rcases List.mem_map.mp rootMember with
    ⟨rootPage, rootPageMember, rootNumber⟩
  have rootBound := represented.treeBounds image rootPage rootPageMember
  omega

theorem DatabaseOnSource.pageSourceRepresents
    {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.State}
    (physical : DatabaseOnSource source state) :
    CoreDecode.PageSourceRepresents source state.database := by
  rcases physical.components with
    ⟨catalog, tableEntries, indexEntries, catalogRead, tableFilter,
      indexFilter, tables, indexes, indexMetadata, separation⟩
  refine .intro catalog catalogRead ?_ ?_
  · rw [tableFilter]
    exact (tables.databaseTablesDecode state.tables_eq).mapM
  · rw [indexFilter]
    exact applyIndexesForOpen_of_index_certificates source state.database
      indexEntries indexes.decode indexMetadata

theorem DatabaseOnSource.decode
    {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.State}
    (physical : DatabaseOnSource source state) :
    CoreDecode.decodeFromPageSource source =
      some state.database.canonicalize :=
  physical.pageSourceRepresents.decode

/-- Representation depends on the logical database and table states, not on
the allocator watermark or freelist bookkeeping stored beside them.  This is
the proof bridge from a bulk-built state to the live retained state, whose
`nextPage` is raised past every physical overflow and index page. -/
def DatabaseOnSource.restate
    {source : CoreDecode.PageSource}
    {before after : CoreChunkPageState.State}
    (physical : DatabaseOnSource source before)
    (databaseEq : after.database = before.database)
    (tablesEq : after.tables = before.tables) :
    DatabaseOnSource source after := by
  rcases physical.components with
    ⟨catalog, tableEntries, indexEntries, catalogRead, tableFilter,
      indexFilter, tables, indexes, metadata, separation⟩
  refine ⟨⟨catalog, tableEntries, indexEntries, catalogRead, tableFilter,
    indexFilter, ?_, ?_, ?_, ?_⟩⟩
  · simpa [tablesEq] using tables
  · simpa [databaseEq] using indexes
  · simpa [databaseEq] using metadata
  · simpa [tablesEq] using separation

/-- Database-wide ordinary-delta composition.  The table and catalog parts
are derived from the live delta builder; catalog metadata and table/index page
separation are transported explicitly.  The storage-image specialization
below discharges both callbacks from exact ownership and page provenance. -/
def DatabaseOnSource.updateState
    {oldSource newSource : CoreDecode.PageSource}
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (physical : DatabaseOnSource oldSource state)
    (allocation : state.AllocationWellFormed)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (catalogPreserved : ∀ catalog,
      (oldSource.readPage 1 >>= CoreDecode.decodeCatalogForOpen = some catalog) →
      (newSource.readPage 1 >>= CoreDecode.decodeCatalogForOpen = some catalog))
    (retained : ∀ (old : CoreChunkPageState.TableState)
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      TableOnSource oldSource old →
        TableOnSource newSource (old.retarget table equivalent))
    (changed : TableOnSource newSource delta.table.after)
    (indexesPreserved : ∀ entries,
      IndexMetadataGroups state.database.tables entries →
      IndexGroupsOnSource oldSource
          state.database.tables entries →
      TablePagesBeforeIndexRoots state.tables entries →
        IndexGroupsOnSource newSource
          database.tables entries)
    (separationPreserved : ∀ entries,
      IndexMetadataGroups state.database.tables entries →
      TablePagesBeforeIndexRoots state.tables entries →
      TablePagesBeforeIndexRoots delta.after.tables entries) :
    DatabaseOnSource newSource delta.after := by
  rcases physical.components with
    ⟨catalog, tableEntries, indexEntries, catalogRead, tableFilter,
      indexFilter, tables, indexes, metadata, separation⟩
  have oldTableEntries := tables.entries_eq
  rw [oldTableEntries] at tables
  have newTables := TablesOnSource.updateState updated tables retained changed
  have encodedCatalog := CoreChunkPageDelta.updateState?_catalogEntries
    allocation updated
  have decodedCatalog := congrArg
    (List.map CoreDecode.CatalogEntry.ofEncoded) encodedCatalog
  have decodedCatalog' :
      delta.after.tables.map (fun table => CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry table)) =
      state.tables.map (fun table => CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry table)) := by
    simpa only [List.map_map, Function.comp_def] using decodedCatalog
  have tableEntriesExact :
      delta.after.tables.map (fun table => CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry table)) = tableEntries :=
    decodedCatalog'.trans oldTableEntries.symm
  rw [tableEntriesExact] at newTables
  have metadataAlignment := CoreChunkPageDelta.updateState?_metadataAligned updated
  rw [state.tables_eq] at metadataAlignment
  have newMetadata := metadata.retarget metadataAlignment
  have endpoints := CoreChunkPageDelta.updateState?_endpoints updated
  refine ⟨⟨catalog, tableEntries, indexEntries,
    catalogPreserved catalog catalogRead, tableFilter, indexFilter, newTables,
    ?_, ?_, separationPreserved indexEntries metadata separation⟩⟩
  · simpa [endpoints.2] using
      indexesPreserved indexEntries metadata indexes separation
  · simpa [endpoints.2] using newMetadata

/-- Complete ordinary-delta preservation for databases with no declared
secondary/implicit indexes.  Here the physical-index callback disappears:
catalog metadata proves the index-entry partition is empty, so no page can be
silently treated as an index. -/
def DatabaseOnSource.updateStateIndexless
    {oldSource newSource : CoreDecode.PageSource}
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (physical : DatabaseOnSource oldSource state)
    (allocation : state.AllocationWellFormed)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (indexless : ∀ table ∈ database.tables, table.indexes = [])
    (catalogPreserved : ∀ catalog,
      (oldSource.readPage 1 >>= CoreDecode.decodeCatalogForOpen = some catalog) →
      (newSource.readPage 1 >>= CoreDecode.decodeCatalogForOpen = some catalog))
    (retained : ∀ (old : CoreChunkPageState.TableState)
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      TableOnSource oldSource old →
        TableOnSource newSource (old.retarget table equivalent))
    (changed : TableOnSource newSource delta.table.after) :
    DatabaseOnSource newSource delta.after := by
  refine physical.updateState allocation updated catalogPreserved retained
    changed ?_ ?_
  · intro entries metadata indexes separation
    have metadataAlignment :=
      CoreChunkPageDelta.updateState?_metadataAligned updated
    rw [state.tables_eq] at metadataAlignment
    have newMetadata := metadata.retarget metadataAlignment
    have entriesEmpty := newMetadata.entries_nil_of_indexless indexless
    subst entries
    exact IndexGroupsOnSource.indexless newSource database.tables
  · intro entries metadata separation
    have metadataAlignment :=
      CoreChunkPageDelta.updateState?_metadataAligned updated
    rw [state.tables_eq] at metadataAlignment
    have newMetadata := metadata.retarget metadataAlignment
    have entriesEmpty := newMetadata.entries_nil_of_indexless indexless
    subst entries
    intro pageId pageMember entry entryMember
    simp at entryMember

end CoreLocalizedRepresentation

end SQLeanite
