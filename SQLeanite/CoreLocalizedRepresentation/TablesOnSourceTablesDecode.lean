import SQLeanite.CoreLocalizedRepresentation.TableOnSource
import SQLeanite.CorePageCodec.EncodeBulkFromState

namespace SQLeanite
namespace CoreLocalizedRepresentation

/-- Collapse the stronger physical-layout invariant into the exact table
decoder equations consumed by the durability certificate. -/
theorem TablesOnSource.tablesDecode
    {source : CoreDecode.PageSource}
    {entries : List CoreDecode.CatalogEntry}
    {states : List CoreChunkPageState.TableState}
    (physical : TablesOnSource source entries states) :
    TablesDecode source entries (states.map (fun state => state.table)) := by
  induction physical with
  | nil => exact .nil
  | cons entryExact head tail induction =>
      subst entryExact
      exact .cons head.decode induction

theorem TablesOnSource.databaseTablesDecode
    {source : CoreDecode.PageSource}
    {entries : List CoreDecode.CatalogEntry}
    {states : List CoreChunkPageState.TableState}
    {database : Core.Database}
    (physical : TablesOnSource source entries states)
    (aligned : states.map (fun state => state.table) = database.tables) :
    TablesDecode source entries database.tables := by
  rw [← aligned]
  exact physical.tablesDecode

/-- The store-owned multi-table encoder establishes the stronger physical
layout invariant table by table.  This is the bulk-image base case for later
localized-preservation proofs. -/
theorem TablesOnSource.ofEncodedTables
    (source : CoreDecode.PageSource) :
    ∀ (nextOverflow : Nat)
      (tables : List CoreChunkPageState.TableState)
      (encoding : CorePageCodec.OverflowEncoding),
      CorePageCodec.encodeChunkTablesWithOverflow nextOverflow tables =
        some encoding →
      CorePageCodec.PageSourceContains source encoding.treePages →
      CoreDecode.ReadsPagesFrom source nextOverflow encoding.overflowPages →
      0 < nextOverflow →
      nextOverflow + encoding.overflowPages.length < 2 ^ 32 →
      encoding.overflowPages.length < source.pageCount + 1 →
      (∀ table ∈ tables,
        table.tree.root.erase.height < source.pageCount + 1) →
      TablesOnSource source
        (tables.map fun table => CoreDecode.CatalogEntry.ofEncoded
          (CorePageCodec.chunkTableCatalogEntry table)) tables
  | _, [], encoding, encoded, _, _, _, _, _, _ => by
      simp only [CorePageCodec.encodeChunkTablesWithOverflow,
        Option.some.injEq] at encoded
      subst encoding
      exact .nil
  | nextOverflow, table :: tables, encoding, encoded, treeContains,
      overflowContains, nextPositive, pageBound, fuelBound, heights => by
      simp only [CorePageCodec.encodeChunkTablesWithOverflow,
        Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : CorePageCodec.encodeChunkNodeWithOverflow
          table.table.schema table.tree.root nextOverflow with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : CorePageCodec.encodeChunkTablesWithOverflow
            head.nextPage tables with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encoding
          have headTreeContains : CorePageCodec.PageSourceContains source
              head.treePages := by
            intro numbered member
            exact treeContains numbered (by simp [member])
          have tailTreeContains : CorePageCodec.PageSourceContains source
              tail.treePages := by
            intro numbered member
            exact treeContains numbered (by simp [member])
          have headOverflowContains : CoreDecode.ReadsPagesFrom source
              nextOverflow head.overflowPages :=
            CoreDecode.ReadsPagesFrom.left overflowContains
          have tailOverflowAt := CoreDecode.ReadsPagesFrom.right overflowContains
          have headNext := CorePageCodec.encodeChunkNodeWithOverflow_nextPage
            table.table.schema table.tree.root nextOverflow head headResult
          have tailOverflowContains : CoreDecode.ReadsPagesFrom source
              head.nextPage tail.overflowPages := by
            simpa [headNext] using tailOverflowAt
          have headPhysical : TableOnSource source table := {
            nextOverflow
            encoding := head
            encoded := headResult
            treeContains := headTreeContains
            overflowContains := headOverflowContains
            heightBound := heights table (by simp)
            nextPositive
            pageBound := by
              simp only [List.length_append] at pageBound
              omega
            fuelBound := by
              simp only [List.length_append] at fuelBound
              omega }
          have tailPhysical := ofEncodedTables source head.nextPage tables tail
            tailResult tailTreeContains tailOverflowContains (by
              rw [headNext]
              omega) (by
              simp only [List.length_append] at pageBound
              rw [headNext]
              omega) (by
              simp only [List.length_append] at fuelBound
              omega) (fun candidate member => heights candidate (by
                simp [member]))
          exact .cons rfl headPhysical tailPhysical

/-- A successful bulk image establishes the full per-table physical-layout
invariant over any page source that contains its active tail.  The returned
state is exactly the proof-carrying state built by the live bulk encoder. -/
theorem exists_tablesOnSource_encodeBulk_in
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image)
    (source : CoreDecode.PageSource)
    (activeTailReads : CoreDecode.ReadsPagesFrom source 2 image.pages.tail)
    (enoughPages : image.pageCount ≤ source.pageCount) :
    ∃ state : CoreChunkPageState.State,
      CoreChunkPageState.State.build? database = some state ∧
      TablesOnSource source
        (state.tables.map fun table => CoreDecode.CatalogEntry.ofEncoded
          (CorePageCodec.chunkTableCatalogEntry table)) state.tables := by
  unfold CorePageCodec.encodeBulk CorePageCodec.encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
    simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
    cases tableResult : CorePageCodec.encodeChunkTablesWithOverflow
        state.nextPage state.tables with
    | none => simp [tableResult] at encoded
    | some tableEncoding =>
      simp only [tableResult] at encoded
      cases indexResult : CoreOverflow.encodeIndexTableGroups
          tableEncoding.nextPage database.tables with
      | none => simp [indexResult] at encoded
      | some indexEncodings =>
        simp only [indexResult] at encoded
        split at encoded
        next countBound =>
          let entries := state.tables.map CorePageCodec.chunkTableCatalogEntry ++
            CoreOverflow.indexEntriesOf indexEncodings
          let treePages := tableEncoding.treePages.map
            CorePageCodec.NumberedPage.page
          let indexPages := CoreOverflow.indexPagesOf indexEncodings
          let remaining := treePages ++ tableEncoding.overflowPages ++ indexPages
          let count : FileFormat.U32Value := ⟨1 + remaining.length, by
            change 1 + remaining.length < 2 ^ 32
            simp only [remaining, treePages, indexPages]
            omega⟩
          change (do
            let schema ← CoreFile.schemaPageForEntries? entries count
            some ⟨database, schema :: remaining⟩) = some image at encoded
          cases schemaResult : CoreFile.schemaPageForEntries? entries count with
          | none => simp [schemaResult] at encoded
          | some schemaPage =>
            rw [schemaResult] at encoded
            simp only [Option.bind_eq_bind, Option.bind,
              Option.some.injEq] at encoded
            subst image
            obtain ⟨tablePageCount, stateNext, statePages⟩ :=
              CoreChunkPageState.State.build?_interval stateResult
            have treeNumbers :=
              CorePageCodec.encodeChunkTablesWithOverflow_pageNumbers
                state.nextPage state.tables tableEncoding tableResult
            rw [statePages] at treeNumbers
            have treeLength : treePages.length = tablePageCount := by
              have lengths := congrArg List.length treeNumbers
              simpa [treePages] using lengths
            have tableNext :=
              CorePageCodec.encodeChunkTablesWithOverflow_nextPage
                state.nextPage state.tables tableEncoding tableResult
            have sourceCountLower :
                1 + remaining.length ≤ source.pageCount := by
              simpa [CoreFile.Image.pageCount, Nat.add_comm] using enoughPages
            have remainingReads : CoreDecode.ReadsPagesFrom source 2
                remaining := by
              simpa using activeTailReads
            have treeReads : CoreDecode.ReadsPagesFrom source 2 treePages := by
              apply CoreDecode.ReadsPagesFrom.left
                (right := tableEncoding.overflowPages ++ indexPages)
              simpa [remaining, List.append_assoc] using remainingReads
            have treeContains : CorePageCodec.PageSourceContains source
                tableEncoding.treePages := by
              apply CorePageCodec.PageSourceContains.ofReadsRange source 2
              · have numberedLength : tableEncoding.treePages.length =
                    tablePageCount := by
                  simpa [treePages] using treeLength
                rw [numberedLength]
                exact treeNumbers
              · exact treeReads
            have overflowReads : CoreDecode.ReadsPagesFrom source
                state.nextPage tableEncoding.overflowPages := by
              have afterTree := CoreDecode.ReadsPagesFrom.right
                (left := treePages)
                (right := tableEncoding.overflowPages ++ indexPages)
                (by simpa [remaining, List.append_assoc] using remainingReads)
              have overflow := CoreDecode.ReadsPagesFrom.left afterTree
              simpa [stateNext, treeLength, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using overflow
            have tablePagesWithin : tablePageCount ≤ remaining.length := by
              simp only [remaining, List.length_append]
              rw [treeLength]
              omega
            have tableHeights : ∀ table ∈ state.tables,
                table.tree.root.erase.height < source.pageCount + 1 := by
              intro table member
              have height := RecursiveBPlusTree.Node.height_lt_pageCount
                table.tree.root.erase
              have pageCount := PersistentPageTree.Node.pageIds_length
                table.tree.root
              have included :=
                CoreChunkPageState.TableState.pageIds_length_le_tablePageIds
                  member
              unfold CoreChunkPageState.TableState.pageIds at included
              rw [statePages] at included
              simp only [List.length_range'] at included
              omega
            refine ⟨state, rfl, ?_⟩
            exact TablesOnSource.ofEncodedTables source state.nextPage
              state.tables tableEncoding tableResult treeContains overflowReads
              (by rw [stateNext]; omega) (by
                rw [stateNext]
                change 1 + remaining.length + 1 < 2 ^ 32 at countBound
                simp only [remaining, List.length_append, List.length_map]
                  at countBound
                omega) (by
                  simp only [remaining, List.length_append] at sourceCountLower
                  omega) tableHeights
        next => contradiction

theorem TablesDecode.mapM
    {source : CoreDecode.PageSource}
    {entries : List CoreDecode.CatalogEntry} {tables : List Core.Table}
    (decoded : TablesDecode source entries tables) :
    entries.mapM (CoreDecode.decodeTableFrom source) =
      some (tables.map Core.Table.withoutIndexes) := by
  induction decoded with
  | nil => rfl
  | cons head tail induction =>
      simp [head, induction]

/-- Exact physical-index certificates aligned with one table's contiguous
canonical catalog run.  `decodeIndexSubtreeFrom` includes promoted interior
entries, so this relation cannot accidentally certify a leaf-only abstraction. -/
inductive IndexesDecode (source : CoreDecode.PageSource)
    (table : Core.Table) : List CoreDecode.CatalogEntry → Prop where
  | nil : IndexesDecode source table []
  | cons {entry : CoreDecode.CatalogEntry}
      {entries : List CoreDecode.CatalogEntry} {index : Core.Index}
      (sameTable : entry.table = table.schema.name)
      (metadata : CoreDecode.decodeCanonicalIndex table.schema
        table.schema.name entry = some index)
      (physical : CoreDecode.decodeIndexSubtreeFrom source
        (source.pageCount + 1) entry.rootPage =
          some (CoreDecode.expectedIndexEntries table index))
      (tail : IndexesDecode source table entries) :
      IndexesDecode source table (entry :: entries)

/-- Per-index exactness is precisely what the generated-file validator needs;
no complete index re-encoding or fallback comparison is required. -/
theorem IndexesDecode.validateForTable
    {source : CoreDecode.PageSource} {table : Core.Table}
    {entries : List CoreDecode.CatalogEntry}
    (decoded : IndexesDecode source table entries)
    (suffix : List CoreDecode.CatalogEntry)
    (boundary : ∀ entry ∈ suffix,
      entry.table ≠ table.schema.name) :
    CoreDecode.validateCanonicalIndexesForTableFrom source table
      (entries ++ suffix) = some suffix := by
  induction decoded with
  | nil =>
      simp only [List.nil_append]
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          unfold CoreDecode.validateCanonicalIndexesForTableFrom
          rw [dif_neg (boundary entry (by simp))]
  | cons sameTable metadata physical tail induction =>
      simp only [List.cons_append]
      unfold CoreDecode.validateCanonicalIndexesForTableFrom
      rw [dif_pos sameTable, metadata]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [physical]
      simp only
      rw [dif_pos True.intro]
      exact induction

/-- Canonical index runs for all tables, retaining the catalog partition that
the executable validator consumes. -/
inductive IndexGroupsDecode (source : CoreDecode.PageSource) :
    List Core.Table → List CoreDecode.CatalogEntry → Prop where
  | nil : IndexGroupsDecode source [] []
  | cons {table : Core.Table} {tables : List Core.Table}
      {entries remaining : List CoreDecode.CatalogEntry}
      (current : IndexesDecode source table entries)
      (boundary : ∀ entry ∈ remaining,
        entry.table ≠ table.schema.name)
      (tail : IndexGroupsDecode source tables remaining) :
      IndexGroupsDecode source (table :: tables) (entries ++ remaining)

/-- Byte-owning certificate for one physical index.  Unlike `IndexesDecode`,
this retains the exact encoder run and every page it owns.  The reference
table may predate later row mutations; `logical` states precisely why those
same bytes still denote the current table's index image. -/
def IndexOnSource (source : CoreDecode.PageSource)
    (table : Core.Table) (entry : CoreDecode.CatalogEntry)
    (index : Core.Index) : Prop :=
  ∃ (reference : Core.Table) (encoding : CoreOverflow.IndexEncoding),
    entry.table = table.schema.name ∧
    entry.rootPage = encoding.rootPage ∧
    CoreDecode.decodeCanonicalIndex table.schema table.schema.name entry =
      some index ∧
    index ∈ table.indexes ∧
    CoreOverflow.encodeIndex encoding.rootPage reference index =
      some encoding ∧
    CoreDecode.ReadsPagesFrom source encoding.rootPage encoding.pages ∧
    0 < encoding.rootPage ∧
    encoding.rootPage + encoding.pages.length < 2 ^ 32 ∧
    encoding.rootPage + encoding.pages.length ≤ source.pageCount + 1 ∧
    CoreDecode.expectedIndexEntries reference index =
      CoreDecode.expectedIndexEntries table index

/-- Exact owned index runs for one table, in catalog order. -/
inductive IndexesOnSource (source : CoreDecode.PageSource)
    (table : Core.Table) : List CoreDecode.CatalogEntry → Prop where
  | nil : IndexesOnSource source table []
  | cons {entry : CoreDecode.CatalogEntry}
      {entries : List CoreDecode.CatalogEntry} {index : Core.Index}
      (head : IndexOnSource source table entry index)
      (tail : IndexesOnSource source table entries) :
      IndexesOnSource source table (entry :: entries)

/-- Database-order grouping of the byte-owning index runs. -/
inductive IndexGroupsOnSource (source : CoreDecode.PageSource) :
    List Core.Table → List CoreDecode.CatalogEntry → Prop where
  | nil : IndexGroupsOnSource source [] []
  | cons {table : Core.Table} {tables : List Core.Table}
      {entries remaining : List CoreDecode.CatalogEntry}
      (current : IndexesOnSource source table entries)
      (boundary : ∀ entry ∈ remaining,
        entry.table ≠ table.schema.name)
      (tail : IndexGroupsOnSource source tables remaining) :
      IndexGroupsOnSource source (table :: tables) (entries ++ remaining)

theorem IndexOnSource.physical
    {source : CoreDecode.PageSource} {table : Core.Table}
    {entry : CoreDecode.CatalogEntry} {index : Core.Index}
    (owned : IndexOnSource source table entry index) :
    CoreDecode.decodeIndexSubtreeFrom source (source.pageCount + 1)
        entry.rootPage =
      some (CoreDecode.expectedIndexEntries table index) := by
  rcases owned with ⟨reference, encoding, sameTable, sameRoot, metadata,
    member, encoded, reads, rootPositive, pageBound, withinSource, logical⟩
  rw [sameRoot]
  have decoded := CoreDecode.decodeIndexSubtreeFrom_encodeIndex source
    encoded reads rootPositive pageBound withinSource
  calc
    _ = some (CoreDecode.expectedIndexEntries reference index) := by
      simpa only [CoreDecode.expectedIndexEntries] using decoded
    _ = some (CoreDecode.expectedIndexEntries table index) :=
      congrArg some logical

theorem IndexesOnSource.decode
    {source : CoreDecode.PageSource} {table : Core.Table}
    {entries : List CoreDecode.CatalogEntry}
    (owned : IndexesOnSource source table entries) :
    IndexesDecode source table.withoutIndexes entries := by
  induction owned with
  | nil => exact .nil
  | cons head tail induction =>
      rcases head with ⟨reference, encoding, sameTable, sameRoot, metadata,
        member, encoded, reads, rootPositive, pageBound, withinSource, logical⟩
      refine .cons (by simpa using sameTable) (by simpa using metadata) ?_ induction
      simpa only [CoreDecode.expectedIndexEntries_withoutIndexes] using
        IndexOnSource.physical ⟨reference, encoding, sameTable, sameRoot,
          metadata, member, encoded, reads, rootPositive, pageBound,
          withinSource, logical⟩

theorem IndexGroupsOnSource.decode
    {source : CoreDecode.PageSource} {tables : List Core.Table}
    {entries : List CoreDecode.CatalogEntry}
    (owned : IndexGroupsOnSource source tables entries) :
    IndexGroupsDecode source (tables.map Core.Table.withoutIndexes) entries := by
  induction owned with
  | nil => exact .nil
  | cons current boundary tail induction =>
      simpa only [List.map_cons] using
        IndexGroupsDecode.cons current.decode boundary induction

def TableIndexImageEq (before after : Core.Table) : Prop :=
  before.schema = after.schema ∧
  before.indexes = after.indexes ∧
  ∀ index ∈ before.indexes,
    CoreDecode.expectedIndexEntries before index =
      CoreDecode.expectedIndexEntries after index

inductive TablesIndexImagesAligned :
    List Core.Table → List Core.Table → Prop where
  | nil : TablesIndexImagesAligned [] []
  | cons {before after : Core.Table} {befores afters : List Core.Table}
      (head : TableIndexImageEq before after)
      (tail : TablesIndexImagesAligned befores afters) :
      TablesIndexImagesAligned (before :: befores) (after :: afters)

theorem expectedIndexEntries_eq_of_rows_eq
    {before after : Core.Table} (index : Core.Index)
    (rows : before.rows = after.rows) :
    CoreDecode.expectedIndexEntries before index =
      CoreDecode.expectedIndexEntries after index := by
  unfold CoreDecode.expectedIndexEntries CoreFile.sortedIndexRows
    CoreFile.indexValuesInteger CoreFile.indexValuesText
  rw [rows]

theorem TableIndexImageEq.ofEquiv {before after : Core.Table}
    (equivalent : before.Equiv after) : TableIndexImageEq before after := by
  exact ⟨equivalent.schema_eq, equivalent.indexes_eq,
    fun index _ => expectedIndexEntries_eq_of_rows_eq index equivalent.rows_eq⟩

private theorem map_index_entries_eq_value
    (indexes : List Core.Index)
    (left right : Core.Index → List CoreDecode.IndexEntry)
    (equal : indexes.map (fun index => (index, left index)) =
      indexes.map (fun index => (index, right index))) :
    ∀ index ∈ indexes, left index = right index := by
  induction indexes with
  | nil => simp
  | cons head tail induction =>
      simp only [List.map_cons, List.cons.injEq] at equal
      intro index member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact congrArg Prod.snd equal.1
      · exact induction equal.2 index member

theorem TableIndexImageEq.ofDelta
    (delta : CoreChunkPageDelta.TableDelta)
    (sufficient : delta.tablePagesSufficient = true) :
    TableIndexImageEq delta.before.table delta.after.table := by
  have metadata := delta.tablePagesSufficient_metadata sufficient
  refine ⟨metadata.1, metadata.2.1, ?_⟩
  have image := delta.tablePagesSufficient_indexImage sufficient
  unfold CoreChunkPageDelta.indexImage at image
  rw [metadata.2.1] at image
  intro index member
  apply map_index_entries_eq_value delta.after.table.indexes
    (fun candidate =>
      CoreDecode.expectedIndexEntries delta.before.table candidate)
    (fun candidate =>
      CoreDecode.expectedIndexEntries delta.after.table candidate) image index
  rw [← metadata.2.1]
  exact member

end CoreLocalizedRepresentation

end SQLeanite
