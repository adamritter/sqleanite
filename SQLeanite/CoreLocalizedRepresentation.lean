import SQLeanite.CorePageCodec
import SQLeanite.CorePageSource
import SQLeanite.CoreChunkPageDelta

namespace SQLeanite
namespace CoreLocalizedRepresentation

/-!
# Local page deltas preserve table decoding

These lemmas isolate the two physical facts needed by the live localized
writer.  A changed encoded page is read from its exact write, and an omitted
page is read from the represented old image.  The resulting containment
certificate feeds the existing recursive table-decoder refinement directly;
there is no decode-and-compare admission check.
-/

/-- Physical representation of one proof-carrying table state.  It records
both the identified tree pages and the separately allocated overflow run; the
decoder bounds are retained explicitly because they are exactly the facts a
page-local update must preserve. -/
structure TableOnSource (source : CoreDecode.PageSource)
    (state : CoreChunkPageState.TableState) where
  nextOverflow : Nat
  encoding : CorePageCodec.OverflowEncoding
  encoded : CorePageCodec.encodeChunkNodeWithOverflow state.table.schema
    state.tree.root nextOverflow = some encoding
  treeContains : CorePageCodec.PageSourceContains source encoding.treePages
  overflowContains : CoreDecode.ReadsPagesFrom source nextOverflow
    encoding.overflowPages
  heightBound : state.tree.root.erase.height < source.pageCount + 1
  nextPositive : 0 < nextOverflow
  pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32
  fuelBound : encoding.overflowPages.length < source.pageCount + 1

theorem TableOnSource.decode
    {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.TableState}
    (physical : TableOnSource source state) :
    CoreDecode.decodeTableFrom source
      (CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry state)) =
      some state.table.withoutIndexes := by
  exact CorePageCodec.decodeTableFrom_encodeChunkNodeWithOverflow source state
    physical.nextOverflow physical.encoding physical.encoded
    physical.treeContains physical.overflowContains physical.heightBound
    physical.nextPositive physical.pageBound physical.fuelBound

/-- Inline tables have exactly the tree-page encoding consumed by the live
delta builder; the general overflow encoder contributes no hidden byte pass. -/
theorem TableOnSource.inlineEncoded
    {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.TableState}
    (physical : TableOnSource source state)
    (inline : physical.encoding.overflowPages = []) :
    CorePageCodec.encodeChunkNode state.table.schema state.tree.root =
      some physical.encoding.treePages :=
  CorePageCodec.encodeChunkNodeWithOverflow_noOverflow state.table.schema
    state.tree.root physical.nextOverflow physical.encoding physical.encoded
    inline

/-- Preserve a table certificate across a source change after separately
re-establishing its exact tree and overflow bytes.  Page-count growth is the
only numeric fact needed to transport both recursive decoder bounds. -/
def TableOnSource.transport
    {oldSource newSource : CoreDecode.PageSource}
    {state : CoreChunkPageState.TableState}
    (physical : TableOnSource oldSource state)
    (pageCountGrows : oldSource.pageCount ≤ newSource.pageCount)
    (treeContains : CorePageCodec.PageSourceContains newSource
      physical.encoding.treePages)
    (overflowContains : CoreDecode.ReadsPagesFrom newSource
      physical.nextOverflow physical.encoding.overflowPages) :
    TableOnSource newSource state := {
  nextOverflow := physical.nextOverflow
  encoding := physical.encoding
  encoded := physical.encoded
  treeContains
  overflowContains
  heightBound := Nat.lt_of_lt_of_le physical.heightBound
    (Nat.add_le_add_right pageCountGrows 1)
  nextPositive := physical.nextPositive
  pageBound := physical.pageBound
  fuelBound := Nat.lt_of_lt_of_le physical.fuelBound
    (Nat.add_le_add_right pageCountGrows 1) }

/-- Secondary-index metadata may change while the table schema, rows, and
physical tree remain identical.  Retargeting the logical table therefore
retargets its physical certificate without touching or revalidating bytes. -/
def TableOnSource.retarget
    {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.TableState}
    (physical : TableOnSource source state)
    (table : Core.Table) (equivalent : state.table.Equiv table) :
    TableOnSource source (state.retarget table equivalent) := by
  have schemaEq := equivalent.schema_eq
  refine {
    nextOverflow := physical.nextOverflow
    encoding := physical.encoding
    encoded := ?_
    treeContains := physical.treeContains
    overflowContains := physical.overflowContains
    heightBound := ?_
    nextPositive := physical.nextPositive
    pageBound := physical.pageBound
    fuelBound := physical.fuelBound }
  · simpa [CoreChunkPageState.TableState.retarget, schemaEq] using
      physical.encoded
  · simpa [CoreChunkPageState.TableState.retarget] using
      physical.heightBound

/-- Database-order physical table certificates.  Catalog identity is part of
the relation, so a certificate cannot be silently attached to the wrong table
or root page. -/
inductive TablesOnSource (source : CoreDecode.PageSource) :
    List CoreDecode.CatalogEntry →
      List CoreChunkPageState.TableState → Prop where
  | nil : TablesOnSource source [] []
  | cons {entry : CoreDecode.CatalogEntry}
      {entries : List CoreDecode.CatalogEntry}
      {state : CoreChunkPageState.TableState}
      {states : List CoreChunkPageState.TableState}
      (entryExact : entry = CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry state))
      (head : TableOnSource source state)
      (tail : TablesOnSource source entries states) :
      TablesOnSource source (entry :: entries) (state :: states)

/-- If alignment reports no changed table, every result is a byte-preserving
retarget of its corresponding input state.  The caller supplies only the
source-transport rule; the recursive alignment proof fixes the database and
catalog order. -/
theorem TablesOnSource.alignTables_none
    {oldSource newSource : CoreDecode.PageSource}
    (retained : ∀ (state : CoreChunkPageState.TableState)
      (table : Core.Table) (equivalent : state.table.Equiv table),
      TableOnSource oldSource state →
        TableOnSource newSource (state.retarget table equivalent)) :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table}
      {aligned : CoreChunkPageDelta.AlignedTables target}
      {entries : List CoreDecode.CatalogEntry},
      CoreChunkPageDelta.alignTables? nextPage states target = some aligned →
      aligned.delta = none →
      TablesOnSource oldSource entries states →
      TablesOnSource newSource
        (aligned.tables.map fun state => CoreDecode.CatalogEntry.ofEncoded
          (CorePageCodec.chunkTableCatalogEntry state)) aligned.tables
  | _, [], target, aligned, entries, success, noChange, physical => by
      cases target with
      | nil =>
          simp only [CoreChunkPageDelta.alignTables?, Option.some.injEq]
            at success
          subst aligned
          cases physical
          exact .nil
      | cons _ _ => simp [CoreChunkPageDelta.alignTables?] at success
  | nextPage, state :: states, target, aligned, entries, success, noChange,
      physical => by
      cases target with
      | nil => simp [CoreChunkPageDelta.alignTables?] at success
      | cons table tables =>
        cases physical with
        | cons entryExact head tail =>
          unfold CoreChunkPageDelta.alignTables? at success
          split at success
          next equivalent =>
            rcases Option.bind_eq_some.mp success with
              ⟨tailAligned, tailResult, success⟩
            simp only [Option.some.injEq] at success
            subst aligned
            have tailPhysical := alignTables_none retained tailResult noChange tail
            exact .cons rfl (retained state table equivalent head) tailPhysical
          next =>
            split at success
            next => contradiction
            next changed changedResult =>
              split at success
              next => contradiction
              next tailAligned tailResult =>
                split at success
                next onlyChange =>
                  simp only [Option.some.injEq] at success
                  subst aligned
                  simp at noChange
                next => contradiction

/-- A successful one-table alignment transports every unchanged physical
table and installs the supplied exact certificate for the changed table.
This is the table-list frame theorem used by localized commits. -/
theorem TablesOnSource.alignTables_changed
    {oldSource newSource : CoreDecode.PageSource}
    (retained : ∀ (state : CoreChunkPageState.TableState)
      (table : Core.Table) (equivalent : state.table.Equiv table),
      TableOnSource oldSource state →
        TableOnSource newSource (state.retarget table equivalent))
    {changed : CoreChunkPageDelta.TableDelta}
    (changedPhysical : TableOnSource newSource changed.after) :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table}
      {aligned : CoreChunkPageDelta.AlignedTables target}
      {entries : List CoreDecode.CatalogEntry},
      CoreChunkPageDelta.alignTables? nextPage states target = some aligned →
      aligned.delta = some changed →
      TablesOnSource oldSource entries states →
      TablesOnSource newSource
        (aligned.tables.map fun state => CoreDecode.CatalogEntry.ofEncoded
          (CorePageCodec.chunkTableCatalogEntry state)) aligned.tables
  | _, [], target, aligned, entries, success, selected, physical => by
      cases target <;> simp [CoreChunkPageDelta.alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, state :: states, target, aligned, entries, success, selected,
      physical => by
      cases target with
      | nil => simp [CoreChunkPageDelta.alignTables?] at success
      | cons table tables =>
        cases physical with
        | cons entryExact head tail =>
          unfold CoreChunkPageDelta.alignTables? at success
          split at success
          next equivalent =>
            rcases Option.bind_eq_some.mp success with
              ⟨tailAligned, tailResult, success⟩
            simp only [Option.some.injEq] at success
            subst aligned
            have tailPhysical := alignTables_changed retained changedPhysical
              tailResult selected tail
            exact .cons rfl (retained state table equivalent head) tailPhysical
          next =>
            split at success
            next => contradiction
            next headDelta headResult =>
              split at success
              next => contradiction
              next tailAligned tailResult =>
                split at success
                next onlyChange =>
                  simp only [Option.some.injEq] at success
                  subst aligned
                  have equal : headDelta = changed :=
                    Option.some.inj selected
                  subst headDelta
                  have tailNone : tailAligned.delta = none := by
                    cases tailResultValue : tailAligned.delta with
                    | none => rfl
                    | some value => simp [tailResultValue] at onlyChange
                  have tailPhysical := alignTables_none retained tailResult
                    tailNone tail
                  exact .cons rfl changedPhysical tailPhysical
                next => contradiction

/-- Database-state specialization of `alignTables_changed` for the candidate
used by changed-index writers.  All list positioning and frame conditions are
derived from the successful live delta builder. -/
theorem TablesOnSource.updateStateCandidate
    {oldSource newSource : CoreDecode.PageSource}
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (updated : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (physical : TablesOnSource oldSource
      (state.tables.map fun table => CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry table)) state.tables)
    (retained : ∀ (old : CoreChunkPageState.TableState)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      TableOnSource oldSource old →
        TableOnSource newSource (old.retarget table equivalent))
    (changed : TableOnSource newSource delta.table.after) :
    TablesOnSource newSource
      (delta.after.tables.map fun table => CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry table)) delta.after.tables := by
  rcases CoreChunkPageDelta.updateStateCandidate?_alignment updated with
    ⟨aligned, alignedResult, alignedTables, selected⟩
  have transported := alignTables_changed retained changed alignedResult
    selected physical
  rw [alignedTables] at transported
  exact transported

/-- The ordinary table-only localized path is the same physical frame theorem
with its stronger unchanged-index premise erased from the conclusion. -/
theorem TablesOnSource.updateState
    {oldSource newSource : CoreDecode.PageSource}
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (physical : TablesOnSource oldSource
      (state.tables.map fun table => CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry table)) state.tables)
    (retained : ∀ (old : CoreChunkPageState.TableState)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      TableOnSource oldSource old →
        TableOnSource newSource (old.retarget table equivalent))
    (changed : TableOnSource newSource delta.table.after) :
    TablesOnSource newSource
      (delta.after.tables.map fun table => CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry table)) delta.after.tables := by
  rcases CoreChunkPageDelta.updateState?_alignment updated with
    ⟨aligned, alignedResult, alignedTables, selected⟩
  have transported := alignTables_changed retained changed alignedResult
    selected physical
  rw [alignedTables] at transported
  exact transported

/-- Per-table physical decoder certificates, aligned with the table entries in
the SQLite catalog.  This is the list-level bridge from each local tree proof
to `PageSourceRepresents.tablesRead`. -/
inductive TablesDecode (source : CoreDecode.PageSource) :
    List CoreDecode.CatalogEntry → List Core.Table → Prop where
  | nil : TablesDecode source [] []
  | cons {entry : CoreDecode.CatalogEntry}
      {entries : List CoreDecode.CatalogEntry}
      {table : Core.Table} {tables : List Core.Table}
      (head : CoreDecode.decodeTableFrom source entry =
        some table.withoutIndexes)
      (tail : TablesDecode source entries tables) :
      TablesDecode source (entry :: entries) (table :: tables)

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
          rw [metadataEq.2] at current'
          exact .cons current'
            (by
              intro entry member same
              have nameEq : beforeTable.schema.name =
                  afterTable.schema.name := congrArg Core.Schema.name metadataEq.1
              exact boundary entry member (same.trans nameEq.symm))
            (IndexMetadataGroups.retarget aligned tail)

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
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry) indexes
  | _, [], encodings, _, encoded, _, _, _, _ => by
      simp only [List.map_nil, CoreOverflow.encodeIndexes,
        Option.some.injEq] at encoded
      subst encodings
      exact ⟨.nil, .nil⟩
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
          constructor
          · exact .cons (by
              change head.table.schema.name = table.schema.name
              rw [identity.1])
              metadata physical tailCertificates.1
          · exact .cons (by
              change head.table.schema.name = table.schema.name
              rw [identity.1])
              metadata tailCertificates.2

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
            CoreDecode.CatalogEntry.ofEncoded encoding.catalogEntry)
  | _, [], encodings, _, encoded, _, _, _, _ => by
      simp only [CoreOverflow.encodeIndexTableGroups,
        Option.some.injEq] at encoded
      subst encodings
      exact ⟨.nil, .nil⟩
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
          constructor
          · simpa only [List.map_cons, List.map_append] using
              IndexGroupsDecode.cons currentCertificates.1 boundary
                tailCertificates.1
          · simpa only [List.map_append] using
              IndexMetadataGroups.cons currentCertificates.2 boundary
                tailCertificates.2

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
        Core.Table.withoutIndexes_rows]
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
    IndexGroupsDecode source
      (state.database.tables.map Core.Table.withoutIndexes) indexEntries ∧
    IndexMetadataGroups state.database.tables indexEntries

theorem DatabaseOnSource.pageSourceRepresents
    {source : CoreDecode.PageSource}
    {state : CoreChunkPageState.State}
    (physical : DatabaseOnSource source state) :
    CoreDecode.PageSourceRepresents source state.database := by
  rcases physical.components with
    ⟨catalog, tableEntries, indexEntries, catalogRead, tableFilter,
      indexFilter, tables, indexes, indexMetadata⟩
  refine .intro catalog catalogRead ?_ ?_
  · rw [tableFilter]
    exact (tables.databaseTablesDecode state.tables_eq).mapM
  · rw [indexFilter]
    exact applyIndexesForOpen_of_index_certificates source state.database
      indexEntries indexes indexMetadata

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
      indexFilter, tables, indexes, metadata⟩
  refine ⟨⟨catalog, tableEntries, indexEntries, catalogRead, tableFilter,
    indexFilter, ?_, ?_, ?_⟩⟩
  · simpa [tablesEq] using tables
  · simpa [databaseEq] using indexes
  · simpa [databaseEq] using metadata

/-- The canonical bulk encoder establishes the complete physical state
invariant over any source which contains its emitted tail and reads its schema
page.  Unlike `PageSourceRepresents`, the result retains table-page ownership,
overflow intervals, and the exact promoted index groups needed by subsequent
localized-write proofs. -/
theorem exists_databaseOnSource_encodeBulk_in
    (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image)
    (source : CoreDecode.PageSource)
    (catalogRead :
      source.readPage 1 >>= CoreDecode.decodeCatalogForOpen =
        (CoreDecode.PageSource.ofList
          (image.pages.map CoreFile.Page.bytes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen)
    (activeTailReads : CoreDecode.ReadsPagesFrom source 2 image.pages.tail)
    (enoughPages : image.pageCount ≤ source.pageCount) :
    ∃ state : CoreChunkPageState.State,
      CoreChunkPageState.State.build? database = some state ∧
      DatabaseOnSource source state := by
  obtain ⟨baseState, baseBuilt, baseTables⟩ :=
    exists_tablesOnSource_encodeBulk_in database image encoded source
      activeTailReads enoughPages
  unfold CorePageCodec.encodeBulk CorePageCodec.encodeBulkFromState at encoded
  cases stateResult : CoreChunkPageState.State.build? database with
  | none => simp [stateResult] at encoded
  | some state =>
    simp only [stateResult, Option.bind_eq_bind, Option.bind] at encoded
    have stateEq : baseState = state := by
      rw [stateResult] at baseBuilt
      exact (Option.some.inj baseBuilt).symm
    subst baseState
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
          let tableEntries := state.tables.map
            CorePageCodec.chunkTableCatalogEntry
          let indexEntries := CoreOverflow.indexEntriesOf indexEncodings
          let entries := tableEntries ++ indexEntries
          let treePages := tableEncoding.treePages.map
            CorePageCodec.NumberedPage.page
          let indexPages := CoreOverflow.indexPagesOf indexEncodings
          let remaining := treePages ++ tableEncoding.overflowPages ++
            indexPages
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
            have indexReads : CoreDecode.ReadsPagesFrom source
                tableEncoding.nextPage indexPages := by
              have afterTree := CoreDecode.ReadsPagesFrom.right
                (left := treePages)
                (right := tableEncoding.overflowPages ++ indexPages)
                (by simpa [remaining, List.append_assoc] using remainingReads)
              have afterOverflow := CoreDecode.ReadsPagesFrom.right
                (left := tableEncoding.overflowPages) (right := indexPages)
                afterTree
              simpa [tableNext, stateNext, treeLength, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc] using afterOverflow
            have individualIndexReads : ∀ encoding ∈ indexEncodings,
                CoreDecode.ReadsPagesFrom source encoding.rootPage
                  encoding.pages :=
              CoreDecode.ReadsPagesFrom.encodeOverflowIndexTableGroups source
                tableEncoding.nextPage database.tables indexEncodings
                indexResult indexReads
            have indexRange : ∀ encoding ∈ indexEncodings,
                tableEncoding.nextPage ≤ encoding.rootPage ∧
                encoding.rootPage + encoding.pages.length ≤
                  tableEncoding.nextPage + indexPages.length := by
              simpa [indexPages] using
                CoreOverflow.encodeIndexTableGroups_member_range
                  tableEncoding.nextPage database.tables indexEncodings
                  indexResult
            have endBound : tableEncoding.nextPage + indexPages.length =
                remaining.length + 2 := by
              simp only [remaining, List.length_append]
              rw [tableNext, stateNext, treeLength]
              omega
            have indexPositive : ∀ encoding ∈ indexEncodings,
                0 < encoding.rootPage := by
              intro encoding member
              have range := indexRange encoding member
              rw [tableNext, stateNext] at range
              omega
            have indexPageBound : ∀ encoding ∈ indexEncodings,
                encoding.rootPage + encoding.pages.length < 2 ^ 32 := by
              intro encoding member
              have range := indexRange encoding member
              rw [endBound] at range
              change 1 + remaining.length + 1 < 2 ^ 32 at countBound
              omega
            have indexSourceBound : ∀ encoding ∈ indexEncodings,
                encoding.rootPage + encoding.pages.length ≤
                  source.pageCount + 1 := by
              intro encoding member
              have range := indexRange encoding member
              rw [endBound] at range
              omega
            have indexCertificates :=
              indexGroupCertificates_encodeIndexTableGroups source
                tableEncoding.nextPage database.tables indexEncodings
                database.tablesWellFormed indexResult individualIndexReads
                indexPositive indexPageBound indexSourceBound
            have safe : ∀ entry ∈ entries,
                CoreDecode.CatalogTextRoundtrips entry := by
              intro entry _
              exact ⟨utf8 entry.kind, utf8 entry.name,
                utf8 entry.table, utf8 entry.sql⟩
            have catalogDecoded :=
              CoreDecode.decodeCatalogForOpen_schemaPageForEntries
                entries count safe schemaResult
            have canonicalFirstRead :
                (CoreDecode.PageSource.ofList
                  ((schemaPage :: remaining).map CoreFile.Page.bytes)).readPage
                    1 = some schemaPage.bytes := by
              simp [CoreDecode.PageSource.ofList, CoreDecode.page?]
            have expectedCatalogRead :
                source.readPage 1 >>= CoreDecode.decodeCatalogForOpen =
                  some (entries.map CoreDecode.CatalogEntry.ofEncoded) := by
              rw [catalogRead, canonicalFirstRead]
              simp only [Option.bind_eq_bind, Option.bind]
              exact catalogDecoded
            have tableFilter :
                ((entries.map CoreDecode.CatalogEntry.ofEncoded).filter
                  (fun entry => entry.kind == "table")) =
                    tableEntries.map CoreDecode.CatalogEntry.ofEncoded := by
              rw [show entries.map CoreDecode.CatalogEntry.ofEncoded =
                  tableEntries.map CoreDecode.CatalogEntry.ofEncoded ++
                    indexEntries.map CoreDecode.CatalogEntry.ofEncoded by
                simp [entries]]
              rw [List.filter_append]
              have tablesKept :
                  (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "table") =
                      tableEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                apply List.filter_eq_self.mpr
                intro entry member
                rcases List.mem_map.mp member with
                  ⟨encodedEntry, encodedMember, rfl⟩
                rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
                rfl
              have indexesRemoved :
                  (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "table") = [] := by
                apply List.filter_eq_nil_iff.mpr
                intro entry member
                rcases List.mem_map.mp member with
                  ⟨encodedEntry, encodedMember, rfl⟩
                rcases List.mem_map.mp encodedMember with
                  ⟨encoding, _, rfl⟩
                simp [CoreOverflow.IndexEncoding.catalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded]
              rw [tablesKept, indexesRemoved, List.append_nil]
            have indexFilter :
                ((entries.map CoreDecode.CatalogEntry.ofEncoded).filter
                  (fun entry => entry.kind == "index")) =
                    indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
              rw [show entries.map CoreDecode.CatalogEntry.ofEncoded =
                  tableEntries.map CoreDecode.CatalogEntry.ofEncoded ++
                    indexEntries.map CoreDecode.CatalogEntry.ofEncoded by
                simp [entries]]
              rw [List.filter_append]
              have tablesRemoved :
                  (tableEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "index") = [] := by
                apply List.filter_eq_nil_iff.mpr
                intro entry member
                rcases List.mem_map.mp member with
                  ⟨encodedEntry, encodedMember, rfl⟩
                rcases List.mem_map.mp encodedMember with ⟨table, _, rfl⟩
                simp [CorePageCodec.chunkTableCatalogEntry,
                  CoreDecode.CatalogEntry.ofEncoded]
              have indexesKept :
                  (indexEntries.map CoreDecode.CatalogEntry.ofEncoded).filter
                    (fun entry => entry.kind == "index") =
                      indexEntries.map CoreDecode.CatalogEntry.ofEncoded := by
                apply List.filter_eq_self.mpr
                intro entry member
                rcases List.mem_map.mp member with
                  ⟨encodedEntry, encodedMember, rfl⟩
                rcases List.mem_map.mp encodedMember with
                  ⟨encoding, _, rfl⟩
                rfl
              rw [tablesRemoved, indexesKept, List.nil_append]
            have stateDatabase :=
              (CoreChunkPageState.State.build?_represents stateResult).1
            refine ⟨state, rfl, ⟨?_⟩⟩
            refine ⟨entries.map CoreDecode.CatalogEntry.ofEncoded,
              tableEntries.map CoreDecode.CatalogEntry.ofEncoded,
              indexEntries.map CoreDecode.CatalogEntry.ofEncoded,
              expectedCatalogRead, tableFilter, indexFilter, ?_, ?_, ?_⟩
            · simpa [tableEntries] using baseTables
            · rw [stateDatabase]
              simpa [indexEntries, CoreOverflow.indexEntriesOf,
                List.map_map, Function.comp_def] using indexCertificates.1
            · rw [stateDatabase]
              simpa [indexEntries, CoreOverflow.indexEntriesOf,
                List.map_map, Function.comp_def] using indexCertificates.2
        next => contradiction

/-- Every encoded page covered by one member of a distinct write set is
present in the page source obtained after applying that write set. -/
theorem pageSourceContains_applyWrites_of_covered
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pages : List CorePageCodec.NumberedPage)
    (covered : ∀ numbered ∈ pages,
      ∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) pages := by
  intro numbered member
  rcases covered numbered member with
    ⟨write, writeMember, pageNumber, bytes⟩
  rw [← pageNumber]
  rw [CorePageSource.readPage_applyWrites_of_mem image distinct writeMember]
  exact congrArg some bytes

/-- A contiguous encoded page run is readable from the post-write source when
every byte page in the run is supplied by its exact numbered write.  This is
the physical bridge used by rebuilt index and overflow runs. -/
theorem readsPagesFrom_applyWrites_of_covered
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (start : Nat) (pages : List CoreFile.Page)
    (covered : ∀ (offset : Nat) (inBounds : offset < pages.length),
      ∃ write ∈ writes,
        write.pageId + 1 = start + offset ∧
        write.page.bytes.toList =
          (pages.get ⟨offset, inBounds⟩).bytes) :
    CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) start pages := by
  intro offset inBounds
  rcases covered offset inBounds with
    ⟨write, writeMember, pageNumber, bytes⟩
  rw [← pageNumber]
  rw [CorePageSource.readPage_applyWrites_of_mem image distinct writeMember]
  exact congrArg some bytes

/-- A contiguous encoded run may mix freshly written pages with exact old
pages omitted from the delta.  This is the index/overflow analogue of
`pageSourceContains_applyWrites`. -/
theorem readsPagesFrom_applyWrites
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (start : Nat) (pages : List CoreFile.Page)
    (accounted : ∀ (offset : Nat) (inBounds : offset < pages.length),
      (∃ write ∈ writes,
        write.pageId + 1 = start + offset ∧
        write.page.bytes.toList =
          (pages.get ⟨offset, inBounds⟩).bytes) ∨
      (0 < start + offset ∧ start + offset ≤ image.pageCount ∧
        (CorePageSource.ofStorageImage image).readPage (start + offset) =
          some (pages.get ⟨offset, inBounds⟩).bytes ∧
        ∀ write ∈ writes, write.pageId + 1 ≠ start + offset)) :
    CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) start pages := by
  intro offset inBounds
  rcases accounted offset inBounds with written | unchanged
  · rcases written with ⟨write, member, pageNumber, bytes⟩
    rw [← pageNumber]
    rw [CorePageSource.readPage_applyWrites_of_mem image distinct member]
    exact congrArg some bytes
  · let pageId := start + offset - 1
    have pageNumber : pageId + 1 = start + offset := by
      simp only [pageId]
      omega
    have oldBound : pageId < image.pageCount := by
      simp only [pageId]
      omega
    have newBound :
        pageId < (GrowableStorage.applyWrites image writes).pageCount := by
      have growth := CorePageSource.applyWrites_pageCount_ge image writes
      omega
    rw [← pageNumber]
    rw [CorePageSource.readPage_applyWrites_of_not_written image writes pageId
      newBound oldBound]
    · simpa [pageNumber] using unchanged.2.2.1
    · intro write member equal
      exact unchanged.2.2.2 write member (by omega)

/-- A successfully encoded index run plus exact post-write page reads gives
the physical index premise consumed by `IndexGroupsDecode`. -/
theorem IndexesDecode.consEncoded
    {source : CoreDecode.PageSource} {table : Core.Table}
    {entry : CoreDecode.CatalogEntry}
    {entries : List CoreDecode.CatalogEntry} {index : Core.Index}
    {rootPage : Nat} {encoding : CoreOverflow.IndexEncoding}
    (sameTable : entry.table = table.schema.name)
    (sameRoot : entry.rootPage = rootPage)
    (metadata : CoreDecode.decodeCanonicalIndex table.schema
      table.schema.name entry = some index)
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : CoreDecode.ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (tail : IndexesDecode source table entries) :
    IndexesDecode source table (entry :: entries) := by
  refine IndexesDecode.cons sameTable metadata ?_ tail
  rw [sameRoot]
  simpa only [CoreDecode.expectedIndexEntries] using
    CoreDecode.decodeIndexSubtreeFrom_encodeIndex source encoded reads
      rootPositive pageBound withinSource

/-- The write list emitted by `TableDelta.writes` immediately establishes the
decoder containment invariant for every page selected by that delta. -/
theorem pageSourceContains_tableDeltaPages
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (delta : CoreChunkPageDelta.TableDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (converted : CoreChunkPageDelta.writes delta = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId)) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.pages := by
  exact pageSourceContains_applyWrites_of_covered image writes distinct
    delta.pages (CoreChunkPageDelta.writes_covers_pages converted)

/-- A canonical old page that is in range and absent from the write set reads
identically after the delta. -/
theorem readPage_applyWrites_of_unchanged
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (numbered : CorePageCodec.NumberedPage)
    (positive : 0 < numbered.pageNumber)
    (oldBound : numbered.pageNumber ≤ image.pageCount)
    (oldRead : (CorePageSource.ofStorageImage image).readPage
      numbered.pageNumber = some numbered.page.bytes)
    (notWritten : ∀ write ∈ writes,
      write.pageId + 1 ≠ numbered.pageNumber) :
    (CorePageSource.ofStorageImage
      (GrowableStorage.applyWrites image writes)).readPage
        numbered.pageNumber = some numbered.page.bytes := by
  let pageId := numbered.pageNumber - 1
  have pageNumber : pageId + 1 = numbered.pageNumber := by
    simp only [pageId]
    omega
  have oldPageIdBound : pageId < image.pageCount := by
    simp only [pageId]
    omega
  have newPageIdBound :
      pageId < (GrowableStorage.applyWrites image writes).pageCount := by
    have growth := CorePageSource.applyWrites_pageCount_ge image writes
    omega
  rw [← pageNumber]
  rw [CorePageSource.readPage_applyWrites_of_not_written image writes pageId
    newPageIdBound oldPageIdBound]
  · simpa [pageNumber] using oldRead
  · intro write member equal
    exact notWritten write member (by omega)

/-- A mixed local delta contains a complete encoded page set when every page
is either supplied by the delta or certified unchanged from the old image. -/
theorem pageSourceContains_applyWrites
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (pages : List CorePageCodec.NumberedPage)
    (accounted : ∀ numbered ∈ pages,
      (∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) ∨
      (0 < numbered.pageNumber ∧
        numbered.pageNumber ≤ image.pageCount ∧
        (CorePageSource.ofStorageImage image).readPage numbered.pageNumber =
          some numbered.page.bytes ∧
        ∀ write ∈ writes, write.pageId + 1 ≠ numbered.pageNumber)) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) pages := by
  intro numbered member
  rcases accounted numbered member with changed | unchanged
  · rcases changed with ⟨write, writeMember, pageNumber, bytes⟩
    rw [← pageNumber]
    rw [CorePageSource.readPage_applyWrites_of_mem image distinct writeMember]
    exact congrArg some bytes
  · exact readPage_applyWrites_of_unchanged image writes numbered
      unchanged.1 unchanged.2.1 unchanged.2.2.1 unchanged.2.2.2

/-- Transport an unchanged table certificate across a disjoint physical write
set.  Every tree and overflow byte is read from the old image; the proof makes
the noninterference condition explicit instead of relying on a whole-file
decode after the write. -/
def TableOnSource.applyWritesOfUntouched
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (state : CoreChunkPageState.TableState)
    (physical : TableOnSource (CorePageSource.ofStorageImage image) state)
    (treeBounds : ∀ numbered ∈ physical.encoding.treePages,
      0 < numbered.pageNumber ∧ numbered.pageNumber ≤ image.pageCount)
    (treeUntouched : ∀ numbered ∈ physical.encoding.treePages,
      ∀ write ∈ writes, write.pageId + 1 ≠ numbered.pageNumber)
    (overflowBounds : ∀ (offset : Nat)
      (_inBounds : offset < physical.encoding.overflowPages.length),
      0 < physical.nextOverflow + offset ∧
        physical.nextOverflow + offset ≤ image.pageCount)
    (overflowUntouched : ∀ (offset : Nat)
      (_inBounds : offset < physical.encoding.overflowPages.length),
      ∀ write ∈ writes,
        write.pageId + 1 ≠ physical.nextOverflow + offset) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) state := by
  refine TableOnSource.transport
    (newSource := CorePageSource.ofStorageImage
      (GrowableStorage.applyWrites image writes)) physical (by
        simpa only [CorePageSource.ofStorageImage_pageCount] using
          CorePageSource.applyWrites_pageCount_ge image writes) ?_ ?_
  · apply pageSourceContains_applyWrites image writes distinct
      physical.encoding.treePages
    intro numbered member
    exact .inr ⟨(treeBounds numbered member).1,
      (treeBounds numbered member).2, physical.treeContains numbered member,
      treeUntouched numbered member⟩
  · apply readsPagesFrom_applyWrites image writes distinct
      physical.nextOverflow physical.encoding.overflowPages
    intro offset inBounds
    exact .inr ⟨(overflowBounds offset inBounds).1,
      (overflowBounds offset inBounds).2,
      physical.overflowContains offset inBounds,
      overflowUntouched offset inBounds⟩

private theorem numberedPage_eq_of_pageNumber_eq
    {pages : List CorePageCodec.NumberedPage}
    (unique : (pages.map CorePageCodec.NumberedPage.pageNumber).Nodup) :
    ∀ {left right : CorePageCodec.NumberedPage}, left ∈ pages →
      right ∈ pages → left.pageNumber = right.pageNumber → left = right := by
  induction pages with
  | nil => simp
  | cons head pages induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      intro left right leftMember rightMember pageNumber
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftLater
      · rcases rightMember with rfl | rightLater
        · rfl
        · exfalso
          exact unique.1 (List.mem_map.mpr
            ⟨right, rightLater, pageNumber.symm⟩)
      · rcases rightMember with rfl | rightLater
        · exfalso
          exact unique.1 (List.mem_map.mpr
            ⟨left, leftLater, pageNumber⟩)
        · exact induction unique.2 leftLater rightLater pageNumber

/-- Complete no-overflow table-page preservation from a `TableDelta`.

The accounting theorem supplies the logical partition; exact conversion gives
both directions between selected pages and writes; and unique post-state page
identities rule out a write aliasing an allegedly unchanged page.  This is the
component theorem needed before composing table pages with overflow, catalog,
freelist, and index components. -/
theorem pageSourceContains_tableDeltaComplete
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (delta : CoreChunkPageDelta.TableDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (converted : CoreChunkPageDelta.writes delta = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (accounted : ∀ page ∈ afterPages,
      page ∈ delta.pages ∨ page ∈ beforePages)
    (selected : ∀ page ∈ delta.pages, page ∈ afterPages)
    (unique : (afterPages.map
      CorePageCodec.NumberedPage.pageNumber).Nodup)
    (oldContains : CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage image) beforePages)
    (oldBounds : ∀ page ∈ beforePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) afterPages := by
  apply pageSourceContains_applyWrites image writes distinct afterPages
  intro page pageMember
  by_cases selectedMember : page ∈ delta.pages
  · left
    exact CoreChunkPageDelta.writes_covers_pages converted page selectedMember
  · right
    have oldMember : page ∈ beforePages := by
      rcases accounted page pageMember with changed | unchanged
      · exact False.elim (selectedMember changed)
      · exact unchanged
    refine ⟨(oldBounds page oldMember).1, (oldBounds page oldMember).2,
      oldContains page oldMember, ?_⟩
    intro write writeMember samePage
    rcases CoreChunkPageDelta.writes_sources_pages converted write writeMember
        with ⟨source, sourceMember, sourcePage, sourceBytes⟩
    have sourceAfter := selected source sourceMember
    have equal : source = page := numberedPage_eq_of_pageNumber_eq unique
      sourceAfter pageMember (sourcePage.symm.trans samePage)
    exact selectedMember (equal ▸ sourceMember)

/-- Live-state specialization.  The delta builder itself supplies accounting,
post-state selection, and active-page identity uniqueness; callers need only
provide the represented old bytes and the successful deterministic encodings.
-/
theorem pageSourceContains_updateStateTree
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (beforeEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some beforePages)
    (afterEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterPages)
    (oldContains : CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage image) beforePages)
    (oldBounds : ∀ page ∈ beforePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) afterPages := by
  apply pageSourceContains_tableDeltaComplete image delta.table writes
    beforePages afterPages converted distinct
  · exact CoreChunkPageDelta.updateState?_treePagesAccounted updated
      beforePages afterPages beforeEncoded afterEncoded
  · exact CoreChunkPageDelta.updateState?_treePagesSelected updated afterPages
      afterEncoded
  · rw [CorePageCodec.encodeChunkNode_pageNumbers _ _ _ afterEncoded]
    exact (CoreChunkPageDelta.updateState?_identityWellFormed updated).1
  · exact oldContains
  · exact oldBounds

/-- Changed-index writers use the candidate before the unchanged-index check;
its table delta has the same exact page-accounting guarantees. -/
theorem pageSourceContains_updateStateCandidateTree
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (updated : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (beforeEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some beforePages)
    (afterEncoded : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterPages)
    (oldContains : CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage image) beforePages)
    (oldBounds : ∀ page ∈ beforePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount) :
    CorePageCodec.PageSourceContains
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) afterPages := by
  apply pageSourceContains_tableDeltaComplete image delta.table writes
    beforePages afterPages converted distinct
  · exact CoreChunkPageDelta.updateStateCandidate?_treePagesAccounted updated
      beforePages afterPages beforeEncoded afterEncoded
  · exact CoreChunkPageDelta.updateStateCandidate?_treePagesSelected updated
      afterPages afterEncoded
  · rw [CorePageCodec.encodeChunkNode_pageNumbers _ _ _ afterEncoded]
    exact (CoreChunkPageDelta.updateStateCandidate?_identityWellFormed updated).1
  · exact oldContains
  · exact oldBounds

/-- A successful ordinary state delta establishes the complete changed-table
certificate for inline records.  Both old and new tree lists are obtained from
the general encoder inverse; `pageSourceContains_updateStateTree` then proves
that the actual write overlay contains every post-state byte. -/
def TableOnSource.updateStateInline
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema)
    (before : TableOnSource (CorePageSource.ofStorageImage image)
      delta.table.before)
    (beforeInline : before.encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding)
    (afterInline : afterEncoding.overflowPages = [])
    (oldBounds : ∀ page ∈ before.encoding.treePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount)
    (heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)).pageCount + 1) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.table.after := by
  have beforeTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some before.encoding.treePages := by
    simpa [schemaSame] using before.inlineEncoded beforeInline
  have afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterEncoding.treePages :=
    CorePageCodec.encodeChunkNodeWithOverflow_noOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow afterEncoding afterEncoded afterInline
  have treeContains := pageSourceContains_updateStateTree image state database
    delta writes before.encoding.treePages afterEncoding.treePages updated
    converted distinct beforeTree afterTree before.treeContains oldBounds
  refine {
    nextOverflow := before.nextOverflow
    encoding := afterEncoding
    encoded := afterEncoded
    treeContains
    overflowContains := ?_
    heightBound
    nextPositive := before.nextPositive
    pageBound := ?_
    fuelBound := ?_ }
  · intro offset inBounds
    simp [afterInline] at inBounds
  · rw [afterInline]
    simpa [beforeInline] using before.pageBound
  · rw [afterInline]
    simp

/-- Changed-index counterpart of `updateStateInline`, using the exact candidate
consumed by the live index preparation paths. -/
def TableOnSource.updateStateCandidateInline
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (updated : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema)
    (before : TableOnSource (CorePageSource.ofStorageImage image)
      delta.table.before)
    (beforeInline : before.encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding)
    (afterInline : afterEncoding.overflowPages = [])
    (oldBounds : ∀ page ∈ before.encoding.treePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount)
    (heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)).pageCount + 1) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.table.after := by
  have beforeTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.before.tree.root =
        some before.encoding.treePages := by
    simpa [schemaSame] using before.inlineEncoded beforeInline
  have afterTree : CorePageCodec.encodeChunkNode
      delta.table.after.table.schema delta.table.after.tree.root =
        some afterEncoding.treePages :=
    CorePageCodec.encodeChunkNodeWithOverflow_noOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow afterEncoding afterEncoded afterInline
  have treeContains := pageSourceContains_updateStateCandidateTree image state
    database delta writes before.encoding.treePages afterEncoding.treePages
    updated converted distinct beforeTree afterTree before.treeContains oldBounds
  refine {
    nextOverflow := before.nextOverflow
    encoding := afterEncoding
    encoded := afterEncoded
    treeContains
    overflowContains := ?_
    heightBound
    nextPositive := before.nextPositive
    pageBound := ?_
    fuelBound := ?_ }
  · intro offset inBounds
    simp [afterInline] at inBounds
  · rw [afterInline]
    simpa [beforeInline] using before.pageBound
  · rw [afterInline]
    simp

/-- Decoding a canonical persistent table after a local page delta returns
exactly the logical table carried by the proof-carrying state.  Tree pages are
identified and may be sparse; overflow pages retain their separately allocated
contiguous interval. -/
theorem decodeTableFrom_of_pageSourceContains
    (source : CoreDecode.PageSource)
    (state : CoreChunkPageState.TableState)
    (nextOverflow : Nat) (encoding : CorePageCodec.OverflowEncoding)
    (encoded : CorePageCodec.encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (treeContains : CorePageCodec.PageSourceContains source
      encoding.treePages)
    (overflowContains : CoreDecode.ReadsPagesFrom source nextOverflow
      encoding.overflowPages)
    (heightBound : state.tree.root.erase.height < source.pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length < source.pageCount + 1) :
    CoreDecode.decodeTableFrom source
      (CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry state)) =
      some state.table.withoutIndexes := by
  exact CorePageCodec.decodeTableFrom_encodeChunkNodeWithOverflow source state
    nextOverflow encoding encoded treeContains overflowContains heightBound
    nextPositive pageBound fuelBound

/-- Direct storage-image specialization used by a localized table writer. -/
theorem decodeTableFrom_applyWrites
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (state : CoreChunkPageState.TableState)
    (nextOverflow : Nat) (encoding : CorePageCodec.OverflowEncoding)
    (encoded : CorePageCodec.encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (accounted : ∀ numbered ∈ encoding.treePages,
      (∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) ∨
      (0 < numbered.pageNumber ∧
        numbered.pageNumber ≤ image.pageCount ∧
        (CorePageSource.ofStorageImage image).readPage numbered.pageNumber =
          some numbered.page.bytes ∧
        ∀ write ∈ writes, write.pageId + 1 ≠ numbered.pageNumber))
    (overflowContains : CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      nextOverflow encoding.overflowPages)
    (heightBound : state.tree.root.erase.height <
      (GrowableStorage.applyWrites image writes).pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length <
      (GrowableStorage.applyWrites image writes).pageCount + 1) :
    CoreDecode.decodeTableFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      (CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry state)) =
      some state.table.withoutIndexes := by
  exact decodeTableFrom_of_pageSourceContains _ state nextOverflow encoding
    encoded
    (pageSourceContains_applyWrites image writes distinct encoding.treePages
      accounted)
    overflowContains (by simpa using heightBound) nextPositive pageBound
    (by simpa using fuelBound)

/-- Insert a changed table, including its separately allocated overflow run,
directly into the database-wide table certificate.  This is the final
list-level composition step: callers no longer have to restate the decoder
equation produced by `decodeTableFrom_applyWrites`. -/
theorem TablesDecode.consOverflowEncoded
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (entry : CoreDecode.CatalogEntry)
    (entries : List CoreDecode.CatalogEntry)
    (state : CoreChunkPageState.TableState) (tables : List Core.Table)
    (entryExact : entry = CoreDecode.CatalogEntry.ofEncoded
      (CorePageCodec.chunkTableCatalogEntry state))
    (nextOverflow : Nat) (encoding : CorePageCodec.OverflowEncoding)
    (encoded : CorePageCodec.encodeChunkNodeWithOverflow state.table.schema
      state.tree.root nextOverflow = some encoding)
    (accounted : ∀ numbered ∈ encoding.treePages,
      (∃ write ∈ writes,
        write.pageId + 1 = numbered.pageNumber ∧
        write.page.bytes.toList = numbered.page.bytes) ∨
      (0 < numbered.pageNumber ∧
        numbered.pageNumber ≤ image.pageCount ∧
        (CorePageSource.ofStorageImage image).readPage numbered.pageNumber =
          some numbered.page.bytes ∧
        ∀ write ∈ writes, write.pageId + 1 ≠ numbered.pageNumber))
    (overflowContains : CoreDecode.ReadsPagesFrom
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      nextOverflow encoding.overflowPages)
    (heightBound : state.tree.root.erase.height <
      (GrowableStorage.applyWrites image writes).pageCount + 1)
    (nextPositive : 0 < nextOverflow)
    (pageBound : nextOverflow + encoding.overflowPages.length < 2 ^ 32)
    (fuelBound : encoding.overflowPages.length <
      (GrowableStorage.applyWrites image writes).pageCount + 1)
    (tail : TablesDecode
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) entries tables) :
    TablesDecode
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes))
      (entry :: entries) (state.table :: tables) := by
  subst entry
  exact .cons
    (decodeTableFrom_applyWrites image writes distinct state nextOverflow
      encoding encoded accounted overflowContains heightBound nextPositive
      pageBound fuelBound)
    tail

end CoreLocalizedRepresentation
end SQLeanite
