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

/-- Exact containment implies the ordinary one-based SQLite page bounds for
every represented tree page.  Keeping this derived avoids asking localized
commit callers to repeat bounds already encoded by the page source. -/
theorem TableOnSource.treeBounds
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    {state : CoreChunkPageState.TableState}
    (physical : TableOnSource (CorePageSource.ofStorageImage image) state) :
    ∀ page ∈ physical.encoding.treePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount := by
  intro page member
  have contained := physical.treeContains page member
  constructor
  · cases number : page.pageNumber with
    | zero =>
        rw [number, CorePageSource.readPage_zero image] at contained
        contradiction
    | succ value => omega
  · by_cases high : image.pageCount < page.pageNumber
    · rw [CorePageSource.readPage_out_of_bounds image page.pageNumber high]
        at contained
      contradiction
    · omega

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

theorem TablesOnSource.entries_eq
    {source : CoreDecode.PageSource} {entries : List CoreDecode.CatalogEntry}
    {states : List CoreChunkPageState.TableState}
    (physical : TablesOnSource source entries states) :
    entries = states.map fun state => CoreDecode.CatalogEntry.ofEncoded
      (CorePageCodec.chunkTableCatalogEntry state) := by
  induction physical with
  | nil => rfl
  | cons entryExact head tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨entryExact, induction⟩

/-- Recover the exact per-table physical witness for any state in an aligned
`TablesOnSource` list.  This is proof-only list lookup; no page is read and no
logical database is compared. -/
theorem TablesOnSource.exists_table
    {source : CoreDecode.PageSource} {entries : List CoreDecode.CatalogEntry}
    {states : List CoreChunkPageState.TableState}
    (physical : TablesOnSource source entries states) :
    ∀ state ∈ states, ∃ _witness : TableOnSource source state, True := by
  induction physical with
  | nil => simp
  | cons entryExact head tail induction =>
      intro state member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨head, True.intro⟩
      · exact induction state member

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
            rcases Option.bind_eq_some_iff.mp success with
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

/-- Membership-aware form of `alignTables_none`.  The stronger callback is
what a page-frame proof needs: it is invoked only for states actually present
in the unchanged list, rather than for an arbitrary `TableState` value. -/
theorem TablesOnSource.alignTables_none_mem
    {oldSource newSource : CoreDecode.PageSource}
    {scopeStates : List CoreChunkPageState.TableState}
    (retained : ∀ (state : CoreChunkPageState.TableState), state ∈ scopeStates →
      ∀ (table : Core.Table) (equivalent : state.table.Equiv table),
      TableOnSource oldSource state →
        TableOnSource newSource (state.retarget table equivalent)) :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table}
      {aligned : CoreChunkPageDelta.AlignedTables target}
      {entries : List CoreDecode.CatalogEntry},
      (∀ state ∈ states, state ∈ scopeStates) →
      CoreChunkPageDelta.alignTables? nextPage states target = some aligned →
      aligned.delta = none →
      TablesOnSource oldSource entries states →
      TablesOnSource newSource
        (aligned.tables.map fun state => CoreDecode.CatalogEntry.ofEncoded
          (CorePageCodec.chunkTableCatalogEntry state)) aligned.tables
  | _, [], target, aligned, entries, subset, success, noChange, physical => by
      cases target with
      | nil =>
          simp only [CoreChunkPageDelta.alignTables?, Option.some.injEq]
            at success
          subst aligned
          cases physical
          exact .nil
      | cons _ _ => simp [CoreChunkPageDelta.alignTables?] at success
  | nextPage, state :: states, target, aligned, entries, subset, success,
      noChange, physical => by
      cases target with
      | nil => simp [CoreChunkPageDelta.alignTables?] at success
      | cons table tables =>
        cases physical with
        | cons entryExact head tail =>
          unfold CoreChunkPageDelta.alignTables? at success
          split at success
          next equivalent =>
            rcases Option.bind_eq_some_iff.mp success with
              ⟨tailAligned, tailResult, success⟩
            simp only [Option.some.injEq] at success
            subst aligned
            have tailSubset : ∀ candidate ∈ states,
                candidate ∈ scopeStates := by
              intro candidate member
              exact subset candidate (by simp [member])
            have tailPhysical := alignTables_none_mem retained tailSubset
              tailResult noChange tail
            exact .cons rfl
              (retained state (subset state (by simp)) table equivalent head)
              tailPhysical
          next =>
            split at success
            next => contradiction
            next changed changedResult =>
              split at success
              next => contradiction
              next tailAligned tailResult =>
                split at success
                next =>
                  simp only [Option.some.injEq] at success
                  subst aligned
                  simp at noChange
                next => contradiction

/-- A successful one-table alignment transports every unchanged physical
table and installs the supplied exact certificate for the changed table.
This is the table-list frame theorem used by localized commits. -/
theorem TablesOnSource.alignTables_changed
    {oldSource newSource : CoreDecode.PageSource}
    {scopeStates : List CoreChunkPageState.TableState}
    {changed : CoreChunkPageDelta.TableDelta}
    (retained : ∀ (state : CoreChunkPageState.TableState), state ∈ scopeStates →
      ∀ (table : Core.Table) (equivalent : state.table.Equiv table),
      state ≠ changed.before →
      TableOnSource oldSource state →
        TableOnSource newSource (state.retarget table equivalent))
    (changedPhysical : TableOnSource newSource changed.after) :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table}
      {aligned : CoreChunkPageDelta.AlignedTables target}
      {entries : List CoreDecode.CatalogEntry},
      (∀ state ∈ states, state ∈ scopeStates) →
      states.Nodup →
      CoreChunkPageDelta.alignTables? nextPage states target = some aligned →
      aligned.delta = some changed →
      TablesOnSource oldSource entries states →
      TablesOnSource newSource
        (aligned.tables.map fun state => CoreDecode.CatalogEntry.ofEncoded
          (CorePageCodec.chunkTableCatalogEntry state)) aligned.tables
  | _, [], target, aligned, entries, subset, nodup, success, selected,
      physical => by
      cases target <;> simp [CoreChunkPageDelta.alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, state :: states, target, aligned, entries, subset, nodup,
      success, selected, physical => by
      simp only [List.nodup_cons] at nodup
      cases target with
      | nil => simp [CoreChunkPageDelta.alignTables?] at success
      | cons table tables =>
        cases physical with
        | cons entryExact head tail =>
          unfold CoreChunkPageDelta.alignTables? at success
          split at success
          next equivalent =>
            rcases Option.bind_eq_some_iff.mp success with
              ⟨tailAligned, tailResult, success⟩
            simp only [Option.some.injEq] at success
            subst aligned
            have selectedTail :=
              CoreChunkPageDelta.alignTables?_selected_mem tailResult selected
            have stateDifferent : state ≠ changed.before := by
              intro equal
              apply nodup.1
              rw [equal]
              exact selectedTail.1
            have tailSubset : ∀ candidate ∈ states,
                candidate ∈ scopeStates := by
              intro candidate member
              exact subset candidate (by simp [member])
            have tailPhysical := alignTables_changed retained changedPhysical
              tailSubset nodup.2 tailResult selected tail
            exact .cons rfl
              (retained state (subset state (by simp)) table equivalent
                stateDifferent head) tailPhysical
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
                  have changedBefore : changed.before = state :=
                    CoreChunkPageDelta.replaceBetween?_before headResult
                  have retainedTail : ∀ old ∈ states, ∀ table
                      (equivalent : old.table.Equiv table),
                      TableOnSource oldSource old →
                        TableOnSource newSource
                          (old.retarget table equivalent) := by
                    intro old member table equivalent oldPhysical
                    apply retained old (subset old (by simp [member])) table
                      equivalent
                    · intro equalOld
                      apply nodup.1
                      have oldEqual : old = state := equalOld.trans changedBefore
                      simpa [oldEqual] using member
                    · exact oldPhysical
                  have tailPhysical := alignTables_none_mem
                    (scopeStates := states) retainedTail
                    (by intro candidate member; exact member)
                    tailResult tailNone tail
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
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      TableOnSource oldSource old →
        TableOnSource newSource (old.retarget table equivalent))
    (changed : TableOnSource newSource delta.table.after) :
    TablesOnSource newSource
      (delta.after.tables.map fun table => CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry table)) delta.after.tables := by
  rcases CoreChunkPageDelta.updateStateCandidate?_alignment updated with
    ⟨aligned, alignedResult, alignedTables, selected⟩
  have transported := alignTables_changed retained changed
    (by intro candidate member; exact member) state.tables_nodup alignedResult
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
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      TableOnSource oldSource old →
        TableOnSource newSource (old.retarget table equivalent))
    (changed : TableOnSource newSource delta.table.after) :
    TablesOnSource newSource
      (delta.after.tables.map fun table => CoreDecode.CatalogEntry.ofEncoded
        (CorePageCodec.chunkTableCatalogEntry table)) delta.after.tables := by
  rcases CoreChunkPageDelta.updateState?_alignment updated with
    ⟨aligned, alignedResult, alignedTables, selected⟩
  have transported := alignTables_changed retained changed
    (by intro candidate member; exact member) state.tables_nodup alignedResult
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
  refine ⟨metadata.1, metadata.2, ?_⟩
  have image := delta.tablePagesSufficient_indexImage sufficient
  unfold CoreChunkPageDelta.indexImage at image
  rw [metadata.2] at image
  intro index member
  apply map_index_entries_eq_value delta.after.table.indexes
    (fun candidate =>
      CoreDecode.expectedIndexEntries delta.before.table candidate)
    (fun candidate =>
      CoreDecode.expectedIndexEntries delta.after.table candidate) image index
  rw [← metadata.2]
  exact member

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
          rw [metadataEq.2] at current'
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
              expectedCatalogRead, tableFilter, indexFilter, ?_, ?_, ?_, ?_⟩
            · simpa [tableEntries, Function.comp_def] using baseTables
            · rw [stateDatabase]
              simpa [indexEntries, CoreOverflow.indexEntriesOf,
                List.map_map, Function.comp_def] using indexCertificates.2.2
            · rw [stateDatabase]
              simpa [indexEntries, CoreOverflow.indexEntriesOf,
                List.map_map, Function.comp_def] using indexCertificates.2.1
            · unfold TablePagesBeforeIndexRoots
              intro pageId pageMember entry entryMember
              rw [statePages] at pageMember
              simp only [List.mem_range'_1] at pageMember
              rcases List.mem_map.mp entryMember with
                ⟨encodedEntry, encodedMember, rfl⟩
              rcases List.mem_map.mp (by
                simpa [indexEntries, CoreOverflow.indexEntriesOf] using
                  encodedMember) with ⟨encoding, encodingMember, rfl⟩
              have range := indexRange encoding encodingMember
              rw [tableNext, stateNext] at range
              change pageId < encoding.rootPage
              omega
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

/-- Writes strictly below an owned index root cannot alter any page in that
index's contiguous tree/overflow run.  The old exact bytes therefore transport
to the actual post-write storage image without decoding the index again. -/
def IndexOnSource.applyWritesBelow
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {table : Core.Table} {entry : CoreDecode.CatalogEntry}
    {index : Core.Index}
    (owned : IndexOnSource (CorePageSource.ofStorageImage image)
      table entry index)
    (below : ∀ write ∈ writes, write.pageId + 1 < entry.rootPage) :
    IndexOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) table entry index := by
  rcases owned with ⟨reference, encoding, sameTable, sameRoot, metadata,
    member, encoded, reads, rootPositive, pageBound, withinSource, logical⟩
  refine ⟨reference, encoding, sameTable, sameRoot, metadata, member, encoded,
    ?_, rootPositive, pageBound, ?_, logical⟩
  · apply readsPagesFrom_applyWrites image writes distinct
      encoding.rootPage encoding.pages
    intro offset inBounds
    refine .inr ⟨by omega, by
      simp only [CorePageSource.ofStorageImage_pageCount] at withinSource
      omega, reads offset inBounds, ?_⟩
    intro write member equal
    have strictlyBelow := below write member
    rw [sameRoot] at strictlyBelow
    omega
  · simp only [CorePageSource.ofStorageImage_pageCount]
    have growth := CorePageSource.applyWrites_pageCount_ge image writes
    simp only [CorePageSource.ofStorageImage_pageCount] at withinSource
    omega

def IndexesOnSource.applyWritesBelow
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {table : Core.Table} {entries : List CoreDecode.CatalogEntry}
    (owned : IndexesOnSource (CorePageSource.ofStorageImage image)
      table entries)
    (below : ∀ entry ∈ entries, ∀ write ∈ writes,
      write.pageId + 1 < entry.rootPage) :
    IndexesOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) table entries := by
  induction owned with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (head.applyWritesBelow image writes distinct
          (below _ (by simp)))
        (induction (fun entry member => below entry (by simp [member])))

def IndexGroupsOnSource.applyWritesBelow
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {tables : List Core.Table} {entries : List CoreDecode.CatalogEntry}
    (owned : IndexGroupsOnSource (CorePageSource.ofStorageImage image)
      tables entries)
    (below : ∀ entry ∈ entries, ∀ write ∈ writes,
      write.pageId + 1 < entry.rootPage) :
    IndexGroupsOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) tables entries := by
  induction owned with
  | nil => exact .nil
  | cons current boundary tail induction =>
      exact .cons
        (current.applyWritesBelow image writes distinct
          (fun entry member => below entry (by simp [member])))
        boundary
        (induction (fun entry member => below entry (by simp [member])))

/-- Extend an indexed table delta across a larger final write list.  Base
writes retain their provenance in the changed table; every framing write added
afterward is handled by a separate below-index proof.  This is the exact shape
of the live planner, which adds page zero (and, on shrinking commits, a
freelist trunk) before journaling. -/
def DatabaseOnSource.updateStateApplyWritesBelowExtension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (physical : DatabaseOnSource (CorePageSource.ofStorageImage image) state)
    (allocation : state.AllocationWellFormed)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage image).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites image finalWrites)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog))
    (retained : ∀ (old : CoreChunkPageState.TableState)
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      TableOnSource (CorePageSource.ofStorageImage image) old →
        TableOnSource
          (CorePageSource.ofStorageImage
            (GrowableStorage.applyWrites image finalWrites))
          (old.retarget table equivalent))
    (changed : TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) delta.table.after)
    (indexed : delta.table.before.table.indexes ≠ [])
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (addedBelow : ∀ entries,
      TablePagesBeforeIndexRoots state.tables entries →
      ∀ write ∈ finalWrites, write ∉ baseWrites →
        ∀ entry ∈ entries, write.pageId + 1 < entry.rootPage)
    (inline : changed.encoding.overflowPages = []) :
    DatabaseOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) delta.after := by
  refine physical.updateState allocation updated catalogPreserved retained
    changed ?_ ?_
  · intro entries metadata owned separation
    have afterEncoded := changed.inlineEncoded inline
    have selectedPages := CoreChunkPageDelta.updateState?_treePagesSelected
      updated changed.encoding.treePages afterEncoded
    have selectedTable :=
      CoreChunkPageDelta.updateState?_selected_mem updated
    have activePages :=
      CoreChunkPageDelta.updateState?_activePageIds_eq_of_indexed updated
        indexed
    have below : ∀ entry ∈ entries, ∀ write ∈ finalWrites,
        write.pageId + 1 < entry.rootPage := by
      intro entry entryMember write writeMember
      by_cases base : write ∈ baseWrites
      · rcases CoreChunkPageDelta.writes_sources_pages converted write base
            with ⟨page, pageMember, pageNumber, pageBytes⟩
        have selectedPage := selectedPages page pageMember
        have pageNumberMember : page.pageNumber ∈
            delta.table.after.tree.root.pageIds := by
          rw [← CorePageCodec.encodeChunkNodeWithOverflow_pageNumbers
            delta.table.after.table.schema delta.table.after.tree.root
            changed.nextOverflow changed.encoding changed.encoded]
          exact List.mem_map_of_mem selectedPage
        have afterActive : page.pageNumber ∈ delta.after.activePageIds := by
          unfold CoreChunkPageState.State.activePageIds
            CoreChunkPageState.tablePageIds
          exact List.mem_flatMap.mpr ⟨delta.table.after, selectedTable.2,
            by simpa [CoreChunkPageState.TableState.pageIds] using
              pageNumberMember⟩
        have beforeActive : page.pageNumber ∈ state.activePageIds := by
          rw [← activePages]
          exact afterActive
        rw [pageNumber]
        exact separation page.pageNumber beforeActive entry entryMember
      · exact addedBelow entries separation write writeMember base entry
          entryMember
    exact (owned.applyWritesBelow image finalWrites distinct below).retarget
      (updateState?_indexImagesAligned updated)
  · intro entries metadata separation
    unfold TablePagesBeforeIndexRoots at separation ⊢
    intro pageId pageMember entry entryMember
    have active : pageId ∈ delta.after.activePageIds := pageMember
    rw [CoreChunkPageDelta.updateState?_activePageIds_eq_of_indexed updated
      indexed] at active
    exact separation pageId active entry entryMember

/-- Storage-image specialization of `updateState`.  It derives—rather than
assumes—that every emitted indexed-table write is below every catalogued index
root. Exact index bytes and the separation invariant are then transported by
the ownership certificate itself. -/
def DatabaseOnSource.updateStateApplyWritesBelow
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (distinct : writes.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : CoreChunkPageDelta.StateDelta}
    (physical : DatabaseOnSource (CorePageSource.ofStorageImage image) state)
    (allocation : state.AllocationWellFormed)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (catalogPreserved : ∀ catalog,
      ((CorePageSource.ofStorageImage image).readPage 1 >>=
          CoreDecode.decodeCatalogForOpen = some catalog) →
      ((CorePageSource.ofStorageImage
          (GrowableStorage.applyWrites image writes)).readPage 1 >>=
            CoreDecode.decodeCatalogForOpen = some catalog))
    (retained : ∀ (old : CoreChunkPageState.TableState)
      (_member : old ∈ state.tables)
      (table : Core.Table) (equivalent : old.table.Equiv table),
      old ≠ delta.table.before →
      TableOnSource (CorePageSource.ofStorageImage image) old →
        TableOnSource
          (CorePageSource.ofStorageImage
            (GrowableStorage.applyWrites image writes))
          (old.retarget table equivalent))
    (changed : TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.table.after)
    (indexed : delta.table.before.table.indexes ≠ [])
    (converted : CoreChunkPageDelta.writes delta.table = some writes)
    (inline : changed.encoding.overflowPages = []) :
    DatabaseOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image writes)) delta.after := by
  apply physical.updateStateApplyWritesBelowExtension image writes writes
    distinct allocation updated catalogPreserved retained changed indexed
    converted
  · intro entries separation write member notBase
    exact False.elim (notBase member)
  · exact inline

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

/-- Frame `pageSourceContains_tableDeltaComplete` across the header/freelist
augmentation performed immediately before the live syscall trace.  The base
delta still supplies every changed table page, while the final write set is
allowed to contain additional pages provided those additions cannot alias a
post-state table page.

This is deliberately phrased over membership rather than list concatenation:
the live planner may prepend page zero and a freelist trunk, and the exact
ordering of the final distinct writes is irrelevant to the represented table
bytes. -/
theorem pageSourceContains_tableDeltaComplete_extension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (delta : CoreChunkPageDelta.TableDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (converted : CoreChunkPageDelta.writes delta = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterPages, write.pageId + 1 ≠ page.pageNumber)
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
        (GrowableStorage.applyWrites image finalWrites)) afterPages := by
  apply pageSourceContains_applyWrites image finalWrites distinct afterPages
  intro page pageMember
  by_cases selectedMember : page ∈ delta.pages
  · left
    rcases CoreChunkPageDelta.writes_covers_pages converted page selectedMember
        with ⟨write, writeMember, pageNumber, bytes⟩
    exact ⟨write, baseMember write writeMember, pageNumber, bytes⟩
  · right
    have oldMember : page ∈ beforePages := by
      rcases accounted page pageMember with changed | unchanged
      · exact False.elim (selectedMember changed)
      · exact unchanged
    refine ⟨(oldBounds page oldMember).1, (oldBounds page oldMember).2,
      oldContains page oldMember, ?_⟩
    intro write writeMember samePage
    by_cases baseWrite : write ∈ baseWrites
    · rcases CoreChunkPageDelta.writes_sources_pages converted write baseWrite
          with ⟨source, sourceMember, sourcePage, sourceBytes⟩
      have sourceAfter := selected source sourceMember
      have equal : source = page := numberedPage_eq_of_pageNumber_eq unique
        sourceAfter pageMember (sourcePage.symm.trans samePage)
      exact selectedMember (equal ▸ sourceMember)
    · exact addedUntouched write writeMember baseWrite page pageMember samePage

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

/-- Live-state specialization for the exact final write list selected by the
header/freelist planner.  Unlike `pageSourceContains_updateStateTree`, the
table conversion equation names only `baseWrites`; proof-carrying membership
and noninterference facts connect it to `finalWrites`, which is the list the
journal and main-file writer actually consume. -/
theorem pageSourceContains_updateStateTree_extension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterPages, write.pageId + 1 ≠ page.pageNumber)
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
        (GrowableStorage.applyWrites image finalWrites)) afterPages := by
  apply pageSourceContains_tableDeltaComplete_extension image delta.table
    baseWrites finalWrites beforePages afterPages converted distinct baseMember
    addedUntouched
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

/-- Changed-index counterpart of
`pageSourceContains_updateStateTree_extension`. -/
theorem pageSourceContains_updateStateCandidateTree_extension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (beforePages afterPages : List CorePageCodec.NumberedPage)
    (updated : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterPages, write.pageId + 1 ≠ page.pageNumber)
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
        (GrowableStorage.applyWrites image finalWrites)) afterPages := by
  apply pageSourceContains_tableDeltaComplete_extension image delta.table
    baseWrites finalWrites beforePages afterPages converted distinct baseMember
    addedUntouched
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

/-- Final-write variant of `TableOnSource.updateStateInline`.  It constructs
the changed-table certificate directly over the header/freelist-augmented
write list used by the live journal, instead of first proving a certificate
for a smaller logical delta and transporting it afterward. -/
def TableOnSource.updateStateInlineExtension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (updated : CoreChunkPageDelta.updateState? state database = some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema)
    (before : TableOnSource (CorePageSource.ofStorageImage image)
      delta.table.before)
    (beforeInline : before.encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterEncoding.treePages,
        write.pageId + 1 ≠ page.pageNumber)
    (afterInline : afterEncoding.overflowPages = [])
    (oldBounds : ∀ page ∈ before.encoding.treePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount)
    (heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)).pageCount + 1) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) delta.table.after := by
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
  have treeContains := pageSourceContains_updateStateTree_extension image state
    database delta baseWrites finalWrites before.encoding.treePages
    afterEncoding.treePages updated converted distinct baseMember addedUntouched
    beforeTree afterTree before.treeContains oldBounds
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

/-- Final-write changed-index counterpart of
`TableOnSource.updateStateInlineExtension`. -/
def TableOnSource.updateStateCandidateInlineExtension
    (image : GrowableStorage.Image PhysicalCodec.pageSize)
    (state : CoreChunkPageState.State) (database : Core.Database)
    (delta : CoreChunkPageDelta.StateDelta)
    (baseWrites finalWrites :
      List (GrowableStorage.PageWrite PhysicalCodec.pageSize))
    (updated : CoreChunkPageDelta.updateStateCandidate? state database =
      some delta)
    (converted : CoreChunkPageDelta.writes delta.table = some baseWrites)
    (distinct : finalWrites.Pairwise
      (fun left right => left.pageId ≠ right.pageId))
    (baseMember : ∀ write ∈ baseWrites, write ∈ finalWrites)
    (schemaSame : delta.table.before.table.schema =
      delta.table.after.table.schema)
    (before : TableOnSource (CorePageSource.ofStorageImage image)
      delta.table.before)
    (beforeInline : before.encoding.overflowPages = [])
    (afterEncoding : CorePageCodec.OverflowEncoding)
    (afterEncoded : CorePageCodec.encodeChunkNodeWithOverflow
      delta.table.after.table.schema delta.table.after.tree.root
      before.nextOverflow = some afterEncoding)
    (addedUntouched : ∀ write ∈ finalWrites, write ∉ baseWrites →
      ∀ page ∈ afterEncoding.treePages,
        write.pageId + 1 ≠ page.pageNumber)
    (afterInline : afterEncoding.overflowPages = [])
    (oldBounds : ∀ page ∈ before.encoding.treePages,
      0 < page.pageNumber ∧ page.pageNumber ≤ image.pageCount)
    (heightBound : delta.table.after.tree.root.erase.height <
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)).pageCount + 1) :
    TableOnSource
      (CorePageSource.ofStorageImage
        (GrowableStorage.applyWrites image finalWrites)) delta.table.after := by
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
  have treeContains := pageSourceContains_updateStateCandidateTree_extension
    image state database delta baseWrites finalWrites before.encoding.treePages
    afterEncoding.treePages updated converted distinct baseMember addedUntouched
    beforeTree afterTree before.treeContains oldBounds
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
