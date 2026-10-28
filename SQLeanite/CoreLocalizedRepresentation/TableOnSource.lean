import SQLeanite.CoreChunkPageDelta.AlignTablesTablePageIdsChangedIndexed
import SQLeanite.CorePageSource

namespace SQLeanite
namespace CoreLocalizedRepresentation

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

end CoreLocalizedRepresentation

end SQLeanite
