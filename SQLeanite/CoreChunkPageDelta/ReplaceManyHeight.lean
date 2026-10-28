import SQLeanite.CoreChunkPageDelta.IndexEntryLessEqTextCompare
import SQLeanite.CoreChunkPageDelta.ReplaceBefore
import SQLeanite.CorePageCodec.LookupTableRangeFromEncodeChunkNodeWithOverflowExact

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

private theorem replaceMany?_height
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.tree.root.erase.height = state.tree.root.erase.height := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        have height : updated.1.root.erase.height =
            state.tree.root.erase.height := by
          have preserved := replaceManyFold_height_of_noAllocation
            updatedResult (by simpa using noAllocation)
          simpa using preserved
        injection success with equal
        subst delta
        exact height
      next => contradiction
    next => contradiction
  next => contradiction

private theorem retainMany?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold retainMany? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
      rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
      injection success with equal
      subst delta
      have root := retainManyFold_rootId state.tree.root.erase.toList
        { state.tree with nextPage } replacement.rows [] updated updatedResult
      simpa using root
    next => contradiction
  next => contradiction

private theorem splitInsert?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (oldRoot : state.tree.root.rootId < nextPage)
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some_iff.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨deleted, deletedResult, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some_iff.mp success with ⟨pages, _, success⟩
        let updated := Core.orderedUpsert row entry.2
        let splitAt := updated.length / 2
        let left := updated.take splitAt
        let right := updated.drop splitAt
        let deleting : PersistentPageTree.Store CoreChunkPageState.Chunk :=
          { state.tree with nextPage }
        let first := deleted.1.insert leftKey left
        let allocated := first.insert rightKey right
        have deletedRoot : deleted.1.root.rootId = state.tree.root.rootId := by
          have root := PersistentPageTree.Store.delete?_rootId deletedResult
          simpa [deleting] using root
        have firstRoot : first.root.rootId = deleted.1.root.rootId :=
          deleted.1.insert_rootId leftKey left
        have allocatedRoot : allocated.root.rootId = first.root.rootId :=
          first.insert_rootId rightKey right
        have allocatedOld : allocated.root.rootId < nextPage := by
          rw [allocatedRoot, firstRoot, deletedRoot]
          exact oldRoot
        have reusedRoot := allocated.reuseFresh_getD_rootId nextPage deleted.2
          allocatedOld
        injection success with equal
        subst delta
        simpa [updated, splitAt, left, right, deleting, first, allocated]
          using reusedRoot.trans (allocatedRoot.trans (firstRoot.trans deletedRoot))
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceBetween?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.before = state := by
  unfold replaceBetween? at success
  split at success
  next => injection success with equal; subst delta; rfl
  next =>
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
      cases insertion : insert? state nextPage row replacement with
      | some candidate =>
          rw [insertion] at success
          injection success with equal
          subst candidate
          exact insert?_before insertion
      | none =>
          rw [insertion] at success
          exact splitInsert?_before success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
        cases deletion : delete? state nextPage row replacement with
        | some candidate =>
            rw [deletion] at success
            injection success with equal
            subst candidate
            exact delete?_before deletion
        | none =>
            rw [deletion] at success
            exact mergeDelete?_before success
      next =>
        split at success
        next => exact retainMany?_before success
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
          cases replacementResult : replace? state nextPage row replacement with
          | some candidate =>
              rw [replacementResult] at success
              injection success with equal
              subst candidate
              exact replace?_before replacementResult
          | none =>
              rw [replacementResult] at success
              exact replaceMany?_before success

/-- Every localized data mutation retains the table's SQLite root page.  Root
splits keep the existing root identity, deletion shrink repairs back to it,
and fresh-page recycling cannot relabel an old root below the allocation
watermark. -/
theorem replaceBetween?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (oldRoot : state.tree.root.rootId < nextPage)
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold replaceBetween? at success
  split at success
  next => injection success with equal; subst delta; rfl
  next =>
    split at success
    next =>
      rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
      cases insertion : insert? state nextPage row replacement with
      | some candidate =>
          rw [insertion] at success
          injection success with equal
          subst candidate
          exact insert?_rootId insertion
      | none =>
          rw [insertion] at success
          exact splitInsert?_rootId oldRoot success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
        cases deletion : delete? state nextPage row replacement with
        | some candidate =>
            rw [deletion] at success
            injection success with equal
            subst candidate
            exact delete?_rootId deletion
        | none =>
            rw [deletion] at success
            exact mergeDelete?_rootId success
      next =>
        split at success
        next => exact retainMany?_rootId success
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
          cases replacementResult : replace? state nextPage row replacement with
          | some candidate =>
              rw [replacementResult] at success
              injection success with equal
              subst candidate
              exact replace?_rootId replacementResult
          | none =>
              rw [replacementResult] at success
              exact replaceMany?_rootId success

/-- Equal-cardinality table replacement cannot take an allocating insert or a
deleting branch.  Both remaining update algorithms preserve every page
identity, so a separately allocated physical index interval stays disjoint. -/
theorem replaceBetween?_pageIds_of_length_eq
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (sameLength : replacement.rows.length = state.table.rows.length)
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.after.tree.root.pageIds = state.tree.root.pageIds := by
  unfold replaceBetween? at success
  split at success
  next => injection success with equal; subst delta; rfl
  next =>
    split at success
    next inserted => omega
    next =>
      split at success
      next deleted => omega
      next =>
        split at success
        next retained => omega
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
          cases replacementResult : replace? state nextPage row replacement with
          | some candidate =>
              rw [replacementResult] at success
              injection success with equal
              subst candidate
              exact replace?_pageIds replacementResult
          | none =>
              rw [replacementResult] at success
              exact replaceMany?_pageIds success

/-- Equal-cardinality replacement also preserves the recursive tree height,
so a validated decoder fuel bound remains valid after the local mutation. -/
theorem replaceBetween?_height_of_length_eq
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (sameLength : replacement.rows.length = state.table.rows.length)
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.after.tree.root.erase.height = state.tree.root.erase.height := by
  unfold replaceBetween? at success
  split at success
  next => injection success with equal; subst delta; rfl
  next =>
    split at success
    next inserted => omega
    next =>
      split at success
      next deleted => omega
      next =>
        split at success
        next retained => omega
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
          cases replacementResult : replace? state nextPage row replacement with
          | some candidate =>
              rw [replacementResult] at success
              injection success with equal
              subst candidate
              exact replace?_height replacementResult
          | none =>
              rw [replacementResult] at success
              exact replaceMany?_height success

/-- Equal-cardinality replacement is an in-place update: neither point nor
bulk replacement releases a page to the SQLite freelist. -/
theorem replaceBetween?_freedPageNumbers_of_length_eq
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (sameLength : replacement.rows.length = state.table.rows.length)
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.freedPageNumbers = [] := by
  unfold replaceBetween? at success
  split at success
  next => injection success with equal; subst delta; rfl
  next =>
    split at success
    next inserted => omega
    next =>
      split at success
      next deleted => omega
      next =>
        split at success
        next retained => omega
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
          cases replacementResult : replace? state nextPage row replacement with
          | some candidate =>
              rw [replacementResult] at success
              injection success with equal
              subst candidate
              exact replace?_freedPageNumbers replacementResult
          | none =>
              rw [replacementResult] at success
              exact replaceMany?_freedPageNumbers success

/-- An equal-cardinality data update with unchanged index metadata follows the
in-place replacement branches and leaves the allocator watermark untouched.
The explicit non-equivalence excludes the metadata-only `retargetData` arm,
whose table-local historical watermark need not equal the current database
watermark. -/
theorem replaceBetween?_after_nextPage_of_data_update
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (sameLength : replacement.rows.length = state.table.rows.length)
    (sameIndexes : state.table.indexes = replacement.indexes)
    (changed : ¬ state.table.Equiv replacement)
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.after.tree.nextPage = nextPage := by
  unfold replaceBetween? at success
  split at success
  next sameData =>
    exfalso
    apply changed
    unfold Core.Table.Equiv Core.Table.contents
    rw [sameData.1, sameData.2.1, sameData.2.2, sameIndexes]
  next =>
    split at success
    next inserted => omega
    next =>
      split at success
      next deleted => omega
      next =>
        split at success
        next retained => omega
        next =>
          rcases Option.bind_eq_some_iff.mp success with ⟨row, _, success⟩
          cases replacementResult : replace? state nextPage row replacement with
          | some candidate =>
              rw [replacementResult] at success
              injection success with equal
              subst candidate
              exact replace?_after_nextPage replacementResult
          | none =>
              rw [replacementResult] at success
              exact replaceMany?_after_nextPage success

theorem replaceBetween?_catalogEntry
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (oldRoot : state.tree.root.rootId < nextPage)
    (success : replaceBetween? state nextPage replacement = some delta)
    (sufficient : delta.tablePagesSufficient = true) :
    CorePageCodec.chunkTableCatalogEntry delta.after =
      CorePageCodec.chunkTableCatalogEntry state := by
  have metadata := TableDelta.tablePagesSufficient_metadata delta sufficient
  rw [replaceBetween?_before success] at metadata
  have root := replaceBetween?_rootId oldRoot success
  unfold CorePageCodec.chunkTableCatalogEntry
    CoreChunkPageState.TableState.rootPage
  simp only [metadata.1, root, CoreFile.tableSQL, metadata.2.2]

/-- A successful alignment with no selected table delta consists entirely of
catalog-metadata-preserving retargets. -/
theorem alignTables?_metadata_none :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target},
      alignTables? nextPage states target = some aligned →
      aligned.delta = none →
      TablesMetadataAligned
        (states.map fun state => state.table) target
  | _, [], target, aligned, success, noChange => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      exact .nil
  | nextPage, old :: olds, target, aligned, success, noChange => by
      cases target with
      | nil => simp [alignTables?] at success
      | cons replacement replacements =>
          unfold alignTables? at success
          split at success
          next same =>
            rcases Option.bind_eq_some_iff.mp success with
              ⟨tail, tailResult, success⟩
            injection success with equal
            subst aligned
            refine .cons ⟨?_, ?_, ?_⟩
              (alignTables?_metadata_none tailResult noChange)
            · exact Core.Table.Equiv.schema_eq same
            · exact Core.Table.Equiv.indexes_eq same
            · exact Core.Table.Equiv.catalogSQL_eq same
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

/-- With one selected table delta, the sufficient-table fast-path check proves
that the changed head also preserves catalog metadata; all remaining tables
come from `alignTables?_metadata_none`. -/
theorem alignTables?_metadata_changed :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.tablePagesSufficient = true →
      TablesMetadataAligned
        (states.map fun state => state.table) target
  | _, [], target, aligned, delta, success, selected, sufficient => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, old :: olds, target, aligned, delta, success, selected,
      sufficient => by
      cases target with
      | nil => simp [alignTables?] at success
      | cons replacement replacements =>
          unfold alignTables? at success
          split at success
          next same =>
            rcases Option.bind_eq_some_iff.mp success with
              ⟨tail, tailResult, success⟩
            injection success with equal
            subst aligned
            refine .cons ⟨Core.Table.Equiv.schema_eq same,
              Core.Table.Equiv.indexes_eq same, Core.Table.Equiv.catalogSQL_eq same⟩
              (alignTables?_metadata_changed tailResult selected sufficient)
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
                  have headMetadata :=
                    TableDelta.tablePagesSufficient_metadata delta sufficient
                  rw [replaceBetween?_before headResult,
                    replaceBetween?_table headResult] at headMetadata
                  exact .cons headMetadata
                    (alignTables?_metadata_none tailResult tailNone)
                next => contradiction

end CoreChunkPageDelta

end SQLeanite
