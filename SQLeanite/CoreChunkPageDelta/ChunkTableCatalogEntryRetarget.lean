import SQLeanite.CoreChunkPageDelta.ReplaceManyHeight

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

private theorem chunkTableCatalogEntry_retarget
    (state : CoreChunkPageState.TableState) (table : Core.Table)
    (equivalent : state.table.Equiv table) :
    CorePageCodec.chunkTableCatalogEntry (state.retarget table equivalent) =
      CorePageCodec.chunkTableCatalogEntry state := by
  unfold CorePageCodec.chunkTableCatalogEntry
    CoreChunkPageState.TableState.rootPage
  simp only [CoreChunkPageState.TableState.retarget_table,
    CoreChunkPageState.TableState.retarget_tree, equivalent.schema_eq,
    CoreFile.tableSQL, equivalent.catalogSQL_eq]

theorem alignTables?_catalogEntries_none :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target},
      alignTables? nextPage states target = some aligned →
      aligned.delta = none →
      aligned.tables.map CorePageCodec.chunkTableCatalogEntry =
        states.map CorePageCodec.chunkTableCatalogEntry
  | _, [], target, aligned, success, noChange => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      rfl
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
            simp only [List.map_cons, List.cons.injEq]
            exact ⟨chunkTableCatalogEntry_retarget old replacement same,
              alignTables?_catalogEntries_none tailResult noChange⟩
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

theorem alignTables?_catalogEntries_changed :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      (∀ state ∈ states, state.tree.root.rootId < nextPage) →
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.tablePagesSufficient = true →
      aligned.tables.map CorePageCodec.chunkTableCatalogEntry =
        states.map CorePageCodec.chunkTableCatalogEntry
  | _, [], target, aligned, delta, roots, success, selected, sufficient => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, old :: olds, target, aligned, delta, roots, success, selected,
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
            simp only [List.map_cons, List.cons.injEq]
            refine ⟨chunkTableCatalogEntry_retarget old replacement same,
              alignTables?_catalogEntries_changed ?_ tailResult selected
                sufficient⟩
            intro state member
            exact roots state (by simp [member])
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
                  simp only [List.map_cons, List.cons.injEq]
                  exact ⟨replaceBetween?_catalogEntry
                      (roots old (by simp)) headResult sufficient,
                    alignTables?_catalogEntries_none tailResult tailNone⟩
                next => contradiction

/-- The selected table in an indexed ordinary delta keeps its complete page
identity list.  `tablePagesSufficient` forces equal row cardinality when an
index exists, excluding the allocating/deleting alignment branches. -/
theorem alignTables?_selectedPageIds_of_indexed :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.tablePagesSufficient = true →
      delta.before.table.indexes ≠ [] →
      delta.after.tree.root.pageIds = delta.before.tree.root.pageIds
  | _, [], target, aligned, delta, success, selected, sufficient,
      indexed => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, old :: olds, target, aligned, delta, success, selected,
      sufficient, indexed => by
      cases target with
      | nil => simp [alignTables?] at success
      | cons replacement replacements =>
        unfold alignTables? at success
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          exact alignTables?_selectedPageIds_of_indexed tailResult selected
            sufficient indexed
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
                have headEqual : head = delta := Option.some.inj selected
                subst head
                have sameLength :=
                  delta.tablePagesSufficient_rowsLength_of_indexed sufficient
                    indexed
                rw [replaceBetween?_before headResult,
                  replaceBetween?_table headResult] at sameLength
                have pages := replaceBetween?_pageIds_of_length_eq
                  (state := old) (replacement := replacement)
                  (delta := delta) sameLength headResult
                rw [replaceBetween?_before headResult]
                exact pages
              next => contradiction

/-- The selected indexed table keeps the same balanced-tree height for the
same equal-cardinality reason that preserves all of its page identities. -/
theorem alignTables?_selectedHeight_of_indexed :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.tablePagesSufficient = true →
      delta.before.table.indexes ≠ [] →
      delta.after.tree.root.erase.height =
        delta.before.tree.root.erase.height
  | _, [], target, aligned, delta, success, selected, sufficient,
      indexed => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, old :: olds, target, aligned, delta, success, selected,
      sufficient, indexed => by
      cases target with
      | nil => simp [alignTables?] at success
      | cons replacement replacements =>
        unfold alignTables? at success
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          exact alignTables?_selectedHeight_of_indexed tailResult selected
            sufficient indexed
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
                have headEqual : head = delta := Option.some.inj selected
                subst head
                have sameLength :=
                  delta.tablePagesSufficient_rowsLength_of_indexed sufficient
                    indexed
                rw [replaceBetween?_before headResult,
                  replaceBetween?_table headResult] at sameLength
                have height := replaceBetween?_height_of_length_eq
                  (state := old) (replacement := replacement)
                  (delta := delta) sameLength headResult
                rw [replaceBetween?_before headResult]
                exact height
              next => contradiction

/-- The same indexed equal-cardinality alignment cannot release a table page.
This is the freelist half of the stable-identity result above. -/
theorem alignTables?_selectedFreedPages_of_indexed :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.tablePagesSufficient = true →
      delta.before.table.indexes ≠ [] →
      delta.freedPageNumbers = []
  | _, [], target, aligned, delta, success, selected, sufficient,
      indexed => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, old :: olds, target, aligned, delta, success, selected,
      sufficient, indexed => by
      cases target with
      | nil => simp [alignTables?] at success
      | cons replacement replacements =>
        unfold alignTables? at success
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          exact alignTables?_selectedFreedPages_of_indexed tailResult selected
            sufficient indexed
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
                have headEqual : head = delta := Option.some.inj selected
                subst head
                have sameLength :=
                  delta.tablePagesSufficient_rowsLength_of_indexed sufficient
                    indexed
                rw [replaceBetween?_before headResult,
                  replaceBetween?_table headResult] at sameLength
                exact replaceBetween?_freedPageNumbers_of_length_eq sameLength
                  headResult
              next => contradiction

/-- Indexed ordinary updates preserve the database allocator watermark as
well as the active page-ID list.  The recursive proof follows the one selected
table through alignment and proves the unchanged tail returns the watermark it
was given. -/
theorem alignTables?_nextPage_changed_indexed :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.tablePagesSufficient = true →
      delta.before.table.indexes ≠ [] →
      aligned.nextPage = nextPage
  | _, [], target, aligned, delta, success, selected, sufficient,
      indexed => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, old :: olds, target, aligned, delta, success, selected,
      sufficient, indexed => by
      cases target with
      | nil => simp [alignTables?] at success
      | cons replacement replacements =>
        unfold alignTables? at success
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          exact alignTables?_nextPage_changed_indexed (target := replacements)
            (aligned := tail) tailResult selected sufficient indexed
        next changed =>
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
                have headEqual : head = delta := Option.some.inj selected
                subst head
                have tailNone : tail.delta = none := by
                  cases tailDelta : tail.delta with
                  | none => rfl
                  | some value => simp [tailDelta] at *
                have sameLength :=
                  delta.tablePagesSufficient_rowsLength_of_indexed sufficient
                    indexed
                have metadata :=
                  delta.tablePagesSufficient_metadata sufficient
                rw [replaceBetween?_before headResult,
                  replaceBetween?_table headResult] at sameLength metadata
                have headNext := replaceBetween?_after_nextPage_of_data_update
                  sameLength metadata.2.1 changed headResult
                exact (alignTables?_nextPage_none tailResult tailNone).trans
                  headNext
              next => contradiction

theorem alignTables?_selected_mem :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.before ∈ states ∧ delta.after ∈ aligned.tables
  | _, [], target, aligned, delta, success, selected => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | nextPage, old :: olds, target, aligned, delta, success, selected => by
      cases target with
      | nil => simp [alignTables?] at success
      | cons replacement replacements =>
        unfold alignTables? at success
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          have found := alignTables?_selected_mem tailResult selected
          exact ⟨by simp [found.1], by simp [found.2]⟩
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
                have headEqual : head = delta := Option.some.inj selected
                subst head
                rw [replaceBetween?_before headResult]
                exact ⟨by simp, by simp⟩
              next => contradiction

theorem alignTables?_tablePageIds_none :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target},
      alignTables? nextPage states target = some aligned →
      aligned.delta = none →
      CoreChunkPageState.tablePageIds aligned.tables =
        CoreChunkPageState.tablePageIds states
  | _, [], target, aligned, success, noChange => by
      cases target <;> simp [alignTables?] at success
      subst aligned
      rfl
  | nextPage, old :: olds, target, aligned, success, noChange => by
      cases target with
      | nil => simp [alignTables?] at success
      | cons replacement replacements =>
        unfold alignTables? at success
        split at success
        next =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          unfold CoreChunkPageState.tablePageIds
          simp only [List.flatMap_cons,
            CoreChunkPageState.TableState.retarget_tree]
          exact congrArg (old.tree.root.pageIds ++ ·)
            (alignTables?_tablePageIds_none tailResult noChange)
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

end CoreChunkPageDelta

end SQLeanite
