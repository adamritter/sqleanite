import SQLeanite.CoreChunkPageDelta.DeleteTreePagesAccounted
import SQLeanite.CoreChunkPageState.TableStateBuildTable

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

theorem replaceBetween?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold replaceBetween? at success
  split at success
  next sameData =>
    injection success with equal
    subst delta
    unfold TableDelta.TreePagesAccounted
    dsimp only
    intro beforePages afterPages beforeEncoded afterEncoded page member
    right
    have pagesEqual : beforePages = afterPages := Option.some.inj
      (beforeEncoded.symm.trans afterEncoded)
    simpa [pagesEqual] using member
  next =>
    split at success
    next =>
      cases inserted : firstInserted state.table.rows replacement.rows with
      | none => simp [inserted] at success
      | some row =>
          simp only [inserted, Option.bind_eq_bind, Option.bind] at success
          cases insertionResult : insert? state nextPage row replacement with
          | none =>
              rw [insertionResult] at success
              exact splitInsert?_treePagesAccounted success
          | some candidate =>
              rw [insertionResult] at success
              simp only [Option.some.injEq] at success
              subst candidate
              exact insert?_treePagesAccounted insertionResult
    next =>
      split at success
      next =>
        cases deleted : firstDeleted state.table.rows replacement.rows with
        | none => simp [deleted] at success
        | some row =>
            simp only [deleted, Option.bind_eq_bind, Option.bind] at success
            cases deletionResult : delete? state nextPage row replacement with
            | none =>
                rw [deletionResult] at success
                exact mergeDelete?_treePagesAccounted success
            | some candidate =>
                rw [deletionResult] at success
                simp only [Option.some.injEq] at success
                subst candidate
                exact delete?_treePagesAccounted deletionResult
      next =>
        split at success
        next => exact retainMany?_treePagesAccounted success
        next =>
          cases difference : firstDifference state.table.rows
              replacement.rows with
          | none => simp [difference] at success
          | some row =>
              simp only [difference, Option.bind_eq_bind, Option.bind]
                at success
              cases replacementResult : replace? state nextPage row
                  replacement with
              | some candidate =>
                  rw [replacementResult] at success
                  simp only [Option.some.injEq] at success
                  subst candidate
                  exact replace?_treePagesAccounted replacementResult
              | none =>
                  rw [replacementResult] at success
                  exact replaceMany?_treePagesAccounted success

theorem replaceBetween?_encodabilityPreserved
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.EncodabilityPreserved := by
  unfold replaceBetween? at success
  split at success
  next sameData =>
    injection success with equal
    subst delta
    unfold TableDelta.EncodabilityPreserved
    dsimp only
    intro beforePages beforeEncoded
    exact ⟨beforePages, beforeEncoded⟩
  next =>
    split at success
    next =>
      cases inserted : firstInserted state.table.rows replacement.rows with
      | none => simp [inserted] at success
      | some row =>
          simp only [inserted, Option.bind_eq_bind, Option.bind] at success
          cases insertionResult : insert? state nextPage row replacement with
          | none =>
              rw [insertionResult] at success
              exact splitInsert?_encodabilityPreserved success
          | some candidate =>
              rw [insertionResult] at success
              simp only [Option.some.injEq] at success
              subst candidate
              exact insert?_encodabilityPreserved insertionResult
    next =>
      split at success
      next =>
        cases deleted : firstDeleted state.table.rows replacement.rows with
        | none => simp [deleted] at success
        | some row =>
            simp only [deleted, Option.bind_eq_bind, Option.bind] at success
            cases deletionResult : delete? state nextPage row replacement with
            | none =>
                rw [deletionResult] at success
                exact mergeDelete?_encodabilityPreserved success
            | some candidate =>
                rw [deletionResult] at success
                simp only [Option.some.injEq] at success
                subst candidate
                exact delete?_encodabilityPreserved deletionResult
      next =>
        split at success
        next => exact retainMany?_encodabilityPreserved success
        next =>
          cases difference : firstDifference state.table.rows
              replacement.rows with
          | none => simp [difference] at success
          | some row =>
              simp only [difference, Option.bind_eq_bind, Option.bind]
                at success
              cases replacementResult : replace? state nextPage row
                  replacement with
              | some candidate =>
                  rw [replacementResult] at success
                  simp only [Option.some.injEq] at success
                  subst candidate
                  exact replace?_encodabilityPreserved replacementResult
              | none =>
                  rw [replacementResult] at success
                  exact replaceMany?_encodabilityPreserved success

theorem replaceBetween?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.TreePagesSelected := by
  unfold replaceBetween? at success
  split at success
  next =>
    injection success with equal
    subst delta
    intro afterPages afterEncoded page member
    simp at member
  next =>
    split at success
    next =>
      cases inserted : firstInserted state.table.rows replacement.rows with
      | none => simp [inserted] at success
      | some row =>
          simp only [inserted, Option.bind_eq_bind, Option.bind] at success
          cases insertionResult : insert? state nextPage row replacement with
          | none =>
              rw [insertionResult] at success
              exact splitInsert?_treePagesSelected success
          | some candidate =>
              rw [insertionResult] at success
              simp only [Option.some.injEq] at success
              subst candidate
              exact insert?_treePagesSelected insertionResult
    next =>
      split at success
      next =>
        cases deleted : firstDeleted state.table.rows replacement.rows with
        | none => simp [deleted] at success
        | some row =>
            simp only [deleted, Option.bind_eq_bind, Option.bind] at success
            cases deletionResult : delete? state nextPage row replacement with
            | none =>
                rw [deletionResult] at success
                exact mergeDelete?_treePagesSelected success
            | some candidate =>
                rw [deletionResult] at success
                simp only [Option.some.injEq] at success
                subst candidate
                exact delete?_treePagesSelected deletionResult
      next =>
        split at success
        next => exact retainMany?_treePagesSelected success
        next =>
          cases difference : firstDifference state.table.rows
              replacement.rows with
          | none => simp [difference] at success
          | some row =>
              simp only [difference, Option.bind_eq_bind, Option.bind]
                at success
              cases replacementResult : replace? state nextPage row
                  replacement with
              | some candidate =>
                  rw [replacementResult] at success
                  simp only [Option.some.injEq] at success
                  subst candidate
                  exact replace?_treePagesSelected replacementResult
              | none =>
                  rw [replacementResult] at success
                  exact replaceMany?_treePagesSelected success

structure AlignedTables (target : List Core.Table) where
  tables : List CoreChunkPageState.TableState
  aligned : tables.map (fun state => state.table) = target
  nextPage : Nat
  delta : Option TableDelta

def alignTables? : Nat → List CoreChunkPageState.TableState →
    (target : List Core.Table) → Option (AlignedTables target)
  | nextPage, [], [] => some ⟨[], rfl, nextPage, none⟩
  | nextPage, old :: olds, replacement :: replacements =>
      if same : old.table.contents = replacement.contents then do
        let tail ← alignTables? nextPage olds replacements
        let retained := old.retarget replacement same
        some ⟨retained :: tail.tables, by
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨CoreChunkPageState.TableState.retarget_table
            old replacement same, tail.aligned⟩, tail.nextPage,
          tail.delta⟩
      else
        match headResult : replaceBetween? old nextPage replacement with
        | none => none
        | some head =>
            match alignTables? head.after.tree.nextPage olds replacements with
            | none => none
            | some tail =>
                if _onlyChange : tail.delta.isNone then
                  some ⟨head.after :: tail.tables, by
                    simp [replaceBetween?_table headResult, tail.aligned],
                    tail.nextPage, some head⟩
                else none
  | _, _, _ => none

theorem alignTables?_nextPage_none :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target},
      alignTables? nextPage states target = some aligned →
      aligned.delta = none → aligned.nextPage = nextPage
  | _, [], target, aligned, success, noChange => by
      cases target with
      | nil =>
          simp only [alignTables?, Option.some.injEq] at success
          subst aligned
          rfl
      | cons _ _ => simp [alignTables?] at success
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
            exact alignTables?_nextPage_none (target := replacements)
              (aligned := tail) tailResult noChange
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

theorem alignTables?_delta_treePagesAccounted :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta → delta.TreePagesAccounted := by
  intro nextPage states
  induction states generalizing nextPage with
  | nil =>
      intro target aligned delta success selected
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | cons old olds induction =>
      intro target aligned delta success selected
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
            exact induction tailResult selected
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
                  subst delta
                  exact replaceBetween?_treePagesAccounted headResult
                next => contradiction

theorem alignTables?_delta_encodabilityPreserved :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta → delta.EncodabilityPreserved := by
  intro nextPage states
  induction states generalizing nextPage with
  | nil =>
      intro target aligned delta success selected
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | cons old olds induction =>
      intro target aligned delta success selected
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
            exact induction tailResult selected
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
                  subst delta
                  exact replaceBetween?_encodabilityPreserved headResult
                next => contradiction

theorem alignTables?_delta_treePagesSelected :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta → delta.TreePagesSelected := by
  intro nextPage states
  induction states generalizing nextPage with
  | nil =>
      intro target aligned delta success selected
      cases target <;> simp [alignTables?] at success
      subst aligned
      simp at selected
  | cons old olds induction =>
      intro target aligned delta success selected
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
            exact induction tailResult selected
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
                  subst delta
                  exact replaceBetween?_treePagesSelected headResult
                next => contradiction

structure StateDelta where
  before : CoreChunkPageState.State
  after : CoreChunkPageState.State
  table : TableDelta

/-- Physical identity is deliberately separate from logical tree erasure.
`PersistentPageTree`'s semantic proofs forget page IDs, so this invariant rules
out duplicate active pages and prevents a released page from remaining live. -/
def TableDelta.IdentityWellFormed (delta : TableDelta) : Prop :=
  delta.after.tree.root.pageIds.Nodup ∧
    delta.freedPageNumbers.Nodup ∧
    ∀ pageId ∈ delta.freedPageNumbers,
      pageId ∉ delta.after.tree.root.pageIds

instance (delta : TableDelta) : Decidable delta.IdentityWellFormed :=
  inferInstanceAs (Decidable
    (delta.after.tree.root.pageIds.Nodup ∧
      delta.freedPageNumbers.Nodup ∧
      ∀ pageId ∈ delta.freedPageNumbers,
        pageId ∉ delta.after.tree.root.pageIds))

def indexImage (table : Core.Table) :
    List (Core.Index × List CoreDecode.IndexEntry) :=
  table.indexes.map fun index =>
    (index, CoreDecode.expectedIndexEntries table index)

def indexEntryOfRow (index : Core.Index) (row : Core.Row) :
    CoreDecode.IndexEntry :=
  ⟨row.value index.column, row.rowid⟩

def indexEntryLess (left right : CoreDecode.IndexEntry) : Bool :=
  match PhysicalQuery.compareValue left.value right.value with
  | .lt => true
  | .gt => false
  | .eq => left.rowid.value < right.rowid.value

def insertIndexEntry (entry : CoreDecode.IndexEntry) :
    List CoreDecode.IndexEntry → List CoreDecode.IndexEntry
  | [] => [entry]
  | candidate :: entries =>
      if indexEntryLess entry candidate then entry :: candidate :: entries
      else candidate :: insertIndexEntry entry entries

def integerIndexEntryKey (entry : CoreDecode.IndexEntry) : Int :=
  match entry.value with
  | .integer value => value.value
  | _ => 0

def integerIndexEntryLe (left right : CoreDecode.IndexEntry) : Bool :=
  decide (integerIndexEntryKey left < integerIndexEntryKey right ∨
    (integerIndexEntryKey left = integerIndexEntryKey right ∧
      left.rowid.value ≤ right.rowid.value))

def indexEntriesInteger (entries : List CoreDecode.IndexEntry) : Bool :=
  entries.all fun entry => CoreFile.valueIsInteger entry.value

def textIndexEntrySortKey (entry : CoreDecode.IndexEntry) :
    List UInt8 × Int :=
  let bytes := match entry.value with
    | .text value => value.bytes
    | _ => []
  (bytes, entry.rowid.value)

def textIndexEntryLe (left right : CoreDecode.IndexEntry) : Bool :=
  (compare (textIndexEntrySortKey left) (textIndexEntrySortKey right)).isLE

end CoreChunkPageDelta

end SQLeanite
