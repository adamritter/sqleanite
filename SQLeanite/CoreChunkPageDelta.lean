import SQLeanite.CorePageCodec

namespace SQLeanite
namespace CoreChunkPageDelta


structure TableDelta where
  before : CoreChunkPageState.TableState
  after : CoreChunkPageState.TableState
  chunkKey : Nat
  pages : List CorePageCodec.NumberedPage
  /-- Structural mutations may touch two old search paths.  Ordinary point
  mutations leave this absent and reconstruct their single old path. -/
  beforePages? : Option (List CorePageCodec.NumberedPage) := none
  freedPageNumbers : List Nat := []

/-- Every complete post-state tree page is either emitted by the delta or is
byte-identical to a page in the complete pre-state tree encoding.  The
post-state schema is used on both sides; schema preservation is a separate
database-level frame fact. -/
def TableDelta.TreePagesAccounted (delta : TableDelta) : Prop :=
  ∀ (beforePages afterPages : List CorePageCodec.NumberedPage),
    CorePageCodec.encodeChunkNode delta.after.table.schema
        delta.before.tree.root = some beforePages →
    CorePageCodec.encodeChunkNode delta.after.table.schema
        delta.after.tree.root = some afterPages →
    ∀ page ∈ afterPages, page ∈ delta.pages ∨ page ∈ beforePages

/-- Every selected page is an exact member of the complete post-state tree
encoding.  This is deliberately separate from `TreePagesAccounted`: together
they give the two directions required to preserve an image without a runtime
decode-and-compare pass. -/
def TableDelta.TreePagesSelected (delta : TableDelta) : Prop :=
  ∀ (afterPages : List CorePageCodec.NumberedPage),
    CorePageCodec.encodeChunkNode delta.after.table.schema
        delta.after.tree.root = some afterPages →
    ∀ page ∈ delta.pages, page ∈ afterPages

def maximumTreeKey? (node : PersistentPageTree.Node
    CoreChunkPageState.Chunk) : Option Nat :=
  node.erase.toList.getLast?.map (fun entry => entry.1)

/-- Locate the chunk whose upper rowid bound contains `key`.  Unlike ordinary
tree lookup, routing uses the maximum key of each left child because keys
inside a packed chunk are not individual tree entries. -/
def findChunkFor? (key : Nat) :
    PersistentPageTree.Node CoreChunkPageState.Chunk →
      Option (PagedBTree.Entry CoreChunkPageState.Chunk)
  | .leaf _ entries =>
      match entries.find? (fun entry => key ≤ entry.1) with
      | some entry => some entry
      | none => entries.getLast?
  | .branch2 _ left _ right => do
      let leftMax ← maximumTreeKey? left
      if key ≤ leftMax then findChunkFor? key left else findChunkFor? key right
  | .branch3 _ left _ middle _ right => do
      let leftMax ← maximumTreeKey? left
      if key ≤ leftMax then findChunkFor? key left
      else
        let middleMax ← maximumTreeKey? middle
        if key ≤ middleMax then findChunkFor? key middle
        else findChunkFor? key right

def replaceRow (target : Core.Row) (chunk : CoreChunkPageState.Chunk) :
    CoreChunkPageState.Chunk :=
  chunk.map fun row => if row.rowid = target.rowid then target else row

def firstDifference : List Core.Row → List Core.Row → Option Core.Row
  | [], [] => none
  | [], row :: _ => some row
  | _ :: _, [] => none
  | old :: olds, row :: rows =>
      if old = row then firstDifference olds rows else some row

/-- First row present only on the right of two rowid-ordered streams.  The old
implementation nested `find?` and `any`, making a tail insertion quadratic. -/
def firstInserted : List Core.Row → List Core.Row → Option Core.Row
  | [], [] => none
  | [], row :: _ => some row
  | _ :: _, [] => none
  | old :: olds, row :: rows =>
      if old.rowid = row.rowid then firstInserted olds rows
      else if row.rowid.value < old.rowid.value then some row
      else firstInserted olds (row :: rows)

/-- First row present only on the left, by the symmetric linear merge. -/
def firstDeleted : List Core.Row → List Core.Row → Option Core.Row
  | [], _ => none
  | old :: _, [] => some old
  | old :: olds, row :: rows =>
      if old.rowid = row.rowid then firstDeleted olds rows
      else if old.rowid.value < row.rowid.value then some old
      else firstDeleted (old :: olds) rows

theorem firstInserted_mem_after {before after : List Core.Row} {row : Core.Row}
    (found : firstInserted before after = some row) : row ∈ after := by
  induction before generalizing after with
  | nil =>
      cases after <;> simp [firstInserted] at found ⊢
      exact .inl found.symm
  | cons old olds induction =>
      cases after with
      | nil => simp [firstInserted] at found
      | cons next rows =>
          simp only [firstInserted] at found
          split at found
          next => exact List.Mem.tail next (induction found)
          next =>
            split at found
            next => simp_all
            next => exact induction found

theorem firstDeleted_mem_before {before after : List Core.Row} {row : Core.Row}
    (found : firstDeleted before after = some row) : row ∈ before := by
  induction after generalizing before with
  | nil =>
      cases before <;> simp [firstDeleted] at found ⊢
      exact .inl found.symm
  | cons next rows induction =>
      cases before with
      | nil => simp [firstDeleted] at found
      | cons old olds =>
          simp only [firstDeleted] at found
          split at found
          next => exact List.Mem.tail old (induction found)
          next =>
            split at found
            next => simp_all
            next => exact induction found

private def insertNumberedPage (page : CorePageCodec.NumberedPage) :
    List CorePageCodec.NumberedPage → List CorePageCodec.NumberedPage
  | [] => [page]
  | existing :: pages =>
      if existing.pageNumber = page.pageNumber then page :: pages
      else existing :: insertNumberedPage page pages

private def mergeNumberedPages (left right : List CorePageCodec.NumberedPage) :
    List CorePageCodec.NumberedPage :=
  right.foldl (fun pages page => insertNumberedPage page pages) left

/-- Encode selected identified nodes.  This is used only when topology changes;
the selected IDs are the old search paths plus freshly allocated pages, so the
write set remains logarithmic even though this proof-oriented collector walks
the in-memory tree to locate them. -/
def encodeChunkNodesWithIds (schema : Core.Schema) (ids : List Nat) :
    PersistentPageTree.Node CoreChunkPageState.Chunk →
      Option (List CorePageCodec.NumberedPage) := fun node =>
  ((CorePageCodec.physicalChunkPagesFast node).filter fun page =>
      ids.contains page.pageNumber).mapM
    (CorePageCodec.encodePhysicalChunkPage schema)

theorem treePagesAccounted_of_changedPhysical
    (schema : Core.Schema)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (encoded : (CorePageCodec.changedPhysicalChunkPagesFast before after).mapM
      (CorePageCodec.encodePhysicalChunkPage schema) = some pages) :
    ∀ (beforePages afterPages : List CorePageCodec.NumberedPage),
      CorePageCodec.encodeChunkNode schema before = some beforePages →
      CorePageCodec.encodeChunkNode schema after = some afterPages →
      ∀ page ∈ afterPages, page ∈ pages ∨ page ∈ beforePages := by
  rw [CorePageCodec.changedPhysicalChunkPagesFast_eq] at encoded
  intro beforePages afterPages beforeEncoded afterEncoded
  exact CorePageCodec.encodeChangedChunkPages_accounts schema before after
    beforePages afterPages pages beforeEncoded afterEncoded (by
      simpa [CorePageCodec.encodeChangedChunkPages] using encoded)

theorem treePagesAccounted_of_pathAgrees
    (schema : Core.Schema) (key : Nat)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (agrees : PersistentPageTree.Node.PathAgrees key before after)
    (encoded : CorePageCodec.encodeChunkPath schema key after = some pages) :
    ∀ (beforePages afterPages : List CorePageCodec.NumberedPage),
      CorePageCodec.encodeChunkNode schema before = some beforePages →
      CorePageCodec.encodeChunkNode schema after = some afterPages →
      ∀ page ∈ afterPages, page ∈ pages ∨ page ∈ beforePages := by
  intro beforePages afterPages beforeEncoded afterEncoded
  exact CorePageCodec.encodeChunkPath_accounts_of_pathAgrees schema key pages
    beforePages afterPages agrees encoded beforeEncoded afterEncoded

theorem treePagesSelected_of_changedPhysical
    (schema : Core.Schema)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (encoded : (CorePageCodec.changedPhysicalChunkPagesFast before after).mapM
      (CorePageCodec.encodePhysicalChunkPage schema) = some pages) :
    ∀ (afterPages : List CorePageCodec.NumberedPage),
      CorePageCodec.encodeChunkNode schema after = some afterPages →
      ∀ page ∈ pages, page ∈ afterPages := by
  rw [CorePageCodec.changedPhysicalChunkPagesFast_eq] at encoded
  intro afterPages afterEncoded
  exact CorePageCodec.encodeChangedChunkPages_subset schema before after
    afterPages pages afterEncoded (by
      simpa [CorePageCodec.encodeChangedChunkPages] using encoded)

theorem treePagesSelected_of_path
    (schema : Core.Schema) (key : Nat)
    (after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List CorePageCodec.NumberedPage)
    (encoded : CorePageCodec.encodeChunkPath schema key after = some pages) :
    ∀ (afterPages : List CorePageCodec.NumberedPage),
      CorePageCodec.encodeChunkNode schema after = some afterPages →
      ∀ page ∈ pages, page ∈ afterPages := by
  intro afterPages afterEncoded
  exact CorePageCodec.encodeChunkPath_subset_encodeChunkNode schema key after
    pages afterPages encoded afterEncoded

def replace? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _present : entry.2.any (fun old => old.rowid = row.rowid) then
    let updatedChunk := replaceRow row entry.2
    let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
      { state.tree with nextPage }
    let updatedTree := allocating.insert entry.1 updatedChunk
    if _noAllocation : updatedTree.nextPage = nextPage then
      if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
        let after : CoreChunkPageState.TableState :=
          ⟨replacement, updatedTree, represents⟩
        let pages ← CorePageCodec.encodeChunkPath replacement.schema
          entry.1 updatedTree.root
        some ⟨state, after, entry.1, pages, none, []⟩
      else none
    else none
  else none

def insert? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _fresh : !entry.2.any (fun old => old.rowid = row.rowid) then
    if _room : entry.2.length < CoreChunkPageState.chunkCapacity then
      let updatedChunk := Core.orderedUpsert row entry.2
      let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
        { state.tree with nextPage }
      let updatedTree := allocating.insert entry.1 updatedChunk
      if _noAllocation : updatedTree.nextPage = nextPage then
        if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
          let after : CoreChunkPageState.TableState :=
            ⟨replacement, updatedTree, represents⟩
          let pages ← CorePageCodec.encodeChunkPath replacement.schema
            entry.1 updatedTree.root
          some ⟨state, after, entry.1, pages, none, []⟩
        else none
      else none
    else none
  else none

/-- Split one full logical chunk and propagate the new entry through the
identified 2-3 tree. Existing nodes retain their page IDs; `Store.insert`
allocates only pages introduced by leaf/interior/root splits. -/
def splitInsert? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _fresh : !entry.2.any (fun old => old.rowid = row.rowid) then
    let updated := Core.orderedUpsert row entry.2
    if _full : CoreChunkPageState.chunkCapacity < updated.length then
      let splitAt := updated.length / 2
      let left := updated.take splitAt
      let right := updated.drop splitAt
      let leftKey ← CoreChunkPageState.chunkKey? left
      let rightKey ← CoreChunkPageState.chunkKey? right
      let deleting : PersistentPageTree.Store CoreChunkPageState.Chunk :=
        { state.tree with nextPage }
      -- The key of a physical chunk is its current maximum row key.  Merely
      -- replacing `entry.1` is wrong when an append raises that maximum: it
      -- leaves a stale routing bound even though flattening the chunks still
      -- yields the right rows. Remove the old keyed entry and insert both
      -- newly bounded halves.
      let deleted ← deleting.delete? entry.1
      let first := deleted.1.insert leftKey left
      let allocatedTree := first.insert rightKey right
      -- Removing the old full chunk can release exactly the pages needed by
      -- split propagation. Recycle them before exposing the delta so a table
      -- below a tail-owned index stays below that index.
      -- Recycling is an optimization, not a precondition for a valid split.
      -- A root/interior split can allocate more identities than deleting the
      -- old chunk releases; in that case retain the ordinary fresh layout.
      let reused := (allocatedTree.reuseFresh? nextPage deleted.2).getD
        (allocatedTree, deleted.2)
      let updatedTree := reused.1
      if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
        let changedPhysical := CorePageCodec.changedPhysicalChunkPagesFast
          state.tree.root updatedTree.root
        let changedIds := changedPhysical.map
          CorePageCodec.PhysicalChunkPage.pageNumber
        let beforeIds := changedIds ++ deleted.2
        let beforePages ← encodeChunkNodesWithIds state.table.schema beforeIds
          state.tree.root
        let pages ← changedPhysical.mapM
          (CorePageCodec.encodePhysicalChunkPage replacement.schema)
        let after : CoreChunkPageState.TableState :=
          ⟨replacement, updatedTree, represents⟩
        some ⟨state, after, entry.1, pages, some beforePages, reused.2⟩
      else none
    else none
  else none

def delete? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _present : entry.2.any (fun old => old.rowid = row.rowid) then
    let updatedChunk := entry.2.filter (fun old => old.rowid != row.rowid)
    if _nonempty : !updatedChunk.isEmpty then
      let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
        { state.tree with nextPage }
      let updatedTree := allocating.insert entry.1 updatedChunk
      if _noAllocation : updatedTree.nextPage = nextPage then
        if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
          let after : CoreChunkPageState.TableState :=
            ⟨replacement, updatedTree, represents⟩
          let pages ← CorePageCodec.encodeChunkPath replacement.schema
            entry.1 updatedTree.root
          some ⟨state, after, entry.1, pages, none, []⟩
        else none
      else none
    else none
  else none

/-- Remove a now-empty chunk with the stable-identity borrow/merge algorithm.
Absorbed physical pages are returned for SQLite freelist encoding. -/
def mergeDelete? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (row : Core.Row) (replacement : Core.Table) : Option TableDelta := do
  let entry ← findChunkFor? row.treeKey state.tree.root
  if _present : entry.2.any (fun old => old.rowid = row.rowid) then
    let updatedChunk := entry.2.filter (fun old => old.rowid != row.rowid)
    if _empty : updatedChunk.isEmpty then
      let deleting : PersistentPageTree.Store CoreChunkPageState.Chunk :=
        { state.tree with nextPage }
      let deleted ← deleting.delete? entry.1
      let updatedTree := deleted.1
      if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
        -- Borrow and merge can modify a sibling that is not on the deleted
        -- key's search path.  Select by stable identity from the exact
        -- before/after page difference so every changed sibling is written,
        -- and include every absorbed page in the preimage set used by the
        -- rollback journal.
        let changedPhysical := CorePageCodec.changedPhysicalChunkPagesFast
          state.tree.root updatedTree.root
        let changedIds := changedPhysical.map
          CorePageCodec.PhysicalChunkPage.pageNumber
        let beforeIds := changedIds ++ deleted.2
        let beforePages ← encodeChunkNodesWithIds state.table.schema beforeIds
          state.tree.root
        let pages ← changedPhysical.mapM
          (CorePageCodec.encodePhysicalChunkPage replacement.schema)
        let after : CoreChunkPageState.TableState :=
          ⟨replacement, updatedTree, represents⟩
        some ⟨state, after, entry.1, pages, some beforePages, deleted.2⟩
      else none
    else none
  else none

/-- Resolve every old chunk row through the replacement primary tree.  This is
the bulk-UPDATE case: rowids and chunk boundaries remain fixed while one or
more payloads change. -/
def replacementChunk? (rows : List Core.Row)
    (chunk : CoreChunkPageState.Chunk) :
    Option (CoreChunkPageState.Chunk × List Core.Row) :=
  let replacement := rows.take chunk.length
  if replacement.length = chunk.length &&
      replacement.map (·.rowid) = chunk.map (·.rowid) then
    some (replacement, rows.drop chunk.length)
  else none

/-- The proof-oriented bulk replacement loop, named separately so page
identity can be related to its accumulator without unfolding a higher-order
`foldlM` application. -/
def replaceManyFold :
    List (PagedBTree.Entry CoreChunkPageState.Chunk) →
      (PersistentPageTree.Store CoreChunkPageState.Chunk × List Core.Row) →
      Option (PersistentPageTree.Store CoreChunkPageState.Chunk × List Core.Row)
  | [], accumulator => some accumulator
  | entry :: entries, accumulator => do
      let resolved ← replacementChunk? accumulator.2 entry.2
      let tree := if resolved.1 = entry.2 then accumulator.1
        else accumulator.1.insert entry.1 resolved.1
      replaceManyFold entries (tree, resolved.2)

theorem replaceManyFold_nextPage_le :
    ∀ {entries : List (PagedBTree.Entry CoreChunkPageState.Chunk)}
      {store updated : PersistentPageTree.Store CoreChunkPageState.Chunk}
      {rows remaining : List Core.Row},
      replaceManyFold entries (store, rows) = some (updated, remaining) →
      store.nextPage ≤ updated.nextPage
  | [], store, updated, rows, remaining, success => by
      simp only [replaceManyFold, Option.some.injEq, Prod.mk.injEq] at success
      exact success.1 ▸ Nat.le_refl _
  | entry :: entries, store, updated, rows, remaining, success => by
      unfold replaceManyFold at success
      rcases Option.bind_eq_some.mp success with
        ⟨resolved, resolvedResult, success⟩
      split at success
      next => exact replaceManyFold_nextPage_le success
      next =>
        exact Nat.le_trans (store.nextPage_le_insert entry.1 resolved.1)
          (replaceManyFold_nextPage_le success)

/-- If the completed replacement loop did not advance the allocation
watermark, every insertion in the loop was a no-allocation update and the
complete physical page-identity list is unchanged. -/
theorem replaceManyFold_pageIds_of_noAllocation :
    ∀ {entries : List (PagedBTree.Entry CoreChunkPageState.Chunk)}
      {store updated : PersistentPageTree.Store CoreChunkPageState.Chunk}
      {rows remaining : List Core.Row},
      replaceManyFold entries (store, rows) = some (updated, remaining) →
      updated.nextPage = store.nextPage →
      updated.root.pageIds = store.root.pageIds
  | [], store, updated, rows, remaining, success, noAllocation => by
      simp only [replaceManyFold, Option.some.injEq, Prod.mk.injEq] at success
      exact congrArg (fun tree => tree.root.pageIds) success.1.symm
  | entry :: entries, store, updated, rows, remaining, success,
      noAllocation => by
      unfold replaceManyFold at success
      rcases Option.bind_eq_some.mp success with
        ⟨resolved, resolvedResult, success⟩
      split at success
      next same =>
        exact replaceManyFold_pageIds_of_noAllocation success noAllocation
      next changed =>
        let inserted := store.insert entry.1 resolved.1
        have stepBound : store.nextPage ≤ inserted.nextPage :=
          store.nextPage_le_insert entry.1 resolved.1
        have tailBound : inserted.nextPage ≤ updated.nextPage :=
          replaceManyFold_nextPage_le success
        have stepNoAllocation : inserted.nextPage = store.nextPage := by
          omega
        have tailNoAllocation : updated.nextPage = inserted.nextPage := by
          omega
        exact (replaceManyFold_pageIds_of_noAllocation success
          tailNoAllocation).trans
            (store.insert_pageIds_of_noAllocation entry.1 resolved.1
              stepNoAllocation)

/-- Update all changed chunks without rebuilding table topology.  Stable page
identity selects the exact before/after paths for the rollback journal.  The
final representation equality is retained as the proof field of `TableState`,
so a primary-key change or missing row rejects this path and falls back. -/
def replaceMany? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (replacement : Core.Table) : Option TableDelta := do
  let row ← firstDifference state.table.rows replacement.rows
  let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
    { state.tree with nextPage }
  let updated ← replaceManyFold state.tree.root.erase.toList
    (allocating, replacement.rows)
  if _consumed : updated.2 = [] then
    let updatedTree := updated.1
    if _noAllocation : updatedTree.nextPage = nextPage then
      if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
        let changedPhysical := CorePageCodec.changedPhysicalChunkPagesFast
          state.tree.root updatedTree.root
        let changedIds := changedPhysical.map
          CorePageCodec.PhysicalChunkPage.pageNumber
        let beforePages ← encodeChunkNodesWithIds state.table.schema changedIds
          state.tree.root
        let pages ← changedPhysical.mapM
          (CorePageCodec.encodePhysicalChunkPage replacement.schema)
        let after : CoreChunkPageState.TableState :=
          ⟨replacement, updatedTree, represents⟩
        some ⟨state, after, row.treeKey, pages, some beforePages, []⟩
      else none
    else none
  else none

theorem replace?_freedPageNumbers {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.freedPageNumbers = [] := by
  unfold replace? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with
          ⟨pages, pagesResult, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem replace?_after_nextPage {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.after.tree.nextPage = nextPage := by
  unfold replace? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with
          ⟨pages, pagesResult, success⟩
        injection success with equal
        subst delta
        exact noAllocation
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_freedPageNumbers
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.freedPageNumbers = [] := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some.mp success with
    ⟨updated, updatedResult, success⟩
  dsimp only at success
  split at success
  next =>
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with
          ⟨pages, pagesResult, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_after_nextPage
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.tree.nextPage = nextPage := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some.mp success with
    ⟨updated, updatedResult, success⟩
  dsimp only at success
  split at success
  next =>
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with
          ⟨pages, pagesResult, success⟩
        injection success with equal
        subst delta
        exact noAllocation
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.table = replacement := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        have equal := Option.some.inj success
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  rw [delta.after.represents, replaceMany?_table success]

theorem replaceMany?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next represents =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        exact treePagesAccounted_of_changedPhysical replacement.schema
          state.tree.root _ pages pagesResult
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceMany?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.TreePagesSelected := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        exact treePagesSelected_of_changedPhysical replacement.schema
          state.tree.root _ pages pagesResult
      next => contradiction
    next => contradiction
  next => contradiction

/-- Consume the replacement rows belonging to one old chunk.  Both inputs are
strictly rowid ordered; rows absent from the replacement are deletions, while a
replacement key not present in the old stream rejects the delete-only path. -/
def retainedChunk? : CoreChunkPageState.Chunk → List Core.Row →
    Option (CoreChunkPageState.Chunk × List Core.Row)
  | [], rows => some ([], rows)
  | _ :: olds, [] => retainedChunk? olds []
  | old :: olds, row :: rows =>
      if old.rowid = row.rowid then do
        let retained ← retainedChunk? olds rows
        some (row :: retained.1, retained.2)
      else if old.rowid.value < row.rowid.value then
        retainedChunk? olds (row :: rows)
      else none

/-- Delete many rows while retaining the existing chunk/page topology wherever
possible. Nonempty chunks keep their stable key and page identity; only chunks
made empty enter the proved borrow/merge deletion algorithm. -/
def retainMany? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (replacement : Core.Table) : Option TableDelta := do
  let row ← firstDeleted state.table.rows replacement.rows
  let allocating : PersistentPageTree.Store CoreChunkPageState.Chunk :=
    { state.tree with nextPage }
  let updated ← state.tree.root.erase.toList.foldlM (fun accumulator entry => do
    let resolved ← retainedChunk? entry.2 accumulator.2.1
    if resolved.1 = entry.2 then
      some (accumulator.1, resolved.2, accumulator.2.2)
    else if resolved.1.isEmpty then
      let deleted ← accumulator.1.delete? entry.1
      some (deleted.1, resolved.2, accumulator.2.2 ++ deleted.2)
    else
      some (accumulator.1.insert entry.1 resolved.1, resolved.2,
        accumulator.2.2)) (allocating, replacement.rows, [])
  if _consumed : updated.2.1 = [] then
    let updatedTree := updated.1
    if represents : CoreChunkPageState.Store.rows updatedTree = replacement.rows then
      let changedPhysical := CorePageCodec.changedPhysicalChunkPagesFast
        state.tree.root updatedTree.root
      let changedIds := changedPhysical.map
        CorePageCodec.PhysicalChunkPage.pageNumber
      let beforeIds := changedIds ++ updated.2.2
      let beforePages ← encodeChunkNodesWithIds state.table.schema beforeIds
        state.tree.root
      let pages ← changedPhysical.mapM
        (CorePageCodec.encodePhysicalChunkPage replacement.schema)
      let after : CoreChunkPageState.TableState :=
        ⟨replacement, updatedTree, represents⟩
      some ⟨state, after, row.treeKey, pages, some beforePages,
        updated.2.2⟩
    else none
  else none

theorem retainMany?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.after.table = replacement := by
  unfold retainMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
      rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
      have equal := Option.some.inj success
      subst delta
      rfl
    next => contradiction
  next => contradiction

theorem retainMany?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  rw [delta.after.represents, retainMany?_table success]

theorem retainMany?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold retainMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next represents =>
      rcases Option.bind_eq_some.mp success with
        ⟨beforePages, beforeResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
      have equal := Option.some.inj success
      subst delta
      exact treePagesAccounted_of_changedPhysical replacement.schema
        state.tree.root _ pages pagesResult
    next => contradiction
  next => contradiction

theorem retainMany?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.TreePagesSelected := by
  unfold retainMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, rowResult, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with
        ⟨beforePages, beforeResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
      have equal := Option.some.inj success
      subst delta
      exact treePagesSelected_of_changedPhysical replacement.schema
        state.tree.root _ pages pagesResult
    next => contradiction
  next => contradiction

def replaceBetween? (state : CoreChunkPageState.TableState) (nextPage : Nat)
    (replacement : Core.Table) : Option TableDelta :=
  if sameData : CoreChunkPageState.TableState.DataEquiv
      state.table replacement then
    let after := state.retargetData replacement sameData
    some ⟨state, after, 0, [], some [], []⟩
  else if replacement.rows.length = state.table.rows.length + 1 then do
    let row ← firstInserted state.table.rows replacement.rows
    match insert? state nextPage row replacement with
    | some delta => some delta
    | none => splitInsert? state nextPage row replacement
  else if state.table.rows.length = replacement.rows.length + 1 then do
    let row ← firstDeleted state.table.rows replacement.rows
    match delete? state nextPage row replacement with
    | some delta => some delta
    | none => mergeDelete? state nextPage row replacement
  else if replacement.rows.length < state.table.rows.length then
    retainMany? state nextPage replacement
  else do
      let row ← firstDifference state.table.rows replacement.rows
      match replace? state nextPage row replacement with
      | some delta => some delta
      | none => replaceMany? state nextPage replacement

/-- Secondary-index metadata does not alter table-page topology.  The delta
builder exposes that case explicitly, including empty tables where there is no
row available to use as a synthetic mutation witness. -/
theorem replaceBetween?_sameData (state : CoreChunkPageState.TableState)
    (nextPage : Nat) (replacement : Core.Table)
    (sameData : CoreChunkPageState.TableState.DataEquiv
      state.table replacement) :
    ∃ delta, replaceBetween? state nextPage replacement = some delta ∧
      delta.before = state ∧ delta.after.table = replacement ∧
      delta.after.tree = state.tree ∧ delta.pages = [] ∧
      delta.beforePages? = some [] ∧ delta.freedPageNumbers = [] := by
  let after := state.retargetData replacement sameData
  let delta : TableDelta := ⟨state, after, 0, [], some [], []⟩
  refine ⟨delta, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [replaceBetween?, sameData, delta, after]

theorem replace?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  unfold replace? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        dsimp only at success
        split at success
        next =>
          split at success
          next represents =>
            cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                entry.1
                ({ state.tree with nextPage }.insert entry.1
                  (replaceRow row entry.2)).root with
            | none => simp [pageResult] at success
            | some pages =>
                simp only [pageResult, Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at success
                subst delta
                exact represents
          next => contradiction
        next => contradiction
      next => contradiction

theorem replace?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.after.table = replacement := by
  unfold replace? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        dsimp only at success
        split at success
        next =>
          split at success
          next =>
            cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                entry.1 ({ state.tree with nextPage }.insert entry.1
                  (replaceRow row entry.2)).root with
            | none => simp [pageResult] at success
            | some pages =>
                simp only [pageResult, Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at success
                subst delta
                rfl
          next => contradiction
        next => contradiction
      next => contradiction

theorem replace?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold replace? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        dsimp only at success
        split at success
        next noAllocation =>
          split at success
          next represents =>
            cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                entry.1 ({ state.tree with nextPage }.insert entry.1
                  (replaceRow row entry.2)).root with
            | none => simp [pageResult] at success
            | some pages =>
                simp only [pageResult, Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at success
                subst delta
                unfold TableDelta.TreePagesAccounted
                dsimp only
                have agrees :=
                  state.tree.root.insert_pathAgrees_of_noAllocation nextPage
                    entry.1 (replaceRow row entry.2) (by
                      simpa [PersistentPageTree.Store.insert] using
                        noAllocation)
                have accounted := treePagesAccounted_of_pathAgrees
                  replacement.schema entry.1 state.tree.root
                    (state.tree.root.insert nextPage entry.1
                      (replaceRow row entry.2)).1 pages agrees (by
                        simpa [PersistentPageTree.Store.insert] using
                          pageResult)
                simpa [PersistentPageTree.Store.insert] using accounted
          next => contradiction
        next => contradiction
      next => contradiction

theorem replace?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold replace? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        dsimp only at success
        split at success
        next =>
          split at success
          next =>
            cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                entry.1 ({ state.tree with nextPage }.insert entry.1
                  (replaceRow row entry.2)).root with
            | none => simp [pageResult] at success
            | some pages =>
                simp only [pageResult, Option.bind_eq_bind, Option.bind,
                  Option.some.injEq] at success
                subst delta
                unfold TableDelta.TreePagesSelected
                dsimp only
                simpa [PersistentPageTree.Store.insert] using
                  treePagesSelected_of_path replacement.schema entry.1
                    (state.tree.root.insert nextPage entry.1
                      (replaceRow row entry.2)).1 pages (by
                        simpa [PersistentPageTree.Store.insert] using
                          pageResult)
          next => contradiction
        next => contradiction
      next => contradiction

theorem insert?_correct {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows ∧
      delta.after.table = replacement := by
  unfold insert? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        split at success
        next =>
          split at success
          next =>
            split at success
            next represents =>
              cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                  entry.1 ({ state.tree with nextPage }.insert entry.1
                    (Core.orderedUpsert row entry.2)).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  exact ⟨represents, rfl⟩
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem insert?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows :=
  (insert?_correct success).1

theorem insert?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.after.table = replacement :=
  (insert?_correct success).2

theorem insert?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold insert? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        split at success
        next =>
          split at success
          next noAllocation =>
            split at success
            next represents =>
              cases pageResult : CorePageCodec.encodeChunkPath
                  replacement.schema entry.1
                  ({ state.tree with nextPage }.insert entry.1
                    (Core.orderedUpsert row entry.2)).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.TreePagesAccounted
                  dsimp only
                  have agrees :=
                    state.tree.root.insert_pathAgrees_of_noAllocation nextPage
                      entry.1 (Core.orderedUpsert row entry.2) (by
                        simpa [PersistentPageTree.Store.insert] using
                          noAllocation)
                  have accounted := treePagesAccounted_of_pathAgrees
                    replacement.schema entry.1 state.tree.root
                      (state.tree.root.insert nextPage entry.1
                        (Core.orderedUpsert row entry.2)).1 pages agrees (by
                          simpa [PersistentPageTree.Store.insert] using
                            pageResult)
                  simpa [PersistentPageTree.Store.insert] using accounted
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem insert?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold insert? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        split at success
        next =>
          split at success
          next =>
            split at success
            next =>
              cases pageResult : CorePageCodec.encodeChunkPath
                  replacement.schema entry.1
                  ({ state.tree with nextPage }.insert entry.1
                    (Core.orderedUpsert row entry.2)).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.TreePagesSelected
                  dsimp only
                  simpa [PersistentPageTree.Store.insert] using
                    treePagesSelected_of_path replacement.schema entry.1
                      (state.tree.root.insert nextPage entry.1
                        (Core.orderedUpsert row entry.2)).1 pages (by
                          simpa [PersistentPageTree.Store.insert] using
                            pageResult)
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem delete?_correct {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows ∧
      delta.after.table = replacement := by
  unfold delete? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        dsimp only at success
        split at success
        next =>
          split at success
          next =>
            split at success
            next represents =>
              cases pageResult : CorePageCodec.encodeChunkPath replacement.schema
                  entry.1 ({ state.tree with nextPage }.insert entry.1
                    (entry.2.filter (fun old => old.rowid != row.rowid))).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  exact ⟨represents, rfl⟩
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem delete?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows :=
  (delete?_correct success).1

theorem delete?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.after.table = replacement :=
  (delete?_correct success).2

theorem delete?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold delete? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        dsimp only at success
        split at success
        next =>
          split at success
          next noAllocation =>
            split at success
            next represents =>
              cases pageResult : CorePageCodec.encodeChunkPath
                  replacement.schema entry.1
                  ({ state.tree with nextPage }.insert entry.1
                    (entry.2.filter
                      (fun old => old.rowid != row.rowid))).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.TreePagesAccounted
                  dsimp only
                  let updatedChunk := entry.2.filter
                    (fun old => old.rowid != row.rowid)
                  have agrees :=
                    state.tree.root.insert_pathAgrees_of_noAllocation nextPage
                      entry.1 updatedChunk (by
                        simpa [updatedChunk, PersistentPageTree.Store.insert]
                          using noAllocation)
                  have accounted := treePagesAccounted_of_pathAgrees
                    replacement.schema entry.1 state.tree.root
                      (state.tree.root.insert nextPage entry.1
                        updatedChunk).1 pages agrees (by
                          simpa [updatedChunk,
                            PersistentPageTree.Store.insert] using pageResult)
                  simpa [updatedChunk, PersistentPageTree.Store.insert] using
                    accounted
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem delete?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold delete? at success
  cases entryResult : findChunkFor? row.treeKey state.tree.root with
  | none => simp [entryResult] at success
  | some entry =>
      simp only [entryResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next =>
        dsimp only at success
        split at success
        next =>
          split at success
          next =>
            split at success
            next =>
              cases pageResult : CorePageCodec.encodeChunkPath
                  replacement.schema entry.1
                  ({ state.tree with nextPage }.insert entry.1
                    (entry.2.filter
                      (fun old => old.rowid != row.rowid))).root with
              | none => simp [pageResult] at success
              | some pages =>
                  simp only [pageResult, Option.bind_eq_bind, Option.bind,
                    Option.some.injEq] at success
                  subst delta
                  unfold TableDelta.TreePagesSelected
                  dsimp only
                  let updatedChunk := entry.2.filter
                    (fun old => old.rowid != row.rowid)
                  simpa [updatedChunk, PersistentPageTree.Store.insert] using
                    treePagesSelected_of_path replacement.schema entry.1
                      (state.tree.root.insert nextPage entry.1
                        updatedChunk).1 pages (by
                          simpa [updatedChunk,
                            PersistentPageTree.Store.insert] using pageResult)
            next => contradiction
          next => contradiction
        next => contradiction
      next => contradiction

theorem splitInsert?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.after.table = replacement := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next represents =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with
          ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem splitInsert?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  rw [delta.after.represents, splitInsert?_table success]

theorem splitInsert?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next represents =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        exact treePagesAccounted_of_changedPhysical replacement.schema
          state.tree.root _ pages pagesResult
      next => contradiction
    next => contradiction
  next => contradiction

theorem splitInsert?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        exact treePagesSelected_of_changedPhysical replacement.schema
          state.tree.root _ pages pagesResult
      next => contradiction
    next => contradiction
  next => contradiction

theorem mergeDelete?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.after.table = replacement := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next represents =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

theorem mergeDelete?_represents {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    CoreChunkPageState.Store.rows delta.after.tree = replacement.rows := by
  rw [delta.after.represents, mergeDelete?_table success]

theorem mergeDelete?_treePagesAccounted
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.TreePagesAccounted := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next represents =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        exact treePagesAccounted_of_changedPhysical replacement.schema
          state.tree.root _ pages pagesResult
      next => contradiction
    next => contradiction
  next => contradiction

theorem mergeDelete?_treePagesSelected
    {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.TreePagesSelected := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, entryResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨deleted, deletedResult, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with
          ⟨beforePages, beforeResult, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, pagesResult, success⟩
        have equal := Option.some.inj success
        subst delta
        exact treePagesSelected_of_changedPhysical replacement.schema
          state.tree.root _ pages pagesResult
      next => contradiction
    next => contradiction
  next => contradiction

theorem replaceBetween?_table {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceBetween? state nextPage replacement = some delta) :
    delta.after.table = replacement := by
  unfold replaceBetween? at success
  split at success
  next =>
    injection success with equal
    subst delta
    rfl
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
              exact splitInsert?_table success
          | some candidate =>
              rw [insertionResult] at success
              simp only [Option.some.injEq] at success
              subst candidate
              exact insert?_table insertionResult
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
                exact mergeDelete?_table success
            | some candidate =>
                rw [deletionResult] at success
                simp only [Option.some.injEq] at success
                subst candidate
                exact delete?_table deletionResult
      next =>
        split at success
        next => exact retainMany?_table success
        next =>
          cases difference : firstDifference state.table.rows replacement.rows with
          | none => simp [difference] at success
          | some row =>
              simp only [difference, Option.bind_eq_bind, Option.bind] at success
              cases replacementResult : replace? state nextPage row replacement with
              | some candidate =>
                  rw [replacementResult] at success
                  simp only [Option.some.injEq] at success
                  subst candidate
                  exact replace?_table replacementResult
              | none =>
                  rw [replacementResult] at success
                  exact replaceMany?_table success

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
            rcases Option.bind_eq_some.mp success with
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
            rcases Option.bind_eq_some.mp success with
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
            rcases Option.bind_eq_some.mp success with
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

def indexEntriesText (entries : List CoreDecode.IndexEntry) : Bool :=
  entries.all fun entry => CoreFile.valueIsText entry.value

def sortIndexEntries (entries : List CoreDecode.IndexEntry) :
    List CoreDecode.IndexEntry :=
  if indexEntriesInteger entries then
    entries.mergeSort integerIndexEntryLe
  else if indexEntriesText entries then
    entries.mergeSort textIndexEntryLe
  else entries.foldl (fun sorted entry => insertIndexEntry entry sorted) []

theorem integerIndexRowLe_entry (index : Core.Index)
    (left right : Core.Row) :
    CoreFile.integerIndexRowLe index left right =
      integerIndexEntryLe (indexEntryOfRow index left)
        (indexEntryOfRow index right) := by
  rfl

theorem textIndexRowLe_entry (index : Core.Index)
    (left right : Core.Row) :
    CoreFile.textIndexRowLe index left right =
      textIndexEntryLe (indexEntryOfRow index left)
        (indexEntryOfRow index right) := by
  rfl

theorem indexEntriesInteger_map (index : Core.Index) (rows : List Core.Row) :
    indexEntriesInteger (rows.map (indexEntryOfRow index)) =
      rows.all (fun row => CoreFile.valueIsInteger (row.value index.column)) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      unfold indexEntriesInteger at induction ⊢
      simp only [List.map_cons, List.all_cons, indexEntryOfRow, induction]

theorem indexEntriesText_map (index : Core.Index) (rows : List Core.Row) :
    indexEntriesText (rows.map (indexEntryOfRow index)) =
      rows.all (fun row => CoreFile.valueIsText (row.value index.column)) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      unfold indexEntriesText at induction ⊢
      simp only [List.map_cons, List.all_cons, indexEntryOfRow, induction]

theorem map_insertIndexRow (index : Core.Index) (row : Core.Row) :
    ∀ rows,
    (CoreFile.insertIndexRow index row rows).map (indexEntryOfRow index) =
      insertIndexEntry (indexEntryOfRow index row)
        (rows.map (indexEntryOfRow index))
  | [] => rfl
  | candidate :: rows => by
      simp only [CoreFile.insertIndexRow, insertIndexEntry, List.map_cons]
      have comparison : indexEntryLess (indexEntryOfRow index row)
          (indexEntryOfRow index candidate) =
          CoreFile.indexRowLess index row candidate := rfl
      rw [comparison]
      split
      · rfl
      · simp only [List.map_cons, map_insertIndexRow index row rows]

theorem map_foldInsertIndexRow (index : Core.Index) :
    ∀ (rows accumulator : List Core.Row),
    (rows.foldl (fun sorted row => CoreFile.insertIndexRow index row sorted)
        accumulator).map (indexEntryOfRow index) =
      (rows.map (indexEntryOfRow index)).foldl
        (fun sorted entry => insertIndexEntry entry sorted)
        (accumulator.map (indexEntryOfRow index))
  | [], _ => rfl
  | row :: rows, accumulator => by
      simp only [List.foldl_cons, List.map_cons]
      rw [map_foldInsertIndexRow index rows
        (CoreFile.insertIndexRow index row accumulator)]
      rw [map_insertIndexRow]

theorem expectedIndexEntries_eq_sortSource (table : Core.Table)
    (index : Core.Index) :
    CoreDecode.expectedIndexEntries table index =
      sortIndexEntries (table.rows.map (indexEntryOfRow index)) := by
  unfold CoreDecode.expectedIndexEntries CoreFile.sortedIndexRows
    sortIndexEntries
  by_cases integers : CoreFile.indexValuesInteger table index = true
  · rw [if_pos integers]
    have sourceIntegers :
        indexEntriesInteger (table.rows.map (indexEntryOfRow index)) = true := by
      rw [indexEntriesInteger_map]
      exact integers
    rw [if_pos sourceIntegers]
    exact List.map_mergeSort fun left _ right _ =>
      integerIndexRowLe_entry index left right
  · rw [if_neg integers]
    have sourceNotIntegers :
        indexEntriesInteger (table.rows.map (indexEntryOfRow index)) ≠ true := by
      rw [indexEntriesInteger_map]
      exact integers
    rw [if_neg sourceNotIntegers]
    by_cases texts : CoreFile.indexValuesText table index = true
    · rw [if_pos texts]
      have sourceTexts :
          indexEntriesText (table.rows.map (indexEntryOfRow index)) = true := by
        rw [indexEntriesText_map]
        exact texts
      rw [if_pos sourceTexts]
      exact List.map_mergeSort fun left _ right _ =>
        textIndexRowLe_entry index left right
    · rw [if_neg texts]
      have sourceNotTexts :
          indexEntriesText (table.rows.map (indexEntryOfRow index)) ≠ true := by
        rw [indexEntriesText_map]
        exact texts
      rw [if_neg sourceNotTexts]
      simpa using map_foldInsertIndexRow index table.rows []

/-- Primary-order index inputs. Equality is linear to decide; unlike
`indexImage`, it does not sort every index twice on each table mutation. -/
def indexSourceImage (table : Core.Table) :
    List (Core.Index × List CoreDecode.IndexEntry) :=
  table.indexes.map fun index =>
    (index, table.rows.map (indexEntryOfRow index))

def sortIndexSourceImage
    (source : List (Core.Index × List CoreDecode.IndexEntry)) :
    List (Core.Index × List CoreDecode.IndexEntry) :=
  source.map fun pair => (pair.1, sortIndexEntries pair.2)

theorem indexImage_eq_sortIndexSourceImage (table : Core.Table) :
    indexImage table = sortIndexSourceImage (indexSourceImage table) := by
  unfold indexImage indexSourceImage sortIndexSourceImage
  rw [List.map_map]
  apply List.map_congr_left
  intro index _
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  exact expectedIndexEntries_eq_sortSource table index

def TableDelta.tablePagesSufficient (delta : TableDelta) : Bool :=
  delta.before.table.schema == delta.after.table.schema &&
    delta.before.table.indexes == delta.after.table.indexes &&
    (delta.before.table.indexes.isEmpty ||
      (delta.before.table.rows.length == delta.after.table.rows.length &&
        indexSourceImage delta.before.table == indexSourceImage delta.after.table))

/-- The linear source-image check is strong enough to leave physical index
pages untouched: deterministic logical sorting maps equal sources to the exact
same promoted-key index image. -/
theorem TableDelta.tablePagesSufficient_indexImage (delta : TableDelta)
    (sufficient : delta.tablePagesSufficient = true) :
    indexImage delta.before.table = indexImage delta.after.table := by
  by_cases empty : delta.before.table.indexes = []
  · simp [TableDelta.tablePagesSufficient, empty] at sufficient
    unfold indexImage
    rw [sufficient.2]
    simp [empty]
  · simp [TableDelta.tablePagesSufficient, empty] at sufficient
    rw [indexImage_eq_sortIndexSourceImage,
      indexImage_eq_sortIndexSourceImage, sufficient.2.2]

theorem TableDelta.tablePagesSufficient_rowsLength_of_indexed
    (delta : TableDelta) (sufficient : delta.tablePagesSufficient = true)
    (indexed : delta.before.table.indexes ≠ []) :
    delta.after.table.rows.length = delta.before.table.rows.length := by
  simp [TableDelta.tablePagesSufficient, indexed] at sufficient
  exact sufficient.2.1.symm

/-- The part of table identity stored in `sqlite_master`.  Rows and proof-tree
topology are deliberately absent: a data mutation changes both without
changing the catalog declaration. -/
def TableMetadataEq (before after : Core.Table) : Prop :=
  before.schema = after.schema ∧ before.indexes = after.indexes

inductive TablesMetadataAligned : List Core.Table → List Core.Table → Prop where
  | nil : TablesMetadataAligned [] []
  | cons {before after : Core.Table} {befores afters : List Core.Table}
      (head : TableMetadataEq before after)
      (tail : TablesMetadataAligned befores afters) :
      TablesMetadataAligned (before :: befores) (after :: afters)

theorem TableDelta.tablePagesSufficient_metadata (delta : TableDelta)
    (sufficient : delta.tablePagesSufficient = true) :
    TableMetadataEq delta.before.table delta.after.table := by
  simp only [TableDelta.tablePagesSufficient, Bool.and_eq_true,
    beq_iff_eq] at sufficient
  exact sufficient.1

private theorem replace?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold replace? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

private theorem insert?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold insert? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    split at success
    next =>
      dsimp only at success
      split at success
      next =>
        split at success
        next =>
          rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
          injection success with equal
          subst delta
          rfl
        next => contradiction
      next => contradiction
    next => contradiction
  next => contradiction

private theorem splitInsert?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : splitInsert? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold splitInsert? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨leftKey, _, success⟩
      rcases Option.bind_eq_some.mp success with ⟨rightKey, _, success⟩
      rcases Option.bind_eq_some.mp success with ⟨deleted, _, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

private theorem delete?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold delete? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        split at success
        next =>
          rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
          injection success with equal
          subst delta
          rfl
        next => contradiction
      next => contradiction
    next => contradiction
  next => contradiction

private theorem mergeDelete?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.before = state := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨deleted, _, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

private theorem retainMany?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.before = state := by
  unfold retainMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
      rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
      injection success with equal
      subst delta
      rfl
    next => contradiction
  next => contradiction

private theorem replaceMany?_before {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.before = state := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some.mp success with ⟨updated, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        rfl
      next => contradiction
    next => contradiction
  next => contradiction

private theorem replaceManyFold_rootId :
    ∀ (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk))
      (store : PersistentPageTree.Store CoreChunkPageState.Chunk)
      (rows : List Core.Row)
      (updated : PersistentPageTree.Store CoreChunkPageState.Chunk ×
        List Core.Row),
      replaceManyFold entries (store, rows) = some updated →
      updated.1.root.rootId = store.root.rootId
  | [], store, rows, updated, success => by
      simp only [replaceManyFold, Option.some.injEq] at success
      subst updated
      rfl
  | entry :: entries, store, rows, updated, success => by
      unfold replaceManyFold at success
      rcases Option.bind_eq_some.mp success with
        ⟨resolved, resolvedResult, success⟩
      split at success
      next => exact replaceManyFold_rootId entries store resolved.2 updated success
      next =>
        have tail := replaceManyFold_rootId entries
          (store.insert entry.1 resolved.1) resolved.2 updated success
        exact tail.trans (store.insert_rootId entry.1 resolved.1)

private theorem retainManyFold_rootId :
    ∀ (entries : List (PagedBTree.Entry CoreChunkPageState.Chunk))
      (store : PersistentPageTree.Store CoreChunkPageState.Chunk)
      (rows : List Core.Row) (freed : List Nat)
      (updated : PersistentPageTree.Store CoreChunkPageState.Chunk ×
        List Core.Row × List Nat),
      entries.foldlM (fun accumulator entry => do
        let resolved ← retainedChunk? entry.2 accumulator.2.1
        if resolved.1 = entry.2 then
          some (accumulator.1, resolved.2, accumulator.2.2)
        else if resolved.1.isEmpty then
          let deleted ← accumulator.1.delete? entry.1
          some (deleted.1, resolved.2, accumulator.2.2 ++ deleted.2)
        else
          some (accumulator.1.insert entry.1 resolved.1, resolved.2,
            accumulator.2.2)) (store, rows, freed) = some updated →
      updated.1.root.rootId = store.root.rootId
  | [], store, rows, freed, updated, success => by
      simp only [List.foldlM_nil, pure, Option.pure_def,
        Option.some.injEq] at success
      subst updated
      rfl
  | entry :: entries, store, rows, freed, updated, success => by
      simp only [List.foldlM_cons] at success
      rcases Option.bind_eq_some.mp success with ⟨next, stepResult, success⟩
      have stepRoot : next.1.root.rootId = store.root.rootId := by
        rcases Option.bind_eq_some.mp stepResult with
          ⟨resolved, resolvedResult, stepResult⟩
        split at stepResult
        next =>
          injection stepResult with equal
          subst next
          rfl
        next =>
          split at stepResult
          next =>
            rcases Option.bind_eq_some.mp stepResult with
              ⟨deleted, deletedResult, stepResult⟩
            injection stepResult with equal
            subst next
            exact store.delete?_rootId deletedResult
          next =>
            injection stepResult with equal
            subst next
            exact store.insert_rootId entry.1 resolved.1
      have tail := retainManyFold_rootId entries next.1 next.2.1 next.2.2
        updated success
      exact tail.trans stepRoot

private theorem replace?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold replace? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        exact PersistentPageTree.Store.insert_rootId
          { state.tree with nextPage } entry.1 (replaceRow row entry.2)
      next => contradiction
    next => contradiction
  next => contradiction

private theorem replace?_pageIds {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : replace? state nextPage row replacement = some delta) :
    delta.after.tree.root.pageIds = state.tree.root.pageIds := by
  unfold replace? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        exact PersistentPageTree.Store.insert_pageIds_of_noAllocation
          { state.tree with nextPage } entry.1 (replaceRow row entry.2)
          noAllocation
      next => contradiction
    next => contradiction
  next => contradiction

private theorem insert?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : insert? state nextPage row replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold insert? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    split at success
    next =>
      dsimp only at success
      split at success
      next =>
        split at success
        next =>
          rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
          injection success with equal
          subst delta
          exact PersistentPageTree.Store.insert_rootId
            { state.tree with nextPage } entry.1
              (Core.orderedUpsert row entry.2)
        next => contradiction
      next => contradiction
    next => contradiction
  next => contradiction

private theorem delete?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : delete? state nextPage row replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold delete? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        split at success
        next =>
          rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
          injection success with equal
          subst delta
          exact PersistentPageTree.Store.insert_rootId
            { state.tree with nextPage } entry.1
              (entry.2.filter fun old => old.rowid != row.rowid)
        next => contradiction
      next => contradiction
    next => contradiction
  next => contradiction

private theorem mergeDelete?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {row : Core.Row} {replacement : Core.Table}
    {delta : TableDelta}
    (success : mergeDelete? state nextPage row replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold mergeDelete? at success
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with
        ⟨deleted, deletedResult, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        have root := PersistentPageTree.Store.delete?_rootId deletedResult
        simpa using root
      next => contradiction
    next => contradiction
  next => contradiction

private theorem replaceMany?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some.mp success with
    ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        injection success with equal
        subst delta
        have root := replaceManyFold_rootId state.tree.root.erase.toList
          { state.tree with nextPage } replacement.rows updated updatedResult
        simpa using root
      next => contradiction
    next => contradiction
  next => contradiction

private theorem replaceMany?_pageIds
    {state : CoreChunkPageState.TableState} {nextPage : Nat}
    {replacement : Core.Table} {delta : TableDelta}
    (success : replaceMany? state nextPage replacement = some delta) :
    delta.after.tree.root.pageIds = state.tree.root.pageIds := by
  unfold replaceMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some.mp success with
    ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next noAllocation =>
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
        have pageIds : updated.1.root.pageIds = state.tree.root.pageIds := by
          have preserved := replaceManyFold_pageIds_of_noAllocation
            updatedResult (by simpa using noAllocation)
          simpa using preserved
        injection success with equal
        subst delta
        exact pageIds
      next => contradiction
    next => contradiction
  next => contradiction

private theorem retainMany?_rootId {state : CoreChunkPageState.TableState}
    {nextPage : Nat} {replacement : Core.Table} {delta : TableDelta}
    (success : retainMany? state nextPage replacement = some delta) :
    delta.after.tree.root.rootId = state.tree.root.rootId := by
  unfold retainMany? at success
  rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
  rcases Option.bind_eq_some.mp success with
    ⟨updated, updatedResult, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
      rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
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
  rcases Option.bind_eq_some.mp success with ⟨entry, _, success⟩
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      rcases Option.bind_eq_some.mp success with
        ⟨leftKey, leftResult, success⟩
      rcases Option.bind_eq_some.mp success with
        ⟨rightKey, rightResult, success⟩
      rcases Option.bind_eq_some.mp success with
        ⟨deleted, deletedResult, success⟩
      split at success
      next =>
        rcases Option.bind_eq_some.mp success with ⟨beforePages, _, success⟩
        rcases Option.bind_eq_some.mp success with ⟨pages, _, success⟩
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
      rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
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
        rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
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
          rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
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
      rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
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
        rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
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
          rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
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
          rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
          cases replacementResult : replace? state nextPage row replacement with
          | some candidate =>
              rw [replacementResult] at success
              injection success with equal
              subst candidate
              exact replace?_pageIds replacementResult
          | none =>
              rw [replacementResult] at success
              exact replaceMany?_pageIds success

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
          rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
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
    rw [sameData.1, sameData.2, sameIndexes]
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
          rcases Option.bind_eq_some.mp success with ⟨row, _, success⟩
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
  simp only [metadata.1, root]

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
            rcases Option.bind_eq_some.mp success with
              ⟨tail, tailResult, success⟩
            injection success with equal
            subst aligned
            refine .cons ⟨?_, ?_⟩
              (alignTables?_metadata_none tailResult noChange)
            · exact Core.Table.Equiv.schema_eq same
            · exact Core.Table.Equiv.indexes_eq same
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
            rcases Option.bind_eq_some.mp success with
              ⟨tail, tailResult, success⟩
            injection success with equal
            subst aligned
            refine .cons ⟨Core.Table.Equiv.schema_eq same,
              Core.Table.Equiv.indexes_eq same⟩
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

private theorem chunkTableCatalogEntry_retarget
    (state : CoreChunkPageState.TableState) (table : Core.Table)
    (equivalent : state.table.Equiv table) :
    CorePageCodec.chunkTableCatalogEntry (state.retarget table equivalent) =
      CorePageCodec.chunkTableCatalogEntry state := by
  unfold CorePageCodec.chunkTableCatalogEntry
    CoreChunkPageState.TableState.rootPage
  simp only [CoreChunkPageState.TableState.retarget_table,
    CoreChunkPageState.TableState.retarget_tree, equivalent.schema_eq]

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
            rcases Option.bind_eq_some.mp success with
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
            rcases Option.bind_eq_some.mp success with
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
          rcases Option.bind_eq_some.mp success with
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
          rcases Option.bind_eq_some.mp success with
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
          rcases Option.bind_eq_some.mp success with
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
                  sameLength metadata.2 changed headResult
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
          rcases Option.bind_eq_some.mp success with
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
          rcases Option.bind_eq_some.mp success with
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

theorem alignTables?_tablePageIds_changed_indexed :
    ∀ {nextPage : Nat} {states : List CoreChunkPageState.TableState}
      {target : List Core.Table} {aligned : AlignedTables target}
      {delta : TableDelta},
      alignTables? nextPage states target = some aligned →
      aligned.delta = some delta →
      delta.tablePagesSufficient = true →
      delta.before.table.indexes ≠ [] →
      CoreChunkPageState.tablePageIds aligned.tables =
        CoreChunkPageState.tablePageIds states
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
          rcases Option.bind_eq_some.mp success with
            ⟨tail, tailResult, success⟩
          injection success with equal
          subst aligned
          unfold CoreChunkPageState.tablePageIds
          simp only [List.flatMap_cons,
            CoreChunkPageState.TableState.retarget_tree]
          exact congrArg (old.tree.root.pageIds ++ ·)
            (alignTables?_tablePageIds_changed_indexed tailResult selected
              sufficient indexed)
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
                have tailNone : tail.delta = none := by
                  cases tailDelta : tail.delta with
                  | none => rfl
                  | some value => simp [tailDelta] at *
                have sameLength :=
                  delta.tablePagesSufficient_rowsLength_of_indexed sufficient
                    indexed
                rw [replaceBetween?_before headResult,
                  replaceBetween?_table headResult] at sameLength
                have headPages := replaceBetween?_pageIds_of_length_eq
                  (state := old) (replacement := replacement)
                  (delta := delta) sameLength headResult
                have tailPages := alignTables?_tablePageIds_none tailResult
                  tailNone
                simp only [CoreChunkPageState.tablePageIds] at tailPages
                unfold CoreChunkPageState.tablePageIds
                simp only [List.flatMap_cons,
                  CoreChunkPageState.TableState.pageIds]
                rw [headPages, tailPages]
              next => contradiction

def addFreePages (existing added : List Nat) : List Nat :=
  added.foldl (fun pages page =>
    if pages.contains page then pages else pages ++ [page]) existing

/-- Build the table-page delta before deciding whether secondary index pages
can remain untouched.  Changed-index writers consume this candidate and attach
their own proved physical index delta; the ordinary path below additionally
requires an identical index image. -/
def updateStateCandidate? (state : CoreChunkPageState.State)
    (database : Core.Database) :
    Option StateDelta := do
  let aligned ← alignTables? state.nextPage state.tables database.tables
  let table ← aligned.delta
  if _identities : table.IdentityWellFormed then
    let after : CoreChunkPageState.State := {
      database
      tables := aligned.tables
      tables_eq := aligned.aligned
      nextPage := aligned.nextPage
      freePages := addFreePages state.freePages table.freedPageNumbers }
    some ⟨state, after, table⟩
  else none

theorem updateStateCandidate?_identityWellFormed
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.table.IdentityWellFormed := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next identities =>
    injection updated with equal
    subst delta
    exact identities
  next => contradiction

theorem updateStateCandidate?_endpoints
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.before = state ∧ delta.after.database = database := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next identities =>
    injection updated with equal
    subst delta
    exact ⟨rfl, rfl⟩
  next => contradiction

theorem updateStateCandidate?_freePages
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.after.freePages =
      addFreePages state.freePages delta.table.freedPageNumbers := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst delta
    rfl
  next => contradiction

/-- Expose the exact recursive table alignment retained inside a successful
state delta.  This proof-only witness lets physical representation proofs
transport unchanged tables in order and replace exactly the selected table. -/
theorem updateStateCandidate?_alignment
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    ∃ aligned : AlignedTables database.tables,
      alignTables? state.nextPage state.tables database.tables = some aligned ∧
      aligned.tables = delta.after.tables ∧
      aligned.delta = some delta.table := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst delta
    exact ⟨aligned, alignedResult, rfl, tableResult⟩
  next => contradiction

theorem updateStateCandidate?_treePagesAccounted
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.table.TreePagesAccounted := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst delta
    exact alignTables?_delta_treePagesAccounted alignedResult tableResult
  next => contradiction

theorem updateStateCandidate?_treePagesSelected
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateStateCandidate? state database = some delta) :
    delta.table.TreePagesSelected := by
  unfold updateStateCandidate? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨aligned, alignedResult, updated⟩
  rcases Option.bind_eq_some.mp updated with
    ⟨table, tableResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst delta
    exact alignTables?_delta_treePagesSelected alignedResult tableResult
  next => contradiction

def updateState? (state : CoreChunkPageState.State) (database : Core.Database) :
    Option StateDelta := do
  let delta ← updateStateCandidate? state database
  if _sufficient : delta.table.tablePagesSufficient then some delta else none

theorem updateState?_identityWellFormed {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.IdentityWellFormed := by
  unfold updateState? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_identityWellFormed candidateResult
  next => contradiction

theorem updateState?_tablePagesSufficient {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.tablePagesSufficient = true := by
  unfold updateState? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next sufficient =>
    injection updated with equal
    subst candidate
    exact sufficient
  next => contradiction

theorem updateState?_endpoints {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.before = state ∧ delta.after.database = database := by
  unfold updateState? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_endpoints candidateResult
  next => contradiction

theorem updateState?_freePages
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.after.freePages =
      addFreePages state.freePages delta.table.freedPageNumbers := by
  unfold updateState? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_freePages candidateResult
  next => contradiction

theorem updateState?_alignment {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    ∃ aligned : AlignedTables database.tables,
      alignTables? state.nextPage state.tables database.tables = some aligned ∧
      aligned.tables = delta.after.tables ∧
      aligned.delta = some delta.table := by
  unfold updateState? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_alignment candidateResult
  next => contradiction

/-- Ordinary localized table writes preserve every catalog-level table/index
declaration.  This is derived from the same successful alignment and
`tablePagesSufficient` check consumed by the live writer. -/
theorem updateState?_metadataAligned
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    TablesMetadataAligned (state.tables.map fun table => table.table)
      database.tables := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, _, selected⟩
  exact alignTables?_metadata_changed alignment selected
    (updateState?_tablePagesSufficient updated)

/-- The ordinary localized fast path leaves every table entry in page-zero's
catalog byte-for-byte unchanged, including root page numbers. -/
theorem updateState?_catalogEntries
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (allocation : state.AllocationWellFormed)
    (updated : updateState? state database = some delta) :
    delta.after.tables.map CorePageCodec.chunkTableCatalogEntry =
      state.tables.map CorePageCodec.chunkTableCatalogEntry := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, alignedTables, selected⟩
  rw [← alignedTables]
  apply alignTables?_catalogEntries_changed _ alignment selected
    (updateState?_tablePagesSufficient updated)
  intro table member
  apply allocation.2.1 table.tree.root.rootId
  unfold CoreChunkPageState.State.activePageIds
    CoreChunkPageState.tablePageIds
  exact List.mem_flatMap.mpr
    ⟨table, member, PersistentPageTree.Node.rootId_mem_pageIds table.tree.root⟩

theorem updateState?_treePagesAccounted
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.TreePagesAccounted := by
  unfold updateState? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_treePagesAccounted candidateResult
  next => contradiction

theorem updateState?_treePagesSelected
    {state : CoreChunkPageState.State}
    {database : Core.Database} {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.TreePagesSelected := by
  unfold updateState? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    exact updateStateCandidate?_treePagesSelected candidateResult
  next => contradiction

theorem updateState?_selectedPageIds_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.table.after.tree.root.pageIds =
      delta.table.before.tree.root.pageIds := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, _, selected⟩
  exact alignTables?_selectedPageIds_of_indexed alignment selected
    (updateState?_tablePagesSufficient updated) indexed

theorem updateState?_activePageIds_eq_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.after.activePageIds = state.activePageIds := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, alignedTables, selected⟩
  unfold CoreChunkPageState.State.activePageIds
  rw [← alignedTables]
  exact alignTables?_tablePageIds_changed_indexed alignment selected
    (updateState?_tablePagesSufficient updated) indexed

theorem updateState?_nextPage_eq_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.after.nextPage = state.nextPage := by
  have alignment := updateState?_alignment updated
  rcases alignment with ⟨aligned, alignedResult, alignedTables, selected⟩
  have nextPage := alignTables?_nextPage_changed_indexed alignedResult selected
    (updateState?_tablePagesSufficient updated) indexed
  unfold updateState? at updated
  rcases Option.bind_eq_some.mp updated with
    ⟨candidate, candidateResult, updated⟩
  split at updated
  next =>
    injection updated with equal
    subst candidate
    unfold updateStateCandidate? at candidateResult
    rcases Option.bind_eq_some.mp candidateResult with
      ⟨builtAligned, builtResult, candidateResult⟩
    rcases Option.bind_eq_some.mp candidateResult with
      ⟨table, tableResult, candidateResult⟩
    split at candidateResult
    next =>
      injection candidateResult with equal
      subst delta
      have alignedEqual : builtAligned = aligned := by
        rw [builtResult] at alignedResult
        exact Option.some.inj alignedResult
      subst builtAligned
      simpa using nextPage
    next => contradiction
  next => contradiction

theorem updateState?_freedPageNumbers_eq_nil_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.table.freedPageNumbers = [] := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, alignedTables, selected⟩
  exact alignTables?_selectedFreedPages_of_indexed alignment selected
    (updateState?_tablePagesSufficient updated) indexed

theorem updateState?_freePages_eq_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.after.freePages = state.freePages := by
  rw [updateState?_freePages updated,
    updateState?_freedPageNumbers_eq_nil_of_indexed updated indexed]
  rfl

/-- Indexed ordinary updates are allocation-preserving by construction: the
active page IDs, database watermark, and freelist are all exactly unchanged.
This removes the need for a second runtime allocation scan when the final
header/freelist write plan is certified. -/
theorem updateState?_allocationWellFormed_of_indexed
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (allocation : state.AllocationWellFormed)
    (updated : updateState? state database = some delta)
    (indexed : delta.table.before.table.indexes ≠ []) :
    delta.after.AllocationWellFormed := by
  unfold CoreChunkPageState.State.AllocationWellFormed at allocation ⊢
  rw [updateState?_activePageIds_eq_of_indexed updated indexed,
    updateState?_nextPage_eq_of_indexed updated indexed,
    updateState?_freePages_eq_of_indexed updated indexed]
  exact allocation

theorem updateState?_selected_mem
    {state : CoreChunkPageState.State} {database : Core.Database}
    {delta : StateDelta}
    (updated : updateState? state database = some delta) :
    delta.table.before ∈ state.tables ∧
      delta.table.after ∈ delta.after.tables := by
  rcases updateState?_alignment updated with
    ⟨aligned, alignment, alignedTables, selected⟩
  have found := alignTables?_selected_mem alignment selected
  exact ⟨found.1, by simpa [alignedTables] using found.2⟩

def numberedWrite? (page : CorePageCodec.NumberedPage) :
    Option (GrowableStorage.PageWrite PhysicalCodec.pageSize) :=
  if _positive : 0 < page.pageNumber then
    some ⟨page.pageNumber - 1, page.page.storage⟩
  else none

theorem numberedWrite?_spec
    {page : CorePageCodec.NumberedPage}
    {write : GrowableStorage.PageWrite PhysicalCodec.pageSize}
    (converted : numberedWrite? page = some write) :
    write.pageId + 1 = page.pageNumber ∧
      write.page.bytes.toList = page.page.bytes := by
  unfold numberedWrite? at converted
  split at converted
  next positive =>
    have equal :
        (⟨page.pageNumber - 1, page.page.storage⟩ :
          GrowableStorage.PageWrite PhysicalCodec.pageSize) = write :=
      Option.some.inj converted
    subst write
    constructor
    · change (page.pageNumber - 1) + 1 = page.pageNumber
      exact Nat.sub_add_cancel positive
    · simp [CoreFile.Page.storage]
  next => contradiction

theorem mapM_numberedWrite?_covers :
    ∀ {pages : List CorePageCodec.NumberedPage}
      {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)},
      pages.mapM numberedWrite? = some writes →
      ∀ page ∈ pages,
        ∃ write ∈ writes,
          write.pageId + 1 = page.pageNumber ∧
          write.page.bytes.toList = page.page.bytes
  | [], writes, converted => by
      simp only [List.mapM_nil, pure, Option.pure_def,
        Option.some.injEq] at converted
      subst writes
      simp
  | page :: pages, writes, converted => by
      simp only [List.mapM_cons] at converted
      cases headResult : numberedWrite? page with
      | none => simp [headResult] at converted
      | some write =>
        simp only [headResult, Option.bind_eq_bind, Option.bind] at converted
        cases tailResult : pages.mapM numberedWrite? with
        | none => simp [tailResult] at converted
        | some remaining =>
          simp only [tailResult, Option.some.injEq] at converted
          have equal : write :: remaining = writes := by simpa using converted
          subst writes
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with equal | later
          · subst candidate
            exact ⟨write, by simp, numberedWrite?_spec headResult⟩
          · rcases mapM_numberedWrite?_covers tailResult candidate later with
              ⟨covered, coveredMember, specification⟩
            exact ⟨covered, by simp [coveredMember], specification⟩

/-- Conversely, every emitted write comes from one selected numbered page.
Together with `mapM_numberedWrite?_covers`, successful conversion is a
byte-preserving correspondence rather than a one-sided coverage check. -/
theorem mapM_numberedWrite?_sources :
    ∀ {pages : List CorePageCodec.NumberedPage}
      {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)},
      pages.mapM numberedWrite? = some writes →
      ∀ write ∈ writes,
        ∃ page ∈ pages,
          write.pageId + 1 = page.pageNumber ∧
          write.page.bytes.toList = page.page.bytes
  | [], writes, converted => by
      simp only [List.mapM_nil, pure, Option.pure_def,
        Option.some.injEq] at converted
      subst writes
      simp
  | page :: pages, writes, converted => by
      simp only [List.mapM_cons] at converted
      cases headResult : numberedWrite? page with
      | none => simp [headResult] at converted
      | some head =>
        simp only [headResult, Option.bind_eq_bind, Option.bind] at converted
        cases tailResult : pages.mapM numberedWrite? with
        | none => simp [tailResult] at converted
        | some tail =>
          simp only [tailResult, Option.some.injEq] at converted
          have equal : head :: tail = writes := by simpa using converted
          subst writes
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with rfl | later
          · exact ⟨page, by simp, numberedWrite?_spec headResult⟩
          · rcases mapM_numberedWrite?_sources tailResult candidate later with
              ⟨source, sourceMember, specification⟩
            exact ⟨source, by simp [sourceMember], specification⟩

def writes (delta : TableDelta) :
    Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) :=
  delta.pages.mapM numberedWrite?

/-- Every numbered page selected by a table delta is present byte-for-byte in
its physical write list.  This is the changed-page half of the localized
decoder representation proof. -/
theorem writes_covers_pages {delta : TableDelta}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (converted : CoreChunkPageDelta.writes delta = some writes) :
    ∀ page ∈ delta.pages,
      ∃ write ∈ writes,
        write.pageId + 1 = page.pageNumber ∧
        write.page.bytes.toList = page.page.bytes := by
  exact mapM_numberedWrite?_covers converted

theorem writes_sources_pages {delta : TableDelta}
    {writes : List (GrowableStorage.PageWrite PhysicalCodec.pageSize)}
    (converted : CoreChunkPageDelta.writes delta = some writes) :
    ∀ write ∈ writes,
      ∃ page ∈ delta.pages,
        write.pageId + 1 = page.pageNumber ∧
        write.page.bytes.toList = page.page.bytes := by
  exact mapM_numberedWrite?_sources converted

def beforeWrites (delta : TableDelta) :
    Option (List (GrowableStorage.PageWrite PhysicalCodec.pageSize)) := do
  let pages ← (match delta.beforePages? with
    | some pages => some pages
    | none => CorePageCodec.encodeChunkPath delta.before.table.schema
        delta.chunkKey delta.before.tree.root)
  pages.mapM numberedWrite?

end CoreChunkPageDelta
end SQLeanite
