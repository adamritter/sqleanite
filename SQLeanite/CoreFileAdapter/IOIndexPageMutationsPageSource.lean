import SQLeanite.CoreFileAdapter.ByteArrayPageSourceEqStorageImage

namespace SQLeanite
namespace CoreFileAdapter

def IOIndexPageMutations.pageSource (state : IOIndexPageMutations) :
    CoreDecode.IOPageSource := {
  usable := state.source.usable
  pageCount := state.nextPage - 1
  readPage := state.readPage? }

def IOIndexPageMutations.writePage? (state : IOIndexPageMutations)
    (pageNumber : Nat) (page : CoreFile.Page) : Option IOIndexPageMutations := do
  if _valid : 0 < pageNumber ∧ pageNumber < state.nextPage then
    some { state with
      changed := replaceChangedPage pageNumber page.bytes state.changed }
  else none

def IOIndexPageMutations.allocatePage? (state : IOIndexPageMutations)
    (page : CoreFile.Page) : Option (Nat × IOIndexPageMutations) := do
  if _fits : state.nextPage < 2 ^ 32 then
    some (state.nextPage, {
      state with
      changed := replaceChangedPage state.nextPage page.bytes state.changed
      nextPage := state.nextPage + 1 })
  else none

/-- Split exactly `count` elements in one traversal, rejecting a short input. -/
def takeExact : Nat → List α → Option (List α × List α)
  | 0, input => some ([], input)
  | _ + 1, [] => none
  | count + 1, byte :: input => do
      let (front, suffix) ← takeExact count input
      some (byte :: front, suffix)

theorem takeExact_spec {count : Nat} {input front suffix : List α}
    (success : takeExact count input = some (front, suffix)) :
    front.length = count ∧ front ++ suffix = input := by
  induction count generalizing input front suffix with
  | zero =>
      simp only [takeExact, Option.some.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      simp
  | succ count induction =>
      cases input with
      | nil => simp [takeExact] at success
      | cons byte input =>
          simp only [takeExact, Option.bind_eq_bind, Option.bind] at success
          cases recursive : takeExact count input with
          | none => simp [recursive] at success
          | some result =>
              rcases result with ⟨tail, rest⟩
              simp only [recursive, Option.some.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              rcases induction recursive with ⟨length, reconstruct⟩
              simp [length, reconstruct]

def splitInlineIndexCells : Nat → List UInt8 →
    Option (List (List UInt8) × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (payloadSize, _afterSize) ← FileFormat.decodeVarint input
      if _inline : payloadSize.val ≤
          FileFormat.indexMaxLocal PhysicalCodec.usablePageSize then
        -- This path only accepts canonical packed generated pages.  Derive
        -- the canonical varint width from its decoded value instead of
        -- repeatedly traversing the shrinking page suffix twice per cell.
        -- A non-minimal external varint therefore fails closed below when
        -- its suffix does not line up with the declared cell count.
        let prefixLength := FileFormat.sqliteVarintSize payloadSize.val
        let cellLength := prefixLength + payloadSize.val
        let (cell, rest) ← takeExact cellLength input
        let tail ← splitInlineIndexCells count rest
        some (cell :: tail.1, tail.2)
      else none

def inlineIndexLeafCells? (page : List UInt8) :
    Option (List (List UInt8)) := do
  if _canonical : CoreDecode.canonicalIndexLeafPointersBeginAtContent page then
    let (count, content) ← CoreDecode.canonicalIndexLeafContent? page
    let (cells, suffix) ← splitInlineIndexCells count content
    if suffix.isEmpty then some cells else none
  else none

def popGreatestIndexEntry? : Nat → Nat → IndexPageMutations →
    Option (CoreDecode.IndexEntry × IndexPageMutations)
  | 0, _, _ => none
  | fuel + 1, pageNumber, state => do
      let page ← state.readPage? pageNumber
      let source := state.pageSource
      match CoreDecode.decodeIndexInteriorFrom source page with
      | some (_, rightmost) =>
          popGreatestIndexEntry? fuel rightmost state
      | none => do
          let cells ← inlineIndexLeafCells? page
          let greatestCell ← cells.getLast?
          let (greatest, suffix) ←
            CoreDecode.decodeIndexCellWithSuffix greatestCell
          if _consumed : suffix = [] then
            let replacement ← CoreFile.indexLeafPage? cells.dropLast
            let updated ← state.writePage? pageNumber replacement
            some (greatest, updated)
          else none

def indexEntryAfter (left right : CoreDecode.IndexEntry) : Bool :=
  left ≠ right && !CoreChunkPageDelta.indexEntryLess left right

/-- Remove an ordered target subsequence from ordered inline leaf cells in one
linear pass. Unlike repeated byte-list membership, every cell is decoded and
compared at most once. -/
def deleteSortedIndexCells? : List (List UInt8) →
    List CoreDecode.IndexEntry → Option (List (List UInt8))
  | cells, [] => some cells
  | [], _ :: _ => none
  | cell :: cells, target :: targets => do
      let (entry, suffix) ← CoreDecode.decodeIndexCellWithSuffix cell
      if _consumed : suffix = [] then
        if entry = target then deleteSortedIndexCells? cells targets
        else if CoreChunkPageDelta.indexEntryLess entry target then
          (deleteSortedIndexCells? cells (target :: targets)).map (cell :: ·)
        else none
      else none

/-- Insert one exact encoded entry into an ordered inline leaf.  Equality is a
duplicate `(value,rowid)` and is rejected; page construction below remains the
single authority for whether the enlarged leaf still fits. -/
def insertSortedIndexCell? (target : CoreDecode.IndexEntry)
    (targetCell : List UInt8) : List (List UInt8) →
      Option (List (List UInt8))
  | [] => some [targetCell]
  | cell :: cells => do
      let (entry, suffix) ← CoreDecode.decodeIndexCellWithSuffix cell
      if _consumed : suffix = [] then
        if target = entry then none
        else if CoreChunkPageDelta.indexEntryLess target entry then
          some (targetCell :: cell :: cells)
        else
          (insertSortedIndexCell? target targetCell cells).map (cell :: ·)
      else none

/-- Descend by the promoted entries stored in an SQLite index interior page.
The interior page is unchanged: this fast path succeeds only when the target
leaf absorbs the new cell without a split. -/
def insertIndexEntryNoSplit? : Nat → Nat → CoreDecode.IndexEntry →
    List UInt8 → IndexPageMutations → Option IndexPageMutations
  | 0, _, _, _, _ => none
  | fuel + 1, pageNumber, target, targetCell, state => do
      let page ← state.readPage? pageNumber
      let source := state.pageSource
      match CoreDecode.decodeIndexInteriorFrom source page with
      | some (entries, rightmost) =>
          let rec descend : List (Nat × CoreDecode.IndexEntry) →
              Option IndexPageMutations
            | [] => insertIndexEntryNoSplit? fuel rightmost target targetCell state
            | (child, separator) :: remaining =>
                if target = separator then none
                else if CoreChunkPageDelta.indexEntryLess target separator then
                  insertIndexEntryNoSplit? fuel child target targetCell state
                else descend remaining
          descend entries
      | none => do
          let cells ← inlineIndexLeafCells? page
          let inserted ← insertSortedIndexCell? target targetCell cells
          let rewritten ← CoreFile.indexLeafPage? inserted
          state.writePage? pageNumber rewritten

/-- Page-directed I/O implementation of `insertIndexEntryNoSplit?`.  Its
control decisions and leaf rewrite are identical; only the unchanged-page
reads are performed through `pread`. -/
def insertIndexEntryNoSplitIO? : Nat → Nat → CoreDecode.IndexEntry →
    List UInt8 → IOIndexPageMutations → IO (Option IOIndexPageMutations)
  | 0, _, _, _, _ => pure none
  | fuel + 1, pageNumber, target, targetCell, state => do
      let some page ← state.readPage? pageNumber | return none
      let source := state.pageSource
      match ← CoreDecode.decodeIndexInteriorIOFrom source page with
      | some (entries, rightmost) =>
          let rec descend : List (Nat × CoreDecode.IndexEntry) →
              IO (Option IOIndexPageMutations)
            | [] =>
                insertIndexEntryNoSplitIO? fuel rightmost target targetCell state
            | (child, separator) :: remaining =>
                if target = separator then pure none
                else if CoreChunkPageDelta.indexEntryLess target separator then
                  insertIndexEntryNoSplitIO? fuel child target targetCell state
                else descend remaining
          descend entries
      | none =>
          match inlineIndexLeafCells? page with
          | none => pure none
          | some cells =>
              match insertSortedIndexCell? target targetCell cells with
              | none => pure none
              | some inserted =>
                  match CoreFile.indexLeafPage? inserted with
                  | none => pure none
                  | some rewritten => pure (state.writePage? pageNumber rewritten)

inductive IOIndexInsertResult where
  | done (state : IOIndexPageMutations)
  | split (state : IOIndexPageMutations) (leftPage : Nat)
      (promoted : CoreDecode.IndexEntry) (rightPage : Nat)

private def coreFilePage? (bytes : List UInt8) : Option CoreFile.Page :=
  if exact : bytes.length = PhysicalCodec.pageSize then
    some ⟨bytes, exact⟩
  else none

/-- Encode an enlarged interior node, splitting it around one promoted entry
when its exact byte representation no longer fits.  Promoted entries are
removed from both children, matching SQLite index-B-tree semantics. -/
private def rewriteOrSplitIndexInteriorIO?
    (pageNumber : Nat) (entries : List (Nat × CoreDecode.IndexEntry))
    (rightmost : Nat) (state : IOIndexPageMutations) :
    Option IOIndexInsertResult :=
  match indexInteriorPageFromEntries? entries rightmost with
  | some page => (state.writePage? pageNumber page).map IOIndexInsertResult.done
  | none => do
      let middleIndex := entries.length / 2
      let middle ← entries[middleIndex]?
      let leftEntries := entries.take middleIndex
      let rightEntries := entries.drop (middleIndex + 1)
      let leftPage ← indexInteriorPageFromEntries? leftEntries middle.1
      let rightPage ← indexInteriorPageFromEntries? rightEntries rightmost
      let leftState ← state.writePage? pageNumber leftPage
      let (rightNumber, finalState) ← leftState.allocatePage? rightPage
      some (.split finalState pageNumber middle.2 rightNumber)

private structure IndexInsertRoute where
  child : Nat
  prior : List (Nat × CoreDecode.IndexEntry)
  boundary : Option (Nat × CoreDecode.IndexEntry)
  remaining : List (Nat × CoreDecode.IndexEntry)

private def indexInsertRoute? (target : CoreDecode.IndexEntry)
    (rightmost : Nat) : List (Nat × CoreDecode.IndexEntry) →
      List (Nat × CoreDecode.IndexEntry) → Option IndexInsertRoute
  | [], reversed => some {
      child := rightmost
      prior := reversed.reverse
      boundary := none
      remaining := [] }
  | current :: remaining, reversed =>
      if target = current.2 then none
      else if CoreChunkPageDelta.indexEntryLess target current.2 then
        some {
          child := current.1
          prior := reversed.reverse
          boundary := some current
          remaining }
      else indexInsertRoute? target rightmost remaining (current :: reversed)

/-- Full high-fanout index insertion.  A leaf split promotes one cell; an
interior page either absorbs that promotion or splits recursively. -/
def insertIndexEntryIO? : Nat → Nat → CoreDecode.IndexEntry → List UInt8 →
    IOIndexPageMutations → IO (Option IOIndexInsertResult)
  | 0, _, _, _, _ => pure none
  | fuel + 1, pageNumber, target, targetCell, state => do
      let some page ← state.readPage? pageNumber | return none
      let source := state.pageSource
      match ← CoreDecode.decodeIndexInteriorIOFrom source page with
      | some (entries, rightmost) =>
          let some route := indexInsertRoute? target rightmost entries [] |
            return none
          let some child ← insertIndexEntryIO? fuel route.child target
            targetCell state | return none
          match child with
          | .done next => return some (.done next)
          | .split next left promoted right =>
              match route.boundary with
              | none =>
                  return rewriteOrSplitIndexInteriorIO? pageNumber
                    (route.prior ++ [(left, promoted)]) right next
              | some current =>
                  return rewriteOrSplitIndexInteriorIO? pageNumber
                    (route.prior ++ [(left, promoted), (right, current.2)] ++
                      route.remaining) rightmost next
      | none =>
          match inlineIndexLeafCells? page with
          | none => return none
          | some cells =>
              match insertSortedIndexCell? target targetCell cells with
              | none => return none
              | some inserted =>
                  match CoreFile.indexLeafPage? inserted with
                  | some rewritten =>
                      return (state.writePage? pageNumber rewritten).map
                        IOIndexInsertResult.done
                  | none =>
                      let middleIndex := inserted.length / 2
                      let some middleCell := inserted[middleIndex]? | return none
                      let some (promoted, suffix) :=
                        CoreDecode.decodeIndexCellWithSuffix middleCell |
                          return none
                      unless suffix = [] do return none
                      let some leftPage :=
                        CoreFile.indexLeafPage? (inserted.take middleIndex) |
                          return none
                      let some rightPage := CoreFile.indexLeafPage?
                        (inserted.drop (middleIndex + 1)) | return none
                      let some leftState := state.writePage? pageNumber leftPage |
                        return none
                      let some (rightNumber, finalState) :=
                        leftState.allocatePage? rightPage | return none
                      return some (.split finalState pageNumber promoted rightNumber)

/-- Keep the catalog root page stable.  When the old root splits, its left
image is copied to a fresh page and the old root becomes a one-separator
interior node. -/
def insertIndexEntryAtRootIO? (rootPage : Nat)
    (target : CoreDecode.IndexEntry) (targetCell : List UInt8)
    (state : IOIndexPageMutations) : IO (Option IOIndexPageMutations) := do
  let some result ← insertIndexEntryIO? (state.source.pageCount + 1)
    rootPage target targetCell state | return none
  match result with
  | .done next => return some next
  | .split next _ promoted rightPage =>
      let some leftBytes ← next.readPage? rootPage | return none
      let some leftPage := coreFilePage? leftBytes | return none
      let some (leftNumber, allocated) := next.allocatePage? leftPage | return none
      let some newRoot := indexInteriorPageFromEntries?
        [(leftNumber, promoted)] rightPage | return none
      return allocated.writePage? rootPage newRoot

/-- Delete a batch of exact encoded entries by partitioning them at the same
promoted separators used by SQLite routing. Each affected leaf is unpacked and
rewritten once, regardless of how many target rows it contains. -/
def deleteIndexEntriesBatch? : Nat → Nat → List CoreDecode.IndexEntry →
    IndexPageMutations → Option IndexPageMutations
  | 0, _, _, _ => none
  | _, _, [], state => some state
  | fuel + 1, pageNumber, targets, state => do
      let page ← state.readPage? pageNumber
      let source := state.pageSource
      match CoreDecode.decodeIndexInteriorFrom source page with
      | some ([(leftPage, separator)], rightPage) => do
          let leftTargets := targets.filter fun target =>
            CoreChunkPageDelta.indexEntryLess target separator
          let rightTargets := targets.filter fun target =>
            indexEntryAfter target separator
          let left ← deleteIndexEntriesBatch? fuel leftPage leftTargets state
          let right ← deleteIndexEntriesBatch? fuel rightPage rightTargets left
          if targets.contains separator then
            let replacement ← popGreatestIndexEntry? fuel leftPage right
            let rewritten ← indexInteriorPageFromEntries?
              [(leftPage, replacement.1)] rightPage
            replacement.2.writePage? pageNumber rewritten
          else some right
      | some ([(leftPage, firstSeparator),
          (middlePage, secondSeparator)], rightPage) => do
          let leftTargets := targets.filter fun target =>
            CoreChunkPageDelta.indexEntryLess target firstSeparator
          let middleTargets := targets.filter fun target =>
            indexEntryAfter target firstSeparator &&
              CoreChunkPageDelta.indexEntryLess target secondSeparator
          let rightTargets := targets.filter fun target =>
            indexEntryAfter target secondSeparator
          let left ← deleteIndexEntriesBatch? fuel leftPage leftTargets state
          let middle ← deleteIndexEntriesBatch? fuel middlePage
            middleTargets left
          let right ← deleteIndexEntriesBatch? fuel rightPage rightTargets middle
          let first ← if targets.contains firstSeparator then do
              let replacement ← popGreatestIndexEntry? fuel leftPage right
              some (replacement.1, replacement.2)
            else some (firstSeparator, right)
          let second ← if targets.contains secondSeparator then do
              let replacement ← popGreatestIndexEntry? fuel middlePage first.2
              some (replacement.1, replacement.2)
            else some (secondSeparator, first.2)
          if targets.contains firstSeparator || targets.contains secondSeparator then
            let rewritten ← indexInteriorPageFromEntries?
              [(leftPage, first.1), (middlePage, second.1)] rightPage
            second.2.writePage? pageNumber rewritten
          else some second.2
      | some _ => none
      | none => do
          let cells ← inlineIndexLeafCells? page
          let retained ← deleteSortedIndexCells? cells targets
          let rewritten ← CoreFile.indexLeafPage? retained
          state.writePage? pageNumber rewritten

def deletedRowsOrdered? : List Core.Row → List Core.Row →
    Option (List Core.Row)
  | [], [] => some []
  | [], _ :: _ => none
  | rows, [] => some rows
  | old :: olds, row :: rows =>
      if old.rowid = row.rowid then deletedRowsOrdered? olds rows
      else if old.rowid.value < row.rowid.value then do
        let deleted ← deletedRowsOrdered? olds (row :: rows)
        some (old :: deleted)
      else none

/-- The merge walk accounts for every pre-state row exactly once: a row is
either consumed by the retained post-state or returned as deleted. -/
theorem deletedRowsOrdered?_length {before after deleted : List Core.Row}
    (success : deletedRowsOrdered? before after = some deleted) :
    before.length = deleted.length + after.length := by
  induction before generalizing after deleted with
  | nil =>
      cases after with
      | nil =>
          simp only [deletedRowsOrdered?, Option.some.injEq] at success
          subst deleted
          rfl
      | cons row rows => simp [deletedRowsOrdered?] at success
  | cons old olds induction =>
      cases after with
      | nil =>
          simp only [deletedRowsOrdered?, Option.some.injEq] at success
          subst deleted
          simp
      | cons row rows =>
          simp only [deletedRowsOrdered?] at success
          split at success
          next =>
            have tail := induction success
            simp only [List.length_cons]
            omega
          next =>
            split at success
            next =>
              rcases Option.bind_eq_some_iff.mp success with ⟨tail, recursive, equal⟩
              simp only [Option.some.injEq] at equal
              subst deleted
              have tailLength := induction (after := row :: rows) recursive
              simp only [List.length_cons] at tailLength ⊢
              omega
            next => contradiction

def deletedRows? (before after : Core.Table) : Option (List Core.Row) :=
  deletedRowsOrdered? before.rows after.rows

def deleteIndexRowsFromPages? (rootPage : Nat) (index : Core.Index)
    (rows : List Core.Row) (source : CoreDecode.PageSource) :
    Option IndexPageMutations :=
  deleteIndexEntriesBatch? (source.pageCount + 1) rootPage
    (CoreChunkPageDelta.sortIndexEntries
      (rows.map (CoreChunkPageDelta.indexEntryOfRow index))) { source }

def insertIndexRowIntoPages? (rootPage : Nat) (index : Core.Index)
    (row : Core.Row) (source : CoreDecode.PageSource) :
    Option IndexPageMutations := do
  let entry := CoreChunkPageDelta.indexEntryOfRow index row
  let cell ← indexEntryCell? entry
  insertIndexEntryNoSplit? (source.pageCount + 1) rootPage entry cell { source }

def insertIndexRowIntoPagesIO? (rootPage : Nat) (index : Core.Index)
    (row : Core.Row) (source : CoreDecode.IOPageSource) (nextPage : Nat) :
    IO (Option IOIndexPageMutations) := do
  let entry := CoreChunkPageDelta.indexEntryOfRow index row
  let some cell := indexEntryCell? entry | return none
  insertIndexEntryAtRootIO? rootPage entry cell {
    source
    nextPage }

end CoreFileAdapter

end SQLeanite
