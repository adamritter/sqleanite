import SQLeanite.CoreLazyWrite.SubtreePages

namespace SQLeanite
namespace CoreLazyWrite

/-- A page of inline cells decodes identically from any source: the pointer-directed
leaf decoder consults the source only to follow overflow chains. -/
theorem decodeRowsByPointersFrom_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (page : List UInt8)
    (inline : PageInline page) :
    CoreDecode.decodeRowsByPointersFrom schema left page
      = CoreDecode.decodeRowsByPointersFrom schema right page := by
  unfold CoreDecode.decodeRowsByPointersFrom
  refine bind_congr' ?_
  intro cells cellsResult
  exact mapM_congr fun cell member =>
    decodeRowCellFrom_congr schema left right _ _ cell
      (inline cells cellsResult cell member)

/-- A leaf whose cells are all inline, on both decoding routes. -/
def LeafInline (schema : Core.Schema) (source : CoreDecode.PageSource)
    (page : List UInt8) : Prop :=
  PageInline page ∧
    ∀ count content, CoreDecode.canonicalLeafContent? 0 page = some (count, content) →
      PackedInline schema source (source.pageCount + 1) count content

theorem LeafInline_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (page : List UInt8)
    (inline : LeafInline schema left page) : LeafInline schema right page :=
  ⟨inline.1, fun count content content? =>
    PackedInline_congr schema left right _ _ count content
      (inline.2 count content content?)⟩

/-- **The leaf premise, discharged.** A leaf of inline cells decodes identically
from any source, so a page write elsewhere in the file cannot change it. This is
what `decodeSubtreeRowsFrom_congr` needs, and together with it the frame half of
the page-local write argument is complete for tables whose rows fit inline. -/
theorem decodeRowsFrom_congr (schema : Core.Schema)
    (left right : CoreDecode.PageSource) (page : List UInt8)
    (inlineLeft : LeafInline schema left page)
    (inlineRight : LeafInline schema right page) :
    CoreDecode.decodeRowsFrom schema left page
      = CoreDecode.decodeRowsFrom schema right page := by
  unfold CoreDecode.decodeRowsFrom
  by_cases canonical : CoreDecode.canonicalPointersBeginAtContent page
  · simp only [canonical, if_pos]
    cases contentResult : CoreDecode.canonicalLeafContent? 0 page with
    | none =>
        simp only [contentResult]
        exact decodeRowsByPointersFrom_congr schema left right page inlineLeft.1
    | some pair =>
        obtain ⟨count, content⟩ := pair
        simp only [contentResult]
        rw [decodePackedRowCellsFrom_congr schema left right
          (left.pageCount + 1) (right.pageCount + 1) count content
          (inlineLeft.2 count content contentResult)]
        cases packedResult : CoreDecode.decodePackedRowCellsFrom schema right
            (right.pageCount + 1) count content with
        | none =>
            exact decodeRowsByPointersFrom_congr schema left right page inlineLeft.1
        | some rowsPair =>
            obtain ⟨rows, suffix⟩ := rowsPair
            cases suffix with
            | nil => rfl
            | cons a rest =>
                exact decodeRowsByPointersFrom_congr schema left right page
                  inlineLeft.1
  · simp only [canonical, if_neg]
    exact decodeRowsByPointersFrom_congr schema left right page inlineLeft.1

/-- `Option.bind_some` in the `>>=` form the `do`-notation elaborates to. Same
mismatch as `bind_congr'`: the library lemma is stated for `Option.bind` and does not
fire on `Bind.bind`. -/
@[simp] theorem some_bind' {α β : Type} (a : α) (f : α → Option β) :
    (some a >>= f) = f a := rfl

/-- The accumulator factors out of the interior fold.

`decodeSubtreeRowsFrom` accumulates children's rows with `foldlM`, so reasoning about
where a key lands means reasoning about that accumulator. Factoring it out turns the
fold into "decode the children, then prepend" and makes the `orderedUpsert`
distribution lemmas applicable. -/
theorem foldlM_acc {α β : Type} (f : α → Option (List β)) :
    ∀ (elements : List α) (acc : List β),
      elements.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) acc
        = (elements.foldlM (fun a x => (f x).bind (fun r => some (a ++ r)))
            []).map (fun tail => acc ++ tail)
  | [], acc => by simp
  | x :: rest, acc => by
      simp only [List.foldlM_cons]
      cases headResult : f x with
      | none => simp
      | some head =>
          simp only [some_bind', Option.bind_some, List.nil_append]
          rw [foldlM_acc f rest (acc ++ head), foldlM_acc f rest head]
          cases restResult : rest.foldlM
              (fun a x => (f x).bind (fun r => some (a ++ r))) [] with
          | none => simp
          | some tail => simp [List.append_assoc]

/-- An insert whose key precedes every row in the tail only disturbs the head. -/
theorem orderedUpsert_append_of_beforeAll (row : Core.Row) :
    ∀ (front back : List Core.Row),
      (∀ later ∈ back, row.rowid.value < later.rowid.value) →
      Core.orderedUpsert row (front ++ back)
        = Core.orderedUpsert row front ++ back
  | [], back, beforeAll => by
      cases back with
      | nil => rfl
      | cons later rest =>
          have rowBefore : row.rowid.value < later.rowid.value :=
            beforeAll later List.mem_cons_self
          simp [Core.orderedUpsert, rowBefore]
  | existing :: front, back, beforeAll => by
      by_cases rowFirst : row.rowid.value < existing.rowid.value
      · simp [Core.orderedUpsert, rowFirst]
      · by_cases existingFirst : existing.rowid.value < row.rowid.value
        · simp only [List.cons_append, Core.orderedUpsert, if_neg rowFirst,
            if_pos existingFirst, List.cons_append, List.cons.injEq, true_and]
          exact orderedUpsert_append_of_beforeAll row front back beforeAll
        · simp [Core.orderedUpsert, rowFirst, existingFirst]

/-- An insert whose key follows every row in the head only disturbs the tail. -/
theorem orderedUpsert_append_of_afterAll (row : Core.Row) :
    ∀ (front back : List Core.Row),
      (∀ earlier ∈ front, earlier.rowid.value < row.rowid.value) →
      Core.orderedUpsert row (front ++ back)
        = front ++ Core.orderedUpsert row back
  | [], _, _ => rfl
  | existing :: front, back, afterAll => by
      have existingBefore : existing.rowid.value < row.rowid.value :=
        afterAll existing List.mem_cons_self
      have rowNotFirst : ¬row.rowid.value < existing.rowid.value := by omega
      simp only [List.cons_append, Core.orderedUpsert, if_neg rowNotFirst,
        if_pos existingBefore, List.cons_append, List.cons.injEq, true_and]
      exact orderedUpsert_append_of_afterAll row front back
        fun earlier member => afterAll earlier (List.mem_cons_of_mem existing member)

/-- **Routing at a single leaf.** When the whole table lives in one leaf, a
page-local insert is exactly the ordered insert. This is the base case of the
routing argument and the shape the refinement composes over interior levels. -/
theorem singleLeaf_refines (schema : Core.Schema)
    (source : CoreDecode.PageSource) (fuel pageNumber : Nat)
    (page : List UInt8) (row : Core.Row) (rows : List Core.Row)
    (pageResult : source.readPage pageNumber = some page)
    (leaf : CoreDecode.interiorChildren? page = none)
    (decoded : CoreDecode.decodeRowsFrom schema source page = some rows) :
    CoreDecode.decodeSubtreeRowsFrom schema source (fuel + 1) pageNumber
      = some rows := by
  rw [CoreDecode.decodeSubtreeRowsFrom]
  rw [pageResult]
  simpa [leaf] using decoded

/-- **The refinement, single-leaf case.** Writing the re-encoded leaf produces bytes
denoting exactly the table with the row inserted.

This is the whole page-local argument for a table that fits one leaf: the write
replaces that leaf, the new bytes decode to the upserted rows, and no other page is
touched. Interior levels compose on top of it using `decodeSubtreeRowsFrom_congr`
for the untouched siblings and the `orderedUpsert` distribution lemmas to place the
key in the right one. -/
theorem singleLeaf_write_refines (schema : Core.Schema)
    (source : CoreDecode.PageSource)
    (pageWrite : GrowableStorage.PageWrite PhysicalCodec.pageSize)
    (fuel pageNumber : Nat) (page : List UInt8) (row : Core.Row)
    (rows : List Core.Row)
    (target : pageNumber = pageWrite.pageId + 1)
    (leafAfter : CoreDecode.interiorChildren?
      pageWrite.page.bytes.toList = none)
    (decodedAfter : CoreDecode.decodeRowsFrom schema
      (CorePageSource.write source pageWrite) pageWrite.page.bytes.toList
        = some (Core.orderedUpsert row rows)) :
    CoreDecode.decodeSubtreeRowsFrom schema
        (CorePageSource.write source pageWrite) (fuel + 1) pageNumber
      = some (Core.orderedUpsert row rows) := by
  refine singleLeaf_refines schema _ fuel pageNumber
    pageWrite.page.bytes.toList row _ ?_ leafAfter decodedAfter
  subst target
  simp only [CorePageSource.write]
  have notZero : ¬ (pageWrite.pageId + 1 = 0) := by omega
  have notBeyond : ¬ (max source.pageCount (pageWrite.pageId + 1)
      < pageWrite.pageId + 1) := by omega
  simp [notZero, notBeyond]

/-- Exactly one child owns the written page, when the children's page sets are
pairwise disjoint.

Disjointness is stated directly as a `Pairwise` rather than as `Nodup` on the
flattened list: without Mathlib there is no `nodup_append` to take apart, and the
`Pairwise` form is both what the interior walk naturally checks and what this
induction consumes. -/
theorem unique_child_owns {target : Nat} {nested : List (List Nat)}
    (disjoint : nested.Pairwise (fun left right => ∀ p ∈ left, p ∉ right))
    (owned : target ∈ nested.flatten) :
    ∃ before childList after,
      nested = before ++ childList :: after ∧
        target ∈ childList ∧
        (∀ other ∈ after, target ∉ other) := by
  induction nested with
  | nil => simp at owned
  | cons head rest induction =>
      rw [List.flatten_cons] at owned
      cases disjoint with
      | cons headDisjoint restDisjoint =>
          by_cases inHead : target ∈ head
          · exact ⟨[], head, rest, rfl, inHead,
              fun other member => headDisjoint other member target inHead⟩
          · have inRest : target ∈ rest.flatten := by
              rcases List.mem_append.mp owned with here | later
              · exact absurd here inHead
              · exact later
            rcases induction restDisjoint inRest with
              ⟨before, childList, after, shape, found, notAfter⟩
            exact ⟨head :: before, childList, after, by rw [shape]; rfl, found,
              notAfter⟩

/-- `locateLeaf?` always lands on a genuine leaf -- a page with no children.

This is the `targetIsLeaf` premise, and it is what makes the write safe to encode as
a leaf page. It holds because the descent stops only where `interiorChildren?` says
there is nothing to descend into; a page with children but unreadable separators
routes to `none` instead of being mistaken for a leaf. -/
theorem locateLeaf_entries_none (source : CoreDecode.PageSource) (key : Nat) :
    ∀ (fuel pageNumber leafPage : Nat),
      locateLeaf? source key fuel pageNumber = some leafPage →
      ∃ page, source.readPage leafPage = some page ∧
        CoreDecode.interiorChildren? page = none
  | 0, _, _, located => by simp [locateLeaf?] at located
  | fuel + 1, pageNumber, leafPage, located => by
      rw [locateLeaf?] at located
      split at located
      · exact absurd located (by simp)
      · rename_i page pageResult
        split at located
        · rename_i childrenResult
          exact ⟨page, by
            have equal : leafPage = pageNumber := (Option.some.inj located).symm
            rw [equal]; exact pageResult, childrenResult⟩
        · split at located
          · exact absurd located (by simp)
          · exact locateLeaf_entries_none source key fuel _ leafPage located

/-- The leaf `locateLeaf?` selects is one of the subtree's own pages.

Uses the bridge: the descent picks a child from `interiorEntries?`, and
`interiorEntries_children` says those are exactly the children `subtreePages`
enumerates, so the chosen child's page set is part of the parent's. Needs nothing
about whether the separators are *meaningful* -- only that the descent follows real
child pointers. This discharges the "the write is somewhere in this subtree" premise
that the routing induction carries. -/
theorem locateLeaf_mem_subtreePages (source : CoreDecode.PageSource) (key : Nat) :
    ∀ (fuel pageNumber : Nat) (pageList : List Nat) (leafPage : Nat),
      subtreePages source fuel pageNumber = some pageList →
      locateLeaf? source key fuel pageNumber = some leafPage →
      leafPage ∈ pageList
  | 0, _, _, _, _, located => by simp [locateLeaf?] at located
  | fuel + 1, pageNumber, pageList, leafPage, enumerated, located => by
      rw [locateLeaf?] at located
      split at located
      · exact absurd located (by simp)
      · rename_i page pageResult
        split at located
        · -- Stops here, so this page is the answer and roots the enumeration.
          have equal : leafPage = pageNumber := (Option.some.inj located).symm
          rw [equal]
          exact mem_subtreePages_self enumerated
        · split at located
          · exact absurd located (by simp)
          rename_i entries rightmost entriesResult
          have childrenResult := interiorEntries_children entriesResult
          simp only [subtreePages, pageResult, childrenResult] at enumerated
          cases nestedResult :
              (entries.map Prod.fst ++ [rightmost]).mapM (subtreePages source fuel) with
          | none => rw [nestedResult] at enumerated; simp at enumerated
          | some nested =>
              rw [nestedResult] at enumerated
              have listShape : pageList = pageNumber :: nested.flatten :=
                (Option.some.inj enumerated).symm
              have childMem : (match entries.find? (fun entry => key ≤ entry.2) with
                  | some entry => entry.1
                  | none => rightmost) ∈ entries.map Prod.fst ++ [rightmost] := by
                cases found : entries.find? (fun entry => key ≤ entry.2) with
                | none => simp [found]
                | some entry =>
                    have member := List.mem_of_find?_eq_some found
                    simp only [found]
                    exact List.mem_append_left _ (List.mem_map_of_mem member)
              rcases mapM_subtreePages_mem nestedResult _ childMem with
                ⟨childList, childEnumerated, subset⟩
              rw [listShape]
              exact List.mem_cons_of_mem pageNumber
                (subset leafPage (locateLeaf_mem_subtreePages source key fuel _
                  childList leafPage childEnumerated located))

/-- What routing has to establish: the subtree's rows split around the target leaf,
with the inserted key strictly between the two sides.

This is the premise the interior induction actually needs, and stating it explicitly
is the third correction to `subtree_write_refines`. The previous version assumed
`rows.Pairwise keyLess` plus "the write is somewhere in this subtree" was enough. It
is not: those say the table is sorted and the write is *somewhere*, not that the
inserted key belongs in *that* leaf. Writing an upserted leaf 1 when the key belongs
in leaf 5 satisfies every earlier premise and falsifies the conclusion.

Deriving this from `locateLeaf?` -- proving the descent lands where the separators
say it should -- is routing correctness proper, and is the remaining work. Splitting
it out here means the interior induction can be proved against a premise that is
true, rather than against one that quietly is not. -/
structure RoutedSplit (schema : Core.Schema) (source : CoreDecode.PageSource)
    (target : Nat) (row : Core.Row) (rows : List Core.Row) where
  before : List Core.Row
  leafRows : List Core.Row
  after : List Core.Row
  decomposition : rows = before ++ leafRows ++ after
  leafDecodes : ∀ oldLeaf, source.readPage target = some oldLeaf →
    CoreDecode.decodeRowsFrom schema source oldLeaf = some leafRows
  beforeBelow : ∀ earlier ∈ before, earlier.rowid.value < row.rowid.value
  afterAbove : ∀ later ∈ after, row.rowid.value < later.rowid.value

/-- The ordered insert on a routed split touches only the target leaf's segment.

This is the arithmetic content of routing, and it is proved: given the split, the
whole-table insert equals the leaf-local insert spliced back in place. What remains
unproved is only that `locateLeaf?` produces such a split. -/
theorem orderedUpsert_routedSplit (row : Core.Row)
    (before leafRows after : List Core.Row)
    (beforeBelow : ∀ earlier ∈ before, earlier.rowid.value < row.rowid.value)
    (afterAbove : ∀ later ∈ after, row.rowid.value < later.rowid.value) :
    Core.orderedUpsert row (before ++ leafRows ++ after)
      = before ++ Core.orderedUpsert row leafRows ++ after := by
  rw [orderedUpsert_append_of_beforeAll row (before ++ leafRows) after afterAbove,
    orderedUpsert_append_of_afterAll row before leafRows beforeBelow]

/-- Folding over a concatenation splits into the two halves' results.

Routing needs this because the chosen child sits between the children before it and
the children after it, and each group's rows have to be named separately to be
bounded separately. -/
theorem foldlM_split {α β : Type} (f : α → Option (List β))
    (left right : List α) (result : List β)
    (folded : (left ++ right).foldlM
        (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some result) :
    ∃ leftRows rightRows,
      left.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some leftRows ∧
      right.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some rightRows ∧
      result = leftRows ++ rightRows := by
  rw [List.foldlM_append] at folded
  cases leftResult :
      left.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) [] with
  | none => rw [leftResult] at folded; simp at folded
  | some leftRows =>
      rw [leftResult] at folded
      simp only [some_bind'] at folded
      rw [foldlM_acc f right leftRows] at folded
      cases rightResult :
          right.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) [] with
      | none => rw [rightResult] at folded; simp at folded
      | some rightRows =>
          rw [rightResult] at folded
          exact ⟨leftRows, rightRows, rfl, rfl, by simpa using folded.symm⟩

/-- The converse of `foldlM_split`: two halves' results concatenate.

Needed in the write direction, where each group's rows are known separately and the
parent's fold has to be reassembled from them. -/
theorem foldlM_join {α β : Type} (f : α → Option (List β))
    (left right : List α) (leftRows rightRows : List β)
    (leftFold : left.foldlM
      (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some leftRows)
    (rightFold : right.foldlM
      (fun a x => (f x).bind (fun r => some (a ++ r))) [] = some rightRows) :
    (left ++ right).foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) []
      = some (leftRows ++ rightRows) := by
  rw [List.foldlM_append, leftFold]
  simp only [some_bind']
  rw [foldlM_acc f right leftRows, rightFold]
  simp

/-- Every element of a fold's result came from some element of the input.

This is what turns a per-child bound into a bound on the concatenated rows: to show
every row before the target is below the key, it is enough to know which child each
row came from. -/
theorem foldlM_mem {α β : Type} (f : α → Option (List β)) :
    ∀ (elements : List α) (result : List β),
      elements.foldlM (fun a x => (f x).bind (fun r => some (a ++ r))) []
          = some result →
      ∀ b ∈ result, ∃ x, x ∈ elements ∧ ∃ xs, f x = some xs ∧ b ∈ xs := by
  intro elements
  induction elements with
  | nil =>
      intro result folded b member
      simp at folded
      subst folded
      simp at member
  | cons x rest induction =>
      intro result folded b member
      rcases foldlM_split f [x] rest result (by simpa using folded) with
        ⟨headRows, tailRows, headFold, tailFold, shape⟩
      have headEq : f x = some headRows := by simpa using headFold
      subst shape
      rcases List.mem_append.mp member with inHead | inTail
      · exact ⟨x, List.mem_cons_self, headRows, headEq, inHead⟩
      · rcases induction tailRows tailFold b inTail with ⟨y, memY, ys, fy, inYs⟩
        exact ⟨y, List.mem_cons_of_mem x memY, ys, fy, inYs⟩

/-- A bound that holds of every child's rows holds of their concatenation. -/
theorem foldRows_bound (schema : Core.Schema) (source : CoreDecode.PageSource)
    (fuel : Nat) (P : Core.Row → Prop) (group : List Nat) (groupRows : List Core.Row)
    (childBound : ∀ child ∈ group, ∀ childRows,
      CoreDecode.decodeSubtreeRowsFrom schema source fuel child = some childRows →
      ∀ candidate ∈ childRows, P candidate)
    (folded : group.foldlM
      (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema source fuel x).bind
        (fun r => some (a ++ r))) ([] : List Core.Row) = some groupRows) :
    ∀ candidate ∈ groupRows, P candidate := by
  intro candidate member
  rcases foldlM_mem _ group groupRows folded candidate member with
    ⟨child, childMem, childRows, childDecoded, rowMem⟩
  exact childBound child childMem childRows childDecoded candidate rowMem

/-- The subtree's separators really bound its children's rows.

This is the one premise that is about *meaning* rather than structure, and it is what
the 653 ms check in `docs/LAZY_WRITE_DESIGN.md` establishes: a tree-order walk of the
interior pages plus the first and last cell of every leaf, decoding no rows. Stated
recursively because routing descends recursively.

`bounded` is the separator contract: every row in a child's subtree is at or below
that child's separator key. `increasing` is what makes the children's row segments
line up in key order, so that `orderedUpsert_routedSplit` applies. -/
def TreeSound (schema : Core.Schema) (source : CoreDecode.PageSource) :
    Nat → Nat → Prop
  | 0, _ => False
  | fuel + 1, pageNumber =>
      ∀ page, source.readPage pageNumber = some page →
        ∀ entries rightmost, interiorEntries? page = some (entries, rightmost) →
          (∀ child ∈ rightmost :: entries.map Prod.fst,
              TreeSound schema source fuel child) ∧
            (∀ entry ∈ entries, ∀ childRows,
              CoreDecode.decodeSubtreeRowsFrom schema source fuel entry.1
                  = some childRows →
                ∀ candidate ∈ childRows, candidate.treeKey ≤ entry.2) ∧
            (∀ (pre : List (Nat × Nat)) (entry : Nat × Nat)
                (post : List (Nat × Nat)), entries = pre ++ entry :: post →
              ∀ later ∈ rightmost :: post.map Prod.fst, ∀ laterRows,
                CoreDecode.decodeSubtreeRowsFrom schema source fuel later
                    = some laterRows →
                ∀ candidate ∈ laterRows, entry.2 < candidate.treeKey)

/-- The routing key is the rowid biased by a fixed midpoint, so it orders rows the
same way. Separators are compared in key space; `orderedUpsert` in rowid space. -/
theorem value_lt_of_treeKey_lt {left right : Core.Row}
    (less : left.treeKey < right.treeKey) :
    left.rowid.value < right.rowid.value :=
  (Core.Row.treeKey_lt_iff left right).mp less

end CoreLazyWrite

end SQLeanite
