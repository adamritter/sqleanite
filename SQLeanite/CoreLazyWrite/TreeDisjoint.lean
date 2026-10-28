import SQLeanite.CoreLazyWrite.DecodeRowsByPointersFromCongr

namespace SQLeanite
namespace CoreLazyWrite

/-- Sibling subtrees own disjoint page sets.

Stated recursively, in the shape routing consumes: the child the descent enters owns
its pages, so a write inside it is invisible to its siblings. Without this the frame
step is simply false -- a page reachable from two subtrees would change both.

This is what the 80 ms interior-only walk checks. Page identities live in interior
pages, so enumerating every page id and finding no duplicate needs no row decode. -/
def TreeDisjoint (source : CoreDecode.PageSource) : Nat → Nat → Prop
  | 0, _ => False
  | fuel + 1, pageNumber =>
      ∀ page, source.readPage pageNumber = some page →
        ∀ children, CoreDecode.interiorChildren? page = some children →
          (∀ child ∈ children, TreeDisjoint source fuel child) ∧
            ∀ (pre : List Nat) (chosen : Nat) (post : List Nat),
              children = pre ++ chosen :: post →
              ∀ other ∈ pre ++ post, ∀ otherList chosenList,
                subtreePages source fuel other = some otherList →
                subtreePages source fuel chosen = some chosenList →
                ∀ p ∈ chosenList, p ∉ otherList

/-- **The remaining obligation.** A sound tree routes a key to the leaf whose segment
it belongs in, which is exactly a `RoutedSplit`.

With this, `orderedUpsert_routedSplit` gives the whole-table insert, the frame chain
gives the untouched pages, and `insertPlan_refines` follows. Everything else in this
module is proved; this is the single step where the checked ordering premise has to do
work rather than the structural facts.

The proof is an induction on the descent: at each interior page the separators split
the children into those wholly below the key and those wholly above, `TreeSound.bounded`
and `.increasing` place the chosen child between them, and the recursive call supplies
the split one level down. -/
theorem locateLeaf_routedSplit (schema : Core.Schema)
    (source : CoreDecode.PageSource) (key : Nat) (row : Core.Row)
    (keyIsRow : row.treeKey = key) :
    ∀ (fuel pageNumber leafPage : Nat) (rows : List Core.Row),
      TreeSound schema source fuel pageNumber →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel pageNumber = some rows →
      locateLeaf? source key fuel pageNumber = some leafPage →
      Nonempty (RoutedSplit schema source leafPage row rows) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ sound _ _; simp [TreeSound] at sound
  | succ fuel induction =>
    intro pageNumber leafPage rows sound decoded located
    rw [locateLeaf?] at located
    split at located
    · exact absurd located (by simp)
    rename_i page pageResult
    simp only [CoreDecode.decodeSubtreeRowsFrom, pageResult, some_bind'] at decoded
    split at located
    · -- A genuine leaf: the subtree is this one page, so the split is trivial.
      rename_i childrenResult
      simp only [childrenResult] at decoded
      have equal : leafPage = pageNumber := (Option.some.inj located).symm
      exact ⟨{ before := [], leafRows := rows, after := []
               decomposition := by simp
               leafDecodes := by
                 intro oldLeaf readLeaf
                 rw [equal, pageResult] at readLeaf
                 rw [← Option.some.inj readLeaf]
                 exact decoded
               beforeBelow := by simp
               afterAbove := by simp }⟩
    rename_i children childrenResult
    split at located
    · exact absurd located (by simp)
    rename_i entries rightmost entriesResult
    have childrenShape : children = entries.map Prod.fst ++ [rightmost] := by
      have viaEntries := interiorEntries_children entriesResult
      rw [childrenResult] at viaEntries
      exact Option.some.inj viaEntries
    subst childrenShape
    simp only [childrenResult] at decoded
    obtain ⟨soundChildren, bounded, above⟩ :=
      sound page pageResult entries rightmost entriesResult
    have decodedFold :
        (entries.map Prod.fst ++ [rightmost]).foldlM
          (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema source fuel x).bind
            (fun r => some (a ++ r))) ([] : List Core.Row) = some rows := decoded
    cases found : entries.find? (fun entry => key ≤ entry.2) with
    | none =>
        -- No separator covers the key, so it belongs in the rightmost child and
        -- every other child is wholly below it.
        simp only [found] at located
        rcases foldlM_split _ (entries.map Prod.fst) [rightmost] rows decodedFold with
          ⟨preRows, restRows, preFold, restFold, shape⟩
        have restDecoded :
            CoreDecode.decodeSubtreeRowsFrom schema source fuel rightmost
              = some restRows := by simpa using restFold
        rcases induction rightmost leafPage restRows
            (soundChildren rightmost (by simp)) restDecoded located with
          ⟨⟨tailBefore, tailLeaf, tailAfter, tailShape, tailDecodes, tailBelow,
            tailAbove⟩⟩
        refine ⟨{ before := preRows ++ tailBefore
                  leafRows := tailLeaf
                  after := tailAfter
                  decomposition := by rw [shape, tailShape]; simp
                  leafDecodes := tailDecodes
                  afterAbove := tailAbove
                  beforeBelow := ?_ }⟩
        intro earlier member
        rcases List.mem_append.mp member with inPre | inSplit
        · rcases foldlM_mem _ (entries.map Prod.fst) preRows preFold earlier inPre with
            ⟨child, childMem, childRows, childDecoded, rowMem⟩
          rcases List.mem_map.mp childMem with ⟨entry, entryMem, entryEq⟩
          have le := bounded entry entryMem childRows
            (by rw [← entryEq] at childDecoded; exact childDecoded) earlier rowMem
          have lt : entry.2 < key := by
            have missed := (List.find?_eq_none).mp found entry entryMem
            simp at missed
            omega
          refine value_lt_of_treeKey_lt ?_
          rw [keyIsRow]
          omega
        · exact tailBelow earlier inSplit
    | some entry =>
        -- `entry` is the first separator at or above the key: children before it are
        -- wholly below the key, children after it are wholly above `entry.2 ≥ key`.
        simp only [found] at located
        rcases List.find?_eq_some_iff_append.mp found with
          ⟨keyLe, pre, post, entriesShape, preFails⟩
        simp at keyLe
        subst entriesShape
        rw [show ((pre ++ entry :: post).map Prod.fst ++ [rightmost])
              = pre.map Prod.fst ++ ([entry.1] ++ (post.map Prod.fst ++ [rightmost]))
            from by simp] at decodedFold
        rcases foldlM_split _ (pre.map Prod.fst) _ rows decodedFold with
          ⟨preRows, tailRows, preFold, tailFold, shape₁⟩
        rcases foldlM_split _ [entry.1] (post.map Prod.fst ++ [rightmost]) tailRows
          tailFold with ⟨chosenRows, postRows, chosenFold, postFold, shape₂⟩
        have chosenDecoded :
            CoreDecode.decodeSubtreeRowsFrom schema source fuel entry.1
              = some chosenRows := by simpa using chosenFold
        rcases induction entry.1 leafPage chosenRows
            (soundChildren entry.1 (by simp)) chosenDecoded located with
          ⟨⟨midBefore, midLeaf, midAfter, midShape, midDecodes, midBelow, midAbove⟩⟩
        refine ⟨{ before := preRows ++ midBefore
                  leafRows := midLeaf
                  after := midAfter ++ postRows
                  decomposition := by rw [shape₁, shape₂, midShape]; simp
                  leafDecodes := midDecodes
                  beforeBelow := ?_
                  afterAbove := ?_ }⟩
        · intro earlier member
          rcases List.mem_append.mp member with inPre | inSplit
          · rcases foldlM_mem _ (pre.map Prod.fst) preRows preFold earlier inPre with
              ⟨child, childMem, childRows, childDecoded, rowMem⟩
            rcases List.mem_map.mp childMem with ⟨earlierEntry, entryMem, entryEq⟩
            have le := bounded earlierEntry (List.mem_append_left _ entryMem) childRows
              (by rw [← entryEq] at childDecoded; exact childDecoded)
              earlier rowMem
            have lt : earlierEntry.2 < key := by
              have missed := preFails earlierEntry entryMem
              simp at missed
              omega
            refine value_lt_of_treeKey_lt ?_
            rw [keyIsRow]
            omega
          · exact midBelow earlier inSplit
        · intro later member
          rcases List.mem_append.mp member with inSplit | inPost
          · exact midAbove later inSplit
          · rcases foldlM_mem _ (post.map Prod.fst ++ [rightmost]) postRows postFold
              later inPost with ⟨child, childMem, childRows, childDecoded, rowMem⟩
            have memAlt : child ∈ rightmost :: post.map Prod.fst := by
              rcases List.mem_append.mp childMem with inPost' | isRightmost
              · exact List.mem_cons_of_mem _ inPost'
              · simp at isRightmost
                simp [isRightmost]
            have gt := above pre entry post rfl child memAlt childRows childDecoded
              later rowMem
            refine value_lt_of_treeKey_lt ?_
            rw [keyIsRow]
            omega

/-- What a page-local write needs to know about the on-disk tree.

Every field is a *checked* premise, not an assumption, and none of them decodes a
row. `separators` and `disjoint` are established by walking interior pages and each
leaf's first and last cell -- 653 ms on the 1,000,000-row file, against 143,671 ms
for the whole-database open they replace. `inline` is the counting check: if the
enumerated tree pages, page one and the freelist account for every page in the file,
no overflow page exists. So the generated-image stamp keeps its existing weaker
role. -/
structure WellFormedTree (schema : Core.Schema) (source : CoreDecode.PageSource)
    (fuel rootPage : Nat) where
  pages : List Nat
  enumerated : subtreePages source fuel rootPage = some pages
  separators : TreeSound schema source fuel rootPage
  disjoint : TreeDisjoint source fuel rootPage
  inline : ∀ p bytes, source.readPage p = some bytes → LeafInline schema source bytes
  bounded : ∀ p, (p = 0 ∨ source.pageCount < p) → source.readPage p = none
  rows : List Core.Row
  decoded : CoreDecode.decodeSubtreeRowsFrom schema source fuel rootPage = some rows

/-- **The write, routed through the tree.** Rewriting the located leaf changes the
subtree's rows by exactly the ordered insert, and changes nothing else.

Frame and routing have to be one induction rather than two lemmas: the frame step
needs to know *which* child owns the written page, and that is what the descent
decides. Siblings are carried by `decodeSubtreeRowsFrom_congr`, the chosen child by
the induction hypothesis, and `orderedUpsert_routedSplit` splices the three groups
back together. -/
theorem locateLeaf_write_refines (schema : Core.Schema)
    (source new : CoreDecode.PageSource) (key : Nat) (row : Core.Row)
    (keyIsRow : row.treeKey = key)
    (leafPage : Nat) (oldLeafRows : List Core.Row)
    (leafAgrees : ∀ p bytes, source.readPage p = some bytes →
      CoreDecode.decodeRowsFrom schema source bytes
        = CoreDecode.decodeRowsFrom schema new bytes)
    (offTarget : ∀ p, p ≠ leafPage → source.readPage p = new.readPage p)
    (oldTarget : ∀ oldLeaf, source.readPage leafPage = some oldLeaf →
      CoreDecode.decodeRowsFrom schema source oldLeaf = some oldLeafRows)
    (newLeaf : List UInt8)
    (newRead : new.readPage leafPage = some newLeaf)
    (newIsLeaf : CoreDecode.interiorChildren? newLeaf = none)
    (newDecoded : CoreDecode.decodeRowsFrom schema new newLeaf
      = some (Core.orderedUpsert row oldLeafRows)) :
    ∀ (fuel pageNumber : Nat) (rows : List Core.Row) (pageList : List Nat),
      TreeSound schema source fuel pageNumber →
      TreeDisjoint source fuel pageNumber →
      subtreePages source fuel pageNumber = some pageList →
      CoreDecode.decodeSubtreeRowsFrom schema source fuel pageNumber = some rows →
      locateLeaf? source key fuel pageNumber = some leafPage →
      CoreDecode.decodeSubtreeRowsFrom schema new fuel pageNumber
        = some (Core.orderedUpsert row rows) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ sound _ _ _ _; simp [TreeSound] at sound
  | succ fuel induction =>
    intro pageNumber rows pageList sound disjoint enumerated decoded located
    have located₀ := located
    rw [locateLeaf?] at located
    split at located
    · exact absurd located (by simp)
    rename_i page pageResult
    simp only [CoreDecode.decodeSubtreeRowsFrom, pageResult, some_bind'] at decoded
    split at located
    · -- The descent stops here, so the subtree is this one leaf and the write is
      -- the whole of it.
      rename_i childrenResult
      simp only [childrenResult] at decoded
      have equal : leafPage = pageNumber := (Option.some.inj located).symm
      have oldEq : oldLeafRows = rows :=
        Option.some.inj
          ((oldTarget page (by rw [equal]; exact pageResult)).symm.trans decoded)
      refine singleLeaf_refines schema new fuel pageNumber newLeaf row _
        (by rw [← equal]; exact newRead) newIsLeaf ?_
      rw [newDecoded, oldEq]
    rename_i children childrenResult
    split at located
    · exact absurd located (by simp)
    rename_i entries rightmost entriesResult
    have childrenShape : children = entries.map Prod.fst ++ [rightmost] := by
      have viaEntries := interiorEntries_children entriesResult
      rw [childrenResult] at viaEntries
      exact Option.some.inj viaEntries
    subst childrenShape
    simp only [childrenResult] at decoded
    obtain ⟨soundChildren, bounded, above⟩ :=
      sound page pageResult entries rightmost entriesResult
    obtain ⟨disjointChildren, siblingsDisjoint⟩ :=
      disjoint page pageResult _ childrenResult
    -- This page has children, so it is not the leaf that was written.
    have pageNe : pageNumber ≠ leafPage := by
      intro same
      rcases locateLeaf_entries_none source key (fuel + 1) pageNumber leafPage located₀
        with ⟨leafBytes, leafRead, leafNoChildren⟩
      rw [← same, pageResult] at leafRead
      rw [← Option.some.inj leafRead, childrenResult] at leafNoChildren
      exact absurd leafNoChildren (by simp)
    have newPage : new.readPage pageNumber = some page := by
      rw [← offTarget pageNumber pageNe]; exact pageResult
    -- Split the children into those wholly below the key, the one it routes to, and
    -- those wholly above it.  Both `find?` outcomes give the same shape.
    obtain ⟨preChildren, chosen, postChildren, split, preBelow, postAbove, chosenEq⟩ :
        ∃ preChildren chosen postChildren,
          entries.map Prod.fst ++ [rightmost]
              = preChildren ++ chosen :: postChildren ∧
          (∀ child ∈ preChildren, ∀ childRows,
            CoreDecode.decodeSubtreeRowsFrom schema source fuel child
                = some childRows →
            ∀ candidate ∈ childRows,
              candidate.rowid.value < row.rowid.value) ∧
          (∀ child ∈ postChildren, ∀ childRows,
            CoreDecode.decodeSubtreeRowsFrom schema source fuel child
                = some childRows →
            ∀ candidate ∈ childRows,
              row.rowid.value < candidate.rowid.value) ∧
          chosen = (match entries.find? (fun entry => key ≤ entry.2) with
            | some entry => entry.1
            | none => rightmost) := by
      cases found : entries.find? (fun entry => key ≤ entry.2) with
      | none =>
          refine ⟨entries.map Prod.fst, rightmost, [], by simp, ?_, by simp,
            by simp [found]⟩
          intro child childMem childRows childDecoded candidate rowMem
          rcases List.mem_map.mp childMem with ⟨entry, entryMem, entryEq⟩
          rw [← entryEq] at childDecoded
          have le := bounded entry entryMem childRows childDecoded candidate rowMem
          have missed := (List.find?_eq_none).mp found entry entryMem
          simp at missed
          refine value_lt_of_treeKey_lt ?_
          rw [keyIsRow]
          omega
      | some entry =>
          rcases List.find?_eq_some_iff_append.mp found with
            ⟨keyLe, pre, post, entriesShape, preFails⟩
          simp at keyLe
          subst entriesShape
          refine ⟨pre.map Prod.fst, entry.1, post.map Prod.fst ++ [rightmost],
            by simp, ?_, ?_, by simp [found]⟩
          · intro child childMem childRows childDecoded candidate rowMem
            rcases List.mem_map.mp childMem with ⟨earlier, earlierMem, earlierEq⟩
            rw [← earlierEq] at childDecoded
            have le := bounded earlier (List.mem_append_left _ earlierMem) childRows
              childDecoded candidate rowMem
            have missed := preFails earlier earlierMem
            simp at missed
            refine value_lt_of_treeKey_lt ?_
            rw [keyIsRow]
            omega
          · intro child childMem childRows childDecoded candidate rowMem
            have memAlt : child ∈ rightmost :: post.map Prod.fst := by
              rcases List.mem_append.mp childMem with inPost | isRightmost
              · exact List.mem_cons_of_mem _ inPost
              · simp at isRightmost
                simp [isRightmost]
            have gt := above pre entry post rfl child memAlt childRows childDecoded
              candidate rowMem
            refine value_lt_of_treeKey_lt ?_
            rw [keyIsRow]
            omega
    have chosenMemChildren : chosen ∈ entries.map Prod.fst ++ [rightmost] := by
      rw [split]; simp
    have chosenSound : TreeSound schema source fuel chosen := by
      refine soundChildren chosen ?_
      rcases List.mem_append.mp chosenMemChildren with inEntries | isRightmost
      · exact List.mem_cons_of_mem _ inEntries
      · simp at isRightmost
        simp [isRightmost]
    rw [split] at childrenResult decoded
    cases nestedResult :
        (preChildren ++ chosen :: postChildren).mapM (subtreePages source fuel) with
    | none =>
        simp only [subtreePages, pageResult, childrenResult, nestedResult] at enumerated
        exact absurd enumerated (by simp)
    | some nested =>
    rcases foldlM_split _ preChildren (chosen :: postChildren) rows decoded with
      ⟨preRows, tailRows, preFold, tailFold, shape₁⟩
    rcases foldlM_split _ [chosen] postChildren tailRows (by simpa using tailFold) with
      ⟨chosenRows, postRows, chosenFold, postFold, shape₂⟩
    have chosenDecoded :
        CoreDecode.decodeSubtreeRowsFrom schema source fuel chosen
          = some chosenRows := by simpa using chosenFold
    have locatedChosen : locateLeaf? source key fuel chosen = some leafPage := by
      rw [chosenEq]; exact located
    rcases mapM_subtreePages_mem nestedResult chosen (by simp) with
      ⟨chosenList, chosenEnum, _⟩
    have targetMem : leafPage ∈ chosenList :=
      locateLeaf_mem_subtreePages source key fuel chosen chosenList leafPage
        chosenEnum locatedChosen
    -- Siblings cannot see the written page, so their rows are unchanged.
    have siblingSame : ∀ child ∈ preChildren ++ postChildren,
        CoreDecode.decodeSubtreeRowsFrom schema source fuel child
          = CoreDecode.decodeSubtreeRowsFrom schema new fuel child := by
      intro child childMem
      have childMem' : child ∈ preChildren ++ chosen :: postChildren := by
        rcases List.mem_append.mp childMem with inPre | inPost
        · exact List.mem_append_left _ inPre
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ inPost)
      rcases mapM_subtreePages_mem nestedResult child childMem' with
        ⟨childList, childEnum, _⟩
      refine decodeSubtreeRowsFrom_congr schema source new leafAgrees childEnum ?_
      intro p pMem
      refine offTarget p ?_
      intro same
      exact (siblingsDisjoint preChildren chosen postChildren split child childMem
        childList chosenList childEnum chosenEnum leafPage targetMem) (same ▸ pMem)
    have preNew : preChildren.foldlM
        (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema new fuel x).bind
          (fun r => some (a ++ r))) ([] : List Core.Row) = some preRows := by
      rw [← preFold]
      exact foldlM_congr fun _ child member => by
        rw [siblingSame child (List.mem_append_left _ member)]
    have postNew : postChildren.foldlM
        (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema new fuel x).bind
          (fun r => some (a ++ r))) ([] : List Core.Row) = some postRows := by
      rw [← postFold]
      exact foldlM_congr fun _ child member => by
        rw [siblingSame child (List.mem_append_right _ member)]
    have chosenNew : CoreDecode.decodeSubtreeRowsFrom schema new fuel chosen
        = some (Core.orderedUpsert row chosenRows) :=
      induction chosen chosenRows chosenList chosenSound
        (disjointChildren chosen chosenMemChildren) chosenEnum chosenDecoded
        locatedChosen
    have wholeNew : (preChildren ++ ([chosen] ++ postChildren)).foldlM
        (fun a x => (CoreDecode.decodeSubtreeRowsFrom schema new fuel x).bind
          (fun r => some (a ++ r))) ([] : List Core.Row)
        = some (preRows ++ (Core.orderedUpsert row chosenRows ++ postRows)) :=
      foldlM_join _ preChildren _ _ _ preNew
        (foldlM_join _ [chosen] postChildren _ _ (by simpa using chosenNew) postNew)
    have preRowsBelow : ∀ earlier ∈ preRows, earlier.rowid.value < row.rowid.value :=
      foldRows_bound schema source fuel _ preChildren preRows preBelow preFold
    have postRowsAbove : ∀ later ∈ postRows, row.rowid.value < later.rowid.value :=
      foldRows_bound schema source fuel _ postChildren postRows postAbove postFold
    have rowsShape : rows = preRows ++ chosenRows ++ postRows := by
      rw [shape₁, shape₂]; simp
    rw [CoreDecode.decodeSubtreeRowsFrom, newPage]
    simp only [some_bind', childrenResult]
    rw [rowsShape,
      orderedUpsert_routedSplit row preRows chosenRows postRows preRowsBelow
        postRowsAbove]
    simpa using wholeNew

/-- The ordered insert introduces no row other than the one being inserted. -/
theorem mem_orderedUpsert (row : Core.Row) :
    ∀ (rows : List Core.Row) (candidate : Core.Row),
      candidate ∈ Core.orderedUpsert row rows → candidate = row ∨ candidate ∈ rows
  | [], candidate, member => by
      simp only [Core.orderedUpsert, List.mem_singleton] at member
      exact Or.inl member
  | existing :: rows, candidate, member => by
      rw [Core.orderedUpsert] at member
      split at member
      · rcases List.mem_cons.mp member with isRow | rest
        · exact Or.inl isRow
        · exact Or.inr rest
      · split at member
        · rcases List.mem_cons.mp member with isExisting | rest
          · exact Or.inr (isExisting ▸ List.mem_cons_self)
          · rcases mem_orderedUpsert row rows candidate rest with isRow | inRows
            · exact Or.inl isRow
            · exact Or.inr (List.mem_cons_of_mem _ inRows)
        · rcases List.mem_cons.mp member with isRow | rest
          · exact Or.inl isRow
          · exact Or.inr (List.mem_cons_of_mem _ rest)

end CoreLazyWrite

end SQLeanite
