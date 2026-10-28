import SQLeanite.WidePageTree.LeafCapacity

namespace SQLeanite
namespace WidePageTree

theorem numberedBranches_root_ne_pendingBytePage (startPage : Nat)
    (nodes : List (Node Value))
    (node : Node Value) (member : node ∈ numberedBranches startPage nodes) :
    node.rootId ≠ pendingBytePage := by
  unfold numberedBranches at member
  rw [List.mem_mapIdx] at member
  rcases member with ⟨offset, bound, equal⟩
  rw [← equal]
  exact allocatedPage_ne_pendingBytePage startPage offset

/-- Build successive numbered interior layers.  The initial node count is a
simple totality fuel; every recursive layer has strictly fewer nodes when it
contains at least two. -/
def buildNumberedFrom : Nat → Nat → List (Node Value) →
    Option (Node Value × Nat)
  | 0, nextPage, [root] => some (root, nextPage)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | _ + 1, nextPage, [root] => some (root, nextPage)
  | fuel + 1, nextPage, first :: second :: nodes =>
      let next := numberedBranches nextPage (first :: second :: nodes)
      buildNumberedFrom fuel (allocatedPage nextPage next.length) next

def buildNumbered (startPage : Nat)
    (entries : List (PagedBTree.Entry Value)) : Option (Node Value × Nat) :=
  let leaves := if entries.isEmpty then
      [.leaf (allocatedPage startPage 0) []]
    else numberedLeaves startPage entries
  buildNumberedFrom leaves.length (allocatedPage startPage leaves.length) leaves

theorem buildNumberedFrom_toList :
    ∀ (fuel nextPage : Nat) (nodes : List (Node Value))
      (root : Node Value) (after : Nat),
      buildNumberedFrom fuel nextPage nodes = some (root, after) →
      root.toList = nodes.flatMap Node.toList
  | 0, _, [], _, _, built => by simp [buildNumberedFrom] at built
  | 0, _, [root], result, after, built => by
      simp only [buildNumberedFrom, Option.some.injEq, Prod.mk.injEq] at built
      rcases built with ⟨rfl, rfl⟩
      simp
  | 0, _, first :: second :: nodes, _, _, built => by
      simp [buildNumberedFrom] at built
  | fuel + 1, _, [], _, _, built => by simp [buildNumberedFrom] at built
  | fuel + 1, _, [root], result, after, built => by
      simp only [buildNumberedFrom, Option.some.injEq, Prod.mk.injEq] at built
      rcases built with ⟨rfl, rfl⟩
      simp
  | fuel + 1, nextPage, first :: second :: nodes, root, after, built => by
      let next := numberedBranches nextPage (first :: second :: nodes)
      have recursive := buildNumberedFrom_toList fuel
        (allocatedPage nextPage next.length) next root after (by
          simpa [buildNumberedFrom, next] using built)
      rw [recursive, numberedBranches_toList]

theorem buildNumberedFrom_after_ge :
    ∀ (fuel nextPage : Nat) (nodes : List (Node Value))
      (root : Node Value) (after : Nat),
      buildNumberedFrom fuel nextPage nodes = some (root, after) →
      nextPage ≤ after
  | 0, _, [], _, _, built => by simp [buildNumberedFrom] at built
  | 0, nextPage, [root], result, after, built => by
      simp only [buildNumberedFrom, Option.some.injEq, Prod.mk.injEq] at built
      omega
  | 0, _, first :: second :: nodes, _, _, built => by
      simp [buildNumberedFrom] at built
  | fuel + 1, _, [], _, _, built => by simp [buildNumberedFrom] at built
  | fuel + 1, nextPage, [root], result, after, built => by
      simp only [buildNumberedFrom, Option.some.injEq, Prod.mk.injEq] at built
      omega
  | fuel + 1, nextPage, first :: second :: nodes, root, after, built => by
      let next := numberedBranches nextPage (first :: second :: nodes)
      have recursive := buildNumberedFrom_after_ge fuel
        (allocatedPage nextPage next.length) next root after (by
          simpa [buildNumberedFrom, next] using built)
      exact Nat.le_trans (allocatedPage_ge nextPage next.length) recursive

theorem buildNumbered_toList {startPage : Nat}
    {entries : List (PagedBTree.Entry Value)} {root : Node Value} {after : Nat}
    (built : buildNumbered startPage entries = some (root, after)) :
    root.toList = entries := by
  unfold buildNumbered at built
  split at built
  next empty =>
    have entriesEmpty : entries = [] := List.isEmpty_iff.mp empty
    simpa [entriesEmpty, Node.toList] using
      buildNumberedFrom_toList 1 (allocatedPage startPage 1)
        [.leaf (allocatedPage startPage 0) []] root after built
  next notEmpty =>
    rw [buildNumberedFrom_toList
      (numberedLeaves startPage entries).length
      (allocatedPage startPage (numberedLeaves startPage entries).length)
      (numberedLeaves startPage entries) root after built,
      numberedLeaves_toList]

theorem buildNumbered_after_ge {startPage : Nat}
    {entries : List (PagedBTree.Entry Value)} {root : Node Value} {after : Nat}
    (built : buildNumbered startPage entries = some (root, after)) :
    startPage ≤ after := by
  unfold buildNumbered at built
  split at built
  next =>
    have bound := buildNumberedFrom_after_ge 1 (allocatedPage startPage 1)
      [.leaf (allocatedPage startPage 0) []] root after built
    exact Nat.le_trans (allocatedPage_ge startPage 1) bound
  next =>
    have bound := buildNumberedFrom_after_ge
      (numberedLeaves startPage entries).length
      (allocatedPage startPage (numberedLeaves startPage entries).length)
      (numberedLeaves startPage entries) root after built
    exact Nat.le_trans
      (allocatedPage_ge startPage (numberedLeaves startPage entries).length)
      bound

def numberedBranchesWithFanout (fanout startPage : Nat)
    (nodes : List (Node Value)) : List (Node Value) :=
  (groups fanout nodes).mapIdx fun offset children =>
    .branch (allocatedPage startPage offset) children

theorem numberedBranchesWithFanout_toList (fanout startPage : Nat)
    (nodes : List (Node Value)) :
    (numberedBranchesWithFanout fanout startPage nodes).flatMap Node.toList =
      nodes.flatMap Node.toList := by
  unfold numberedBranchesWithFanout
  rw [List.mapIdx_eq_zipIdx_map, List.flatMap_map]
  simp only [Function.comp_apply, Node.toList]
  have zipped : (groups fanout nodes).zipIdx.flatMap Prod.fst =
      (groups fanout nodes).flatten := by
    change ((groups fanout nodes).zipIdx.map Prod.fst).flatten = _
    rw [List.zipIdx_map_fst]
  rw [← List.flatMap_assoc, zipped, flatten_groups]

def buildNumberedFromWithFanout (fanout : Nat) :
    Nat → Nat → List (Node Value) → Option (Node Value × Nat)
  | 0, nextPage, [root] => some (root, nextPage)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | _ + 1, nextPage, [root] => some (root, nextPage)
  | fuel + 1, nextPage, first :: second :: nodes =>
      let next := numberedBranchesWithFanout fanout nextPage
        (first :: second :: nodes)
      buildNumberedFromWithFanout fanout fuel
        (allocatedPage nextPage next.length) next

def buildNumberedWithFanout (fanout startPage : Nat)
    (entries : List (PagedBTree.Entry Value)) : Option (Node Value × Nat) :=
  let leaves := if entries.isEmpty then
      [.leaf (allocatedPage startPage 0) []]
    else numberedLeaves startPage entries
  buildNumberedFromWithFanout fanout leaves.length
    (allocatedPage startPage leaves.length) leaves

theorem buildNumberedFromWithFanout_toList (fanout : Nat) :
    ∀ (fuel nextPage : Nat) (nodes : List (Node Value))
      (root : Node Value) (after : Nat),
      buildNumberedFromWithFanout fanout fuel nextPage nodes =
          some (root, after) →
      root.toList = nodes.flatMap Node.toList
  | 0, _, [], _, _, built => by
      simp [buildNumberedFromWithFanout] at built
  | 0, _, [root], result, after, built => by
      simp only [buildNumberedFromWithFanout, Option.some.injEq,
        Prod.mk.injEq] at built
      rcases built with ⟨rfl, rfl⟩
      simp
  | 0, _, first :: second :: nodes, _, _, built => by
      simp [buildNumberedFromWithFanout] at built
  | fuel + 1, _, [], _, _, built => by
      simp [buildNumberedFromWithFanout] at built
  | fuel + 1, _, [root], result, after, built => by
      simp only [buildNumberedFromWithFanout, Option.some.injEq,
        Prod.mk.injEq] at built
      rcases built with ⟨rfl, rfl⟩
      simp
  | fuel + 1, nextPage, first :: second :: nodes, root, after, built => by
      let next := numberedBranchesWithFanout fanout nextPage
        (first :: second :: nodes)
      have recursive := buildNumberedFromWithFanout_toList fanout fuel
        (allocatedPage nextPage next.length) next root after (by
          simpa [buildNumberedFromWithFanout, next] using built)
      rw [recursive, numberedBranchesWithFanout_toList]

theorem buildNumberedFromWithFanout_after_ge (fanout : Nat) :
    ∀ (fuel nextPage : Nat) (nodes : List (Node Value))
      (root : Node Value) (after : Nat),
      buildNumberedFromWithFanout fanout fuel nextPage nodes =
          some (root, after) →
      nextPage ≤ after
  | 0, _, [], _, _, built => by
      simp [buildNumberedFromWithFanout] at built
  | 0, nextPage, [root], result, after, built => by
      simp only [buildNumberedFromWithFanout, Option.some.injEq,
        Prod.mk.injEq] at built
      omega
  | 0, _, first :: second :: nodes, _, _, built => by
      simp [buildNumberedFromWithFanout] at built
  | fuel + 1, _, [], _, _, built => by
      simp [buildNumberedFromWithFanout] at built
  | fuel + 1, nextPage, [root], result, after, built => by
      simp only [buildNumberedFromWithFanout, Option.some.injEq,
        Prod.mk.injEq] at built
      omega
  | fuel + 1, nextPage, first :: second :: nodes, root, after, built => by
      let next := numberedBranchesWithFanout fanout nextPage
        (first :: second :: nodes)
      have recursive := buildNumberedFromWithFanout_after_ge fanout fuel
        (allocatedPage nextPage next.length) next root after (by
          simpa [buildNumberedFromWithFanout, next] using built)
      exact Nat.le_trans (allocatedPage_ge nextPage next.length) recursive

theorem buildNumberedWithFanout_toList {fanout startPage : Nat}
    {entries : List (PagedBTree.Entry Value)} {root : Node Value} {after : Nat}
    (built : buildNumberedWithFanout fanout startPage entries =
      some (root, after)) : root.toList = entries := by
  unfold buildNumberedWithFanout at built
  split at built
  next empty =>
    have entriesEmpty : entries = [] := List.isEmpty_iff.mp empty
    simpa [entriesEmpty, Node.toList] using
      buildNumberedFromWithFanout_toList fanout 1
        (allocatedPage startPage 1)
        [.leaf (allocatedPage startPage 0) []] root after built
  next =>
    rw [buildNumberedFromWithFanout_toList fanout
      (numberedLeaves startPage entries).length
      (allocatedPage startPage (numberedLeaves startPage entries).length)
      (numberedLeaves startPage entries) root after built,
      numberedLeaves_toList]

theorem buildNumberedWithFanout_after_ge {fanout startPage : Nat}
    {entries : List (PagedBTree.Entry Value)} {root : Node Value} {after : Nat}
    (built : buildNumberedWithFanout fanout startPage entries =
      some (root, after)) : startPage ≤ after := by
  unfold buildNumberedWithFanout at built
  split at built
  next =>
    have bound := buildNumberedFromWithFanout_after_ge fanout 1
      (allocatedPage startPage 1)
      [.leaf (allocatedPage startPage 0) []] root after built
    exact Nat.le_trans (allocatedPage_ge startPage 1) bound
  next =>
    have bound := buildNumberedFromWithFanout_after_ge fanout
      (numberedLeaves startPage entries).length
      (allocatedPage startPage (numberedLeaves startPage entries).length)
      (numberedLeaves startPage entries) root after built
    exact Nat.le_trans
      (allocatedPage_ge startPage (numberedLeaves startPage entries).length)
      bound

/-- The live owner of a wide physical topology.  `represents` is erased by the
compiler; it prevents callers from attaching the page graph to a different
logical sequence. -/
structure Store (Value : Type) where
  root : Node Value
  nextPage : Nat
  represents : root.toList.Pairwise (fun left right => left.1 < right.1)

def Store.toList (store : Store Value) := store.root.toList

def Store.build? (startPage : Nat)
    (entries : List (PagedBTree.Entry Value))
    (ordered : entries.Pairwise (fun left right => left.1 < right.1)) :
    Option (Store Value) :=
  match numbered : buildNumbered startPage entries with
  | none => none
  | some (root, nextPage) => some {
      root
      nextPage
      represents := by
        rw [buildNumbered_toList numbered]
        exact ordered }

theorem Store.build?_toList {startPage : Nat}
    {entries : List (PagedBTree.Entry Value)}
    {ordered : entries.Pairwise (fun left right => left.1 < right.1)}
    {store : Store Value}
    (built : Store.build? startPage entries ordered = some store) :
    store.toList = entries := by
  unfold Store.build? at built
  split at built
  next => contradiction
  next root nextPage numbered =>
    injection built with equal
    change store.root.toList = entries
    rw [← congrArg Store.root equal]
    exact buildNumbered_toList numbered

theorem Store.build?_nextPage_ge {startPage : Nat}
    {entries : List (PagedBTree.Entry Value)}
    {ordered : entries.Pairwise (fun left right => left.1 < right.1)}
    {store : Store Value}
    (built : Store.build? startPage entries ordered = some store) :
    startPage ≤ store.nextPage := by
  unfold Store.build? at built
  split at built
  next => contradiction
  next root nextPage numbered =>
    injection built with equal
    rw [← congrArg Store.nextPage equal]
    exact buildNumbered_after_ge numbered

def KeysAdjacent : List (PagedBTree.Entry Value) → Prop
  | [] | [_] => True
  | first :: second :: entries =>
      first.1 < second.1 ∧ KeysAdjacent (second :: entries)

def decideKeysAdjacent :
    (entries : List (PagedBTree.Entry Value)) → Decidable (KeysAdjacent entries)
  | [] | [_] => isTrue trivial
  | first :: second :: entries =>
      let head : Decidable (first.1 < second.1) := inferInstance
      let tail := decideKeysAdjacent (second :: entries)
      @instDecidableAnd (first.1 < second.1)
        (KeysAdjacent (second :: entries)) head tail
termination_by entries => entries.length

instance (entries : List (PagedBTree.Entry Value)) :
    Decidable (KeysAdjacent entries) := decideKeysAdjacent entries

theorem keysAdjacent_iff_pairwise : ∀ (entries : List
    (PagedBTree.Entry Value)),
    KeysAdjacent entries ↔
      entries.Pairwise (fun left right => left.1 < right.1)
  | [] => by simp [KeysAdjacent]
  | [entry] => by simp [KeysAdjacent]
  | first :: second :: entries => by
      simp only [KeysAdjacent]
      rw [List.pairwise_cons, keysAdjacent_iff_pairwise (second :: entries)]
      constructor
      · intro adjacent
        refine ⟨?_, adjacent.2⟩
        intro candidate member
        simp only [List.mem_cons] at member
        rcases member with equal | later
        · simpa [equal] using adjacent.1
        · have secondBefore := (List.pairwise_cons.mp adjacent.2).1
            candidate later
          exact Nat.lt_trans adjacent.1 secondBefore
      · intro pairwise
        exact ⟨pairwise.1 second (by simp), pairwise.2⟩

def decideKeysPairwise
    (entries : List (PagedBTree.Entry Value)) :
    Decidable (entries.Pairwise (fun left right => left.1 < right.1)) :=
  decidable_of_iff (KeysAdjacent entries) (keysAdjacent_iff_pairwise entries)

def splitLast? (values : List α) : Option (List α × α) :=
  match values.reverse with
  | [] => none
  | last :: reversed => some (reversed.reverse, last)

theorem splitLast?_reconstruct {values initial : List α} {last : α}
    (success : splitLast? values = some (initial, last)) :
    initial ++ [last] = values := by
  unfold splitLast? at success
  cases reversed : values.reverse with
  | nil => simp [reversed] at success
  | cons final tail =>
      simp only [reversed, Option.some.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      have restored := congrArg List.reverse reversed
      simpa using restored.symm

inductive AppendResult (Value : Type) where
  | done (node : Node Value)
  | split (left right : Node Value)

def AppendResult.nodes : AppendResult Value → List (Node Value)
  | .done node => [node]
  | .split left right => [left, right]

def AppendResult.toList (result : AppendResult Value) :
    List (PagedBTree.Entry Value) :=
  result.nodes.flatMap Node.toList

def AppendResult.firstRootId? : AppendResult Value → Option Nat
  | .done node => some node.rootId
  | .split left _ => some left.rootId

def Node.setRootId (pageId : Nat) : Node Value → Node Value
  | .leaf _ entries => .leaf pageId entries
  | .branch _ children => .branch pageId children

@[simp] theorem Node.toList_setRootId (node : Node Value) (pageId : Nat) :
    (node.setRootId pageId).toList = node.toList := by
  cases node <;> simp [Node.setRootId, Node.toList]

@[simp] theorem Node.rootId_setRootId (node : Node Value) (pageId : Nat) :
    (node.setRootId pageId).rootId = pageId := by
  cases node <;> simp [Node.setRootId, Node.rootId]

/-- Fuel is the remaining physical height.  It makes malformed cyclic input
unrepresentable at the API boundary and keeps the executable total. -/
def appendStep : Nat → Nat → PagedBTree.Entry Value → Node Value →
    Option (AppendResult Value × Nat)
  | 0, _, _, _ => none
  | _ + 1, nextPage, entry, .leaf pageId entries =>
      let updated := entries ++ [entry]
      if _fits : updated.length ≤ leafCapacity then
        some (.done (.leaf pageId updated), nextPage)
      else if _full : entries.length = leafCapacity then
        some (.split (.leaf pageId entries)
          (.leaf (allocatedPage nextPage 0) [entry]),
          allocatedPage nextPage 1)
      else none
  | fuel + 1, nextPage, entry, .branch pageId children => do
      let (initial, last) ← splitLast? children
      let (childResult, afterChild) ← appendStep fuel nextPage entry last
      let updated := initial ++ childResult.nodes
      if _fits : updated.length ≤ interiorFanout then
        some (.done (.branch pageId updated), afterChild)
      else if _full : children.length = interiorFanout then
        let splitAt := updated.length / 2
        some (.split (.branch pageId (updated.take splitAt))
          (.branch (allocatedPage afterChild 0) (updated.drop splitAt)),
            allocatedPage afterChild 1)
      else none

end WidePageTree

end SQLeanite
