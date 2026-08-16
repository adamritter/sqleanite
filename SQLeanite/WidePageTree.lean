import SQLeanite.PagedBTree
import SQLeanite.PhysicalCodec

namespace SQLeanite
namespace WidePageTree

/-!
# High-fanout physical page topology

The logical ordered-map development uses a 2-3 tree because its branching
proofs are compact.  A physical SQLite interior page must not inherit that
branching factor: a 4096-byte page can hold hundreds of four-byte child
pointers and nine-byte worst-case integer separators.  Materializing each
logical 2-3 node as one disk page made roughly half of every database consist
of almost-empty interior pages.

This module is the replacement physical topology.  Leaves contain at most two
already byte-budgeted chunks, while an interior node contains up to 256
children.  The builder is total, preserves the exact entry sequence at every
level, and exposes the bounds needed by the SQLite page encoder.  Stable page
identity and localized mutation are layered on this plan in the subsequent
migration step; there is deliberately no second byte encoder here.
-/

def leafCapacity : Nat := 2

/-- With at most 255 interior cells, the 12-byte page header, two-byte pointer
for each cell, four-byte child page number, and nine-byte worst-case separator
fit in a 4096-byte SQLite page. -/
def interiorFanout : Nat := 256

theorem leafCapacity_pos : 0 < leafCapacity := by decide

theorem interiorFanout_pos : 0 < interiorFanout := by decide

theorem interiorFanout_pageFit :
    12 + (interiorFanout - 1) * (2 + 4 + 9) ≤ PhysicalCodec.pageSize := by
  decide

/-- Proof-facing fixed-capacity grouping. -/
def groups : Nat → List α → List (List α)
  | 0, values => if values.isEmpty then [] else [values]
  | _ + 1, [] => []
  | capacity + 1, value :: values =>
      let input := value :: values
      input.take (capacity + 1) :: groups (capacity + 1)
        (input.drop (capacity + 1))
  termination_by _ values => values.length
  decreasing_by
    simp only [input, List.length_drop, List.length_cons]
    omega

theorem flatten_groups (capacity : Nat) (values : List α) :
    (groups capacity values).flatten = values := by
  induction capacity, values using groups.induct with
  | case1 values =>
      simp only [groups]
      split <;> simp_all
  | case2 values empty => simp [groups, empty]
  | case3 capacity => simp [groups]
  | case4 capacity value values input induction =>
      simp only [groups, List.flatten_cons]
      rw [induction, List.take_append_drop]

/-- Tail-recursive grouping used by compiled bulk construction. -/
def groupsGo : Nat → List α → List (List α) → List (List α)
  | 0, values, reversed =>
      if values.isEmpty then reversed.reverse
      else reversed.reverseAux [values]
  | _ + 1, [], reversed => reversed.reverse
  | capacity + 1, value :: values, reversed =>
      let input := value :: values
      groupsGo (capacity + 1) (input.drop (capacity + 1))
        (input.take (capacity + 1) :: reversed)
  termination_by _ values _ => values.length
  decreasing_by
    simp only [input, List.length_drop, List.length_cons]
    omega

def groupsTR (capacity : Nat) (values : List α) : List (List α) :=
  groupsGo capacity values []

theorem groupsGo_eq (capacity : Nat) (values : List α)
    (reversed : List (List α)) :
    groupsGo capacity values reversed =
      reversed.reverse ++ groups capacity values := by
  induction capacity, values using groups.induct generalizing reversed with
  | case1 values =>
      simp only [groupsGo, groups]
      split
      · simp_all
      · simp [List.reverseAux_eq]
  | case2 values empty => simp [groupsGo, groups, empty]
  | case3 capacity => simp [groupsGo, groups]
  | case4 capacity value values input induction =>
      simp only [groupsGo, groups]
      rw [induction]
      simp [input]

@[csimp] theorem groups_eq_groupsTR : @groups = @groupsTR := by
  funext α capacity values
  rw [groupsTR, groupsGo_eq]
  simp

theorem groups_member_nonempty :
    ∀ (capacity : Nat) (values group : List α), 0 < capacity →
      group ∈ groups capacity values → group ≠ [] := by
  intro capacity values
  induction capacity, values using groups.induct with
  | case1 values => omega
  | case2 values empty => simp [groups, empty]
  | case3 capacity => simp [groups]
  | case4 capacity value values input induction =>
      intro group positive member
      simp only [groups, List.mem_cons] at member
      rcases member with equal | tail
      · subst group
        simp [input]
      · exact induction group positive tail

theorem groups_member_length_le :
    ∀ (capacity : Nat) (values group : List α), 0 < capacity →
      group ∈ groups capacity values → group.length ≤ capacity := by
  intro capacity values
  induction capacity, values using groups.induct with
  | case1 values => omega
  | case2 values empty => simp [groups, empty]
  | case3 capacity => simp [groups]
  | case4 capacity value values input induction =>
      intro group positive member
      simp only [groups, List.mem_cons] at member
      rcases member with equal | tail
      · subst group
        simp [input]
        omega
      · exact induction group positive tail

/-- An unnumbered physical page tree.  A `branch` is one SQLite interior page,
not a logical 2-3 node. -/
inductive Plan (Value : Type) where
  | leaf (entries : List (PagedBTree.Entry Value))
  | branch (children : List (Plan Value))
  deriving Repr

def Plan.toList : Plan Value → List (PagedBTree.Entry Value)
  | .leaf entries => entries
  | .branch children => children.flatMap Plan.toList

def Plan.pageCount : Plan Value → Nat
  | .leaf _ => 1
  | .branch children => 1 + (children.map Plan.pageCount).sum

def Plan.leafCount : Plan Value → Nat
  | .leaf _ => 1
  | .branch children => (children.map Plan.leafCount).sum

def Plan.interiorCount : Plan Value → Nat
  | .leaf _ => 0
  | .branch children => 1 + (children.map Plan.interiorCount).sum

def Plan.height : Plan Value → Nat
  | .leaf _ => 0
  | .branch [] => 1
  | .branch (child :: _) => child.height + 1

def Plan.BranchingBound : Plan Value → Prop
  | .leaf entries => entries.length ≤ leafCapacity
  | .branch children =>
      children ≠ [] ∧ children.length ≤ interiorFanout ∧
        ∀ child ∈ children, child.BranchingBound

def Plan.Balanced : Plan Value → Prop
  | .leaf _ => True
  | .branch children => children ≠ [] ∧
      ∃ height, ∀ child ∈ children,
        child.Balanced ∧ child.height = height

def leafLayer (entries : List (PagedBTree.Entry Value)) : List (Plan Value) :=
  if entries.isEmpty then [.leaf []]
  else (groups leafCapacity entries).map Plan.leaf

theorem leafLayer_toList (entries : List (PagedBTree.Entry Value)) :
    (leafLayer entries).flatMap Plan.toList = entries := by
  unfold leafLayer
  split
  next empty =>
    have : entries = [] := List.isEmpty_iff.mp empty
    simp [this, Plan.toList]
  next =>
    simp only [List.flatMap_map, Function.comp_def, Plan.toList]
    simpa only [List.flatMap_id'] using flatten_groups leafCapacity entries

def LayerAt (height : Nat) (nodes : List (Plan Value)) : Prop :=
  ∀ node ∈ nodes,
    node.Balanced ∧ node.height = height ∧ node.BranchingBound

theorem leafLayer_layer (entries : List (PagedBTree.Entry Value)) :
    LayerAt 0 (leafLayer entries) := by
  intro node member
  unfold leafLayer at member
  split at member
  next =>
    simp only [List.mem_singleton] at member
    subst node
    exact ⟨by simp [Plan.Balanced], rfl,
      by simp [Plan.BranchingBound, leafCapacity]⟩
  next notEmpty =>
    rcases List.mem_map.mp member with ⟨page, pageMember, rfl⟩
    refine ⟨by simp [Plan.Balanced], rfl, ?_⟩
    unfold Plan.BranchingBound
    exact groups_member_length_le leafCapacity entries page
      leafCapacity_pos pageMember

def combineLevel (nodes : List (Plan Value)) : List (Plan Value) :=
  (groups interiorFanout nodes).map Plan.branch

theorem combineLevel_toList (nodes : List (Plan Value)) :
    (combineLevel nodes).flatMap Plan.toList = nodes.flatMap Plan.toList := by
  unfold combineLevel
  simp only [List.flatMap_map, Function.comp_def, Plan.toList]
  rw [← List.flatMap_assoc]
  simp [flatten_groups]

theorem combineLevel_layer {height : Nat} {nodes : List (Plan Value)}
    (layer : LayerAt height nodes) :
    LayerAt (height + 1) (combineLevel nodes) := by
  intro node member
  unfold combineLevel at member
  rcases List.mem_map.mp member with ⟨children, childrenMember, rfl⟩
  have nonempty := groups_member_nonempty interiorFanout nodes children
    interiorFanout_pos childrenMember
  have bounded := groups_member_length_le interiorFanout nodes children
    interiorFanout_pos childrenMember
  have childSource : ∀ child ∈ children, child ∈ nodes := by
    intro child childMember
    rw [← flatten_groups interiorFanout nodes]
    exact List.mem_flatten.mpr ⟨children, childrenMember, childMember⟩
  have childLayer : ∀ child ∈ children,
      child.Balanced ∧ child.height = height ∧ child.BranchingBound := by
    intro child childMember
    exact layer child (childSource child childMember)
  rcases List.exists_cons_of_ne_nil nonempty with ⟨first, rest, equal⟩
  subst children
  refine ⟨?_, ?_, ?_⟩
  · simp only [Plan.Balanced]
    refine ⟨by simp, ⟨height, ?_⟩⟩
    intro child childMember
    exact ⟨(childLayer child childMember).1,
      (childLayer child childMember).2.1⟩
  · simp only [Plan.height]
    rw [(childLayer first (by simp)).2.1]
  · simp only [Plan.BranchingBound]
    refine ⟨by simp, bounded, ?_⟩
    intro child childMember
    exact (childLayer child childMember).2.2

/-- Repeatedly combine one physical level.  The initial node count is enough
fuel because every non-root layer has at least two nodes and fanout is at least
two.  Fuel keeps totality independent of that arithmetic fact. -/
def buildFromNodes : Nat → List (Plan Value) → Option (Plan Value)
  | 0, [root] => some root
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [root] => some root
  | fuel + 1, first :: second :: nodes =>
      buildFromNodes fuel (combineLevel (first :: second :: nodes))

def build (entries : List (PagedBTree.Entry Value)) : Option (Plan Value) :=
  let leaves := leafLayer entries
  buildFromNodes leaves.length leaves

theorem buildFromNodes_toList : ∀ (fuel : Nat) (nodes : List (Plan Value))
    (plan : Plan Value), buildFromNodes fuel nodes = some plan →
      plan.toList = nodes.flatMap Plan.toList
  | 0, [], _, built => by simp [buildFromNodes] at built
  | 0, [root], plan, built => by
      simp only [buildFromNodes, Option.some.injEq] at built
      subst plan
      simp
  | 0, first :: second :: nodes, _, built => by
      simp [buildFromNodes] at built
  | fuel + 1, [], _, built => by simp [buildFromNodes] at built
  | fuel + 1, [root], plan, built => by
      simp only [buildFromNodes, Option.some.injEq] at built
      subst plan
      simp
  | fuel + 1, first :: second :: nodes, plan, built => by
      have recursive := buildFromNodes_toList fuel
        (combineLevel (first :: second :: nodes)) plan (by
          simpa [buildFromNodes] using built)
      rw [recursive, combineLevel_toList]

theorem buildFromNodes_valid : ∀ (fuel : Nat) (nodes : List (Plan Value))
    (plan : Plan Value), (∃ height, LayerAt height nodes) →
      buildFromNodes fuel nodes = some plan →
      plan.Balanced ∧ plan.BranchingBound
  | 0, [], _, _, built => by simp [buildFromNodes] at built
  | 0, [root], plan, layer, built => by
      simp only [buildFromNodes, Option.some.injEq] at built
      subst plan
      rcases layer with ⟨height, layer⟩
      have rootLayer := layer root (by simp)
      exact ⟨rootLayer.1, rootLayer.2.2⟩
  | 0, first :: second :: nodes, _, _, built => by
      simp [buildFromNodes] at built
  | fuel + 1, [], _, _, built => by simp [buildFromNodes] at built
  | fuel + 1, [root], plan, layer, built => by
      simp only [buildFromNodes, Option.some.injEq] at built
      subst plan
      rcases layer with ⟨height, layer⟩
      have rootLayer := layer root (by simp)
      exact ⟨rootLayer.1, rootLayer.2.2⟩
  | fuel + 1, first :: second :: nodes, plan, layer, built => by
      rcases layer with ⟨height, layer⟩
      apply buildFromNodes_valid fuel
        (combineLevel (first :: second :: nodes)) plan
        ⟨height + 1, combineLevel_layer layer⟩
      simpa [buildFromNodes] using built

theorem build_toList {entries : List (PagedBTree.Entry Value)}
    {plan : Plan Value} (built : build entries = some plan) :
    plan.toList = entries := by
  unfold build at built
  rw [buildFromNodes_toList (leafLayer entries).length
    (leafLayer entries) plan built, leafLayer_toList]

theorem build_valid {entries : List (PagedBTree.Entry Value)}
    {plan : Plan Value} (built : build entries = some plan) :
    plan.Balanced ∧ plan.BranchingBound := by
  unfold build at built
  exact buildFromNodes_valid (leafLayer entries).length
    (leafLayer entries) plan ⟨0, leafLayer_layer entries⟩ built

/-! ## Stable page identities

`Plan` is the proof-facing bulk topology.  The live store below gives every
page a persistent identity.  Bulk construction allocates leaves first and
then one contiguous interval for each interior layer; consequently the root
is the last allocated page, not an artificial page placed before its
children.  SQLite permits that layout, and later mutations can keep the root
identity fixed without renumbering an unchanged sibling.
-/

inductive Node (Value : Type) where
  | leaf (pageId : Nat) (entries : List (PagedBTree.Entry Value))
  | branch (pageId : Nat) (children : List (Node Value))
  deriving Repr

def Node.rootId : Node Value → Nat
  | .leaf pageId _ | .branch pageId _ => pageId

def Node.toList : Node Value → List (PagedBTree.Entry Value)
  | .leaf _ entries => entries
  | .branch _ children => children.flatMap Node.toList

def Node.pageIds : Node Value → List Nat
  | .leaf pageId _ => [pageId]
  | .branch pageId children =>
      pageId :: children.flatMap Node.pageIds

def Node.pageCount : Node Value → Nat
  | .leaf _ _ => 1
  | .branch _ children => 1 + (children.map Node.pageCount).sum

def Node.leafCount : Node Value → Nat
  | .leaf _ _ => 1
  | .branch _ children => (children.map Node.leafCount).sum

def Node.interiorCount : Node Value → Nat
  | .leaf _ _ => 0
  | .branch _ children => 1 + (children.map Node.interiorCount).sum

def Node.height : Node Value → Nat
  | .leaf _ _ => 0
  | .branch _ [] => 1
  | .branch _ (child :: _) => child.height + 1

def Node.erase : Node Value → Plan Value
  | .leaf _ entries => .leaf entries
  | .branch _ children => .branch (children.map Node.erase)

def numberedLeaves (startPage : Nat)
    (entries : List (PagedBTree.Entry Value)) : List (Node Value) :=
  (groups leafCapacity entries).mapIdx fun offset group =>
    .leaf (startPage + offset) group

theorem numberedLeaves_toList (startPage : Nat)
    (entries : List (PagedBTree.Entry Value)) :
    (numberedLeaves startPage entries).flatMap Node.toList = entries := by
  unfold numberedLeaves
  rw [List.mapIdx_eq_zipIdx_map, List.flatMap_map]
  simp only [Function.comp_apply, Node.toList]
  change ((groups leafCapacity entries).zipIdx.map Prod.fst).flatten = entries
  rw [List.zipIdx_map_fst]
  exact flatten_groups leafCapacity entries

def numberedBranches (startPage : Nat) (nodes : List (Node Value)) :
    List (Node Value) :=
  (groups interiorFanout nodes).mapIdx fun offset children =>
    .branch (startPage + offset) children

theorem numberedBranches_toList (startPage : Nat)
    (nodes : List (Node Value)) :
    (numberedBranches startPage nodes).flatMap Node.toList =
      nodes.flatMap Node.toList := by
  unfold numberedBranches
  rw [List.mapIdx_eq_zipIdx_map, List.flatMap_map]
  simp only [Function.comp_apply, Node.toList]
  have zipped : (groups interiorFanout nodes).zipIdx.flatMap Prod.fst =
      (groups interiorFanout nodes).flatten := by
    change ((groups interiorFanout nodes).zipIdx.map Prod.fst).flatten = _
    rw [List.zipIdx_map_fst]
  rw [← List.flatMap_assoc, zipped]
  rw [flatten_groups]

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
      buildNumberedFrom fuel (nextPage + next.length) next

def buildNumbered (startPage : Nat)
    (entries : List (PagedBTree.Entry Value)) : Option (Node Value × Nat) :=
  let leaves := if entries.isEmpty then [.leaf startPage []]
    else numberedLeaves startPage entries
  buildNumberedFrom leaves.length (startPage + leaves.length) leaves

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
        (nextPage + next.length) next root after (by
          simpa [buildNumberedFrom, next] using built)
      rw [recursive, numberedBranches_toList]

theorem buildNumbered_toList {startPage : Nat}
    {entries : List (PagedBTree.Entry Value)} {root : Node Value} {after : Nat}
    (built : buildNumbered startPage entries = some (root, after)) :
    root.toList = entries := by
  unfold buildNumbered at built
  split at built
  next empty =>
    have entriesEmpty : entries = [] := List.isEmpty_iff.mp empty
    simpa [entriesEmpty, Node.toList] using
      buildNumberedFrom_toList 1 (startPage + 1)
        [.leaf startPage []] root after built
  next notEmpty =>
    rw [buildNumberedFrom_toList
      (numberedLeaves startPage entries).length
      (startPage + (numberedLeaves startPage entries).length)
      (numberedLeaves startPage entries) root after built,
      numberedLeaves_toList]

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

end WidePageTree
end SQLeanite
