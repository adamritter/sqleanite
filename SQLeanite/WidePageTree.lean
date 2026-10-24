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

This module is the replacement physical topology.  Leaves contain one
page-budgeted chunk, while an interior node contains up to 256
children.  The builder is total, preserves the exact entry sequence at every
level, and exposes the bounds needed by the SQLite page encoder.  Stable page
identity and localized mutation are layered on this plan in the subsequent
migration step; there is deliberately no second byte encoder here.
-/

def leafCapacity : Nat := 1

/-- With at most 255 interior cells, the 12-byte page header, two-byte pointer
for each cell, four-byte child page number, and nine-byte worst-case separator
fit in a 4096-byte SQLite page. -/
def interiorFanout : Nat := 256

/-- SQLite page number containing the POSIX pending-byte lock.  The file
format reserves this page even when locking is implemented outside the file;
no B-tree, overflow, pointer-map, or freelist page may own it.  Page numbers
in this module are the one-based numbers stored in SQLite page headers. -/
def pendingBytePage : Nat := 262145

/-- The `offset`th allocatable SQLite page at or after `startPage`.  There is
one architectural hole in the page-number space, `pendingBytePage`.  Keeping
the rule in the topology owner prevents encoders and VFS writers from having
to repair an already-invalid graph. -/
def allocatedPage (startPage offset : Nat) : Nat :=
  let raw := startPage + offset
  if startPage ≤ pendingBytePage ∧ pendingBytePage ≤ raw then raw + 1
  else raw

theorem allocatedPage_ne_pendingBytePage (startPage offset : Nat) :
    allocatedPage startPage offset ≠ pendingBytePage := by
  by_cases skip : startPage ≤ pendingBytePage ∧ pendingBytePage ≤ startPage + offset
  · simp [allocatedPage, skip]
    omega
  · simp [allocatedPage, skip]
    omega

theorem allocatedPage_ge (startPage offset : Nat) :
    startPage ≤ allocatedPage startPage offset := by
  simp only [allocatedPage]
  split <;> omega

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

/-- Greatest entry by right-spine descent.  Physical interior encoding uses
this view instead of flattening every child subtree whenever one separator
page changes. -/
def lastEntryStep : Nat → Node Value → Option (PagedBTree.Entry Value)
  | 0, _ => none
  | _ + 1, .leaf _ entries => entries.getLast?
  | fuel + 1, .branch _ children =>
      match children.reverse with
      | [] => none
      | last :: _ => lastEntryStep fuel last

theorem lastEntryStep_witness {fuel : Nat} {node : Node Value}
    {entry : PagedBTree.Entry Value}
    (success : lastEntryStep fuel node = some entry) :
    node.toList.getLast? = some entry := by
  induction fuel generalizing node with
  | zero => simp [lastEntryStep] at success
  | succ fuel induction =>
      cases node with
      | leaf pageId entries =>
          simpa [lastEntryStep, Node.toList] using success
      | branch pageId children =>
          simp only [lastEntryStep] at success
          cases reversed : children.reverse with
          | nil => simp [reversed] at success
          | cons last initialReversed =>
              simp only [reversed] at success
              have child := induction success
              have restored := congrArg List.reverse reversed
              rw [show children = initialReversed.reverse ++ [last] by
                simpa using restored]
              simp [Node.toList, child]

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

def Node.lastEntry? (node : Node Value) : Option (PagedBTree.Entry Value) :=
  lastEntryStep (node.height + 1) node

theorem Node.lastEntry?_witness {node : Node Value}
    {entry : PagedBTree.Entry Value}
    (success : node.lastEntry? = some entry) :
    node.toList.getLast? = some entry :=
  lastEntryStep_witness success

def Node.erase : Node Value → Plan Value
  | .leaf _ entries => .leaf entries
  | .branch _ children => .branch (children.map Node.erase)

def numberedLeaves (startPage : Nat)
    (entries : List (PagedBTree.Entry Value)) : List (Node Value) :=
  (groups leafCapacity entries).mapIdx fun offset group =>
    .leaf (allocatedPage startPage offset) group

theorem numberedLeaves_toList (startPage : Nat)
    (entries : List (PagedBTree.Entry Value)) :
    (numberedLeaves startPage entries).flatMap Node.toList = entries := by
  unfold numberedLeaves
  rw [List.mapIdx_eq_zipIdx_map, List.flatMap_map]
  simp only [Function.comp_apply, Node.toList]
  change ((groups leafCapacity entries).zipIdx.map Prod.fst).flatten = entries
  rw [List.zipIdx_map_fst]
  exact flatten_groups leafCapacity entries

theorem numberedLeaves_root_ne_pendingBytePage (startPage : Nat)
    (entries : List (PagedBTree.Entry Value))
    (node : Node Value) (member : node ∈ numberedLeaves startPage entries) :
    node.rootId ≠ pendingBytePage := by
  unfold numberedLeaves at member
  rw [List.mem_mapIdx] at member
  rcases member with ⟨offset, bound, equal⟩
  rw [← equal]
  exact allocatedPage_ne_pendingBytePage startPage offset

def numberedBranches (startPage : Nat) (nodes : List (Node Value)) :
    List (Node Value) :=
  (groups interiorFanout nodes).mapIdx fun offset children =>
    .branch (allocatedPage startPage offset) children

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

/-! ## Byte-selected interior fanout

Table separators are fixed-width rowids, so `interiorFanout` is exact there.
Index separators are promoted records whose byte widths depend on the indexed
value.  The generic builder below lets the index codec select a smaller, proved
page-fitting fanout without returning to a 2-3 physical topology. -/

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

/-! ## Linear admission of ordered entry streams

`List.Pairwise` is the proof-facing invariant, but its generic decision
procedure checks every pair.  For a transitive key order, adjacent comparisons
are equivalent and linear.  Validating open uses this decision procedure so a
million-row image does not pay a quadratic proof-construction tax. -/

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

/-! ## Local right-spine insertion

SQLite rowids allocated by the Core are strictly increasing.  Appending the
new terminal chunk therefore needs one right-spine descent, not a comparison
against every existing chunk.  A full leaf splits into two leaves; a full
interior page splits into two pages and propagates one level upward. -/

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

theorem appendStep_toList {fuel nextPage after : Nat}
    {entry : PagedBTree.Entry Value} {node : Node Value}
    {result : AppendResult Value}
    (success : appendStep fuel nextPage entry node = some (result, after)) :
    result.toList = node.toList ++ [entry] := by
  induction fuel generalizing nextPage after node result with
  | zero => simp [appendStep] at success
  | succ fuel induction =>
      cases node with
      | leaf pageId entries =>
          simp only [appendStep] at success
          split at success
          next =>
            simp only [Option.some.injEq, Prod.mk.injEq] at success
            rcases success with ⟨rfl, rfl⟩
            simp [AppendResult.toList, AppendResult.nodes, Node.toList]
          next =>
            split at success
            next =>
              simp only [Option.some.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              simp [AppendResult.toList, AppendResult.nodes, Node.toList]
            next => contradiction

      | branch pageId children =>
          simp only [appendStep] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨split, splitResult, success⟩
          rcases split with ⟨initial, last⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨recursive, recursiveResult, success⟩
          rcases recursive with ⟨childResult, afterChild⟩
          have childContents := induction recursiveResult
          change childResult.toList = last.toList ++ [entry] at childContents
          have childrenEq := splitLast?_reconstruct splitResult
          simp only [splitResult, recursiveResult, Option.bind_eq_bind,
            Option.bind] at success
          have updatedContents :
              (initial ++ childResult.nodes).flatMap Node.toList =
                children.flatMap Node.toList ++ [entry] := by
            rw [List.flatMap_append]
            change initial.flatMap Node.toList ++ childResult.toList = _
            rw [childContents, ← childrenEq, List.flatMap_append,
              List.flatMap_singleton, List.append_assoc]
          split at success
          next =>
            simp only [Option.some.injEq, Prod.mk.injEq] at success
            rcases success with ⟨rfl, rfl⟩
            simp only [AppendResult.toList, AppendResult.nodes,
              List.flatMap_singleton, Node.toList]
            exact updatedContents
          next =>
            split at success
            next =>
              simp only [Option.some.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              simp only [AppendResult.toList, AppendResult.nodes,
                List.flatMap_cons, List.flatMap_singleton, Node.toList]
              simp only [List.flatMap_nil, List.append_nil]
              let nodes := initial ++ childResult.nodes
              change (nodes.take (nodes.length / 2)).flatMap Node.toList ++
                (nodes.drop (nodes.length / 2)).flatMap Node.toList = _
              rw [← List.flatMap_append, List.take_append_drop]
              exact updatedContents
            next => contradiction

theorem appendStep_firstRootId {fuel nextPage after : Nat}
    {entry : PagedBTree.Entry Value} {node : Node Value}
    {result : AppendResult Value}
    (success : appendStep fuel nextPage entry node = some (result, after)) :
    result.firstRootId? = some node.rootId := by
  induction fuel generalizing nextPage after node result with
  | zero => simp [appendStep] at success
  | succ fuel induction =>
      cases node with
      | leaf pageId entries =>
          simp only [appendStep] at success
          split at success
          next =>
            simp only [Option.some.injEq, Prod.mk.injEq] at success
            rcases success with ⟨rfl, rfl⟩
            rfl
          next =>
            split at success
            next =>
              simp only [Option.some.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              rfl
            next => contradiction
      | branch pageId children =>
          simp only [appendStep] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨split, splitResult, success⟩
          rcases split with ⟨initial, last⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨recursive, recursiveResult, success⟩
          rcases recursive with ⟨childResult, afterChild⟩
          simp only [splitResult, recursiveResult, Option.bind_eq_bind,
            Option.bind] at success
          split at success
          next =>
            simp only [Option.some.injEq, Prod.mk.injEq] at success
            rcases success with ⟨rfl, rfl⟩
            rfl
          next =>
            split at success
            next =>
              simp only [Option.some.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              rfl
            next => contradiction

structure Appended (store : Store Value) (entry : PagedBTree.Entry Value) where
  value : Store Value
  toList_eq : value.toList = store.toList ++ [entry]
  rootId_eq : value.root.rootId = store.root.rootId

def Store.append? (store : Store Value) (entry : PagedBTree.Entry Value)
    (after : ∀ old ∈ store.toList, old.1 < entry.1) :
    Option (Appended store entry) :=
  match appended : appendStep (store.root.height + 1) store.nextPage entry
      store.root with
  | none => none
  | some (.done root, nextPage) =>
      let value : Store Value := {
        root
        nextPage
        represents := by
          have contents := appendStep_toList appended
          simp only [AppendResult.toList, AppendResult.nodes,
            List.flatMap_singleton] at contents
          rw [contents, List.pairwise_append]
          refine ⟨store.represents, by simp, ?_⟩
          intro old oldMember new newMember
          simp only [List.mem_singleton] at newMember
          subst new
          exact after old oldMember }
      some ⟨value, by
        change root.toList = store.toList ++ [entry]
        simpa [AppendResult.toList, AppendResult.nodes, Store.toList] using
          appendStep_toList appended, by
        change root.rootId = store.root.rootId
        simpa [AppendResult.firstRootId?] using
          appendStep_firstRootId appended⟩
  | some (.split left right, nextPage) =>
      let root := .branch store.root.rootId
        [left.setRootId (allocatedPage nextPage 0), right]
      let value : Store Value := {
        root
        nextPage := allocatedPage nextPage 1
        represents := by
          have contents := appendStep_toList appended
          simp only [AppendResult.toList, AppendResult.nodes,
            List.flatMap_cons, List.flatMap_singleton, List.flatMap_nil,
            List.append_nil] at contents
          dsimp only [root]
          simp only [Node.toList, List.flatMap_cons, List.flatMap_singleton,
            List.flatMap_nil, List.append_nil]
          change (left.setRootId (allocatedPage nextPage 0)).toList ++
            right.toList |>.Pairwise
            (fun left right => left.1 < right.1)
          rw [Node.toList_setRootId, contents, List.pairwise_append]
          refine ⟨store.represents, by simp, ?_⟩
          intro old oldMember new newMember
          simp only [List.mem_singleton] at newMember
          subst new
          exact after old oldMember }
      some ⟨value, by
        dsimp only [value, Store.toList, root]
        simpa [AppendResult.toList, AppendResult.nodes, Node.toList] using
          appendStep_toList appended, by
        rfl⟩

/-! ## Identity-preserving terminal replacement

Appending a row usually changes the last byte-budgeted chunk rather than
creating a new chunk.  This operation rewrites exactly the right spine and
keeps every page identity.  Its theorem exposes both the removed terminal
entry and the exact replacement sequence, so callers never validate the
result by flattening and comparing the complete table. -/

structure NodeReplacedLast (node : Node Value)
    (entry : PagedBTree.Entry Value) where
  value : Node Value
  initial : List (PagedBTree.Entry Value)
  old : PagedBTree.Entry Value
  before_eq : node.toList = initial ++ [old]
  after_eq : value.toList = initial ++ [entry]
  rootId_eq : value.rootId = node.rootId

def replaceLastStep : Nat → (node : Node Value) →
    (entry : PagedBTree.Entry Value) →
    Option (NodeReplacedLast node entry)
  | 0, _, _ => none
  | _ + 1, node@(.leaf pageId entries), entry =>
      match splitResult : splitLast? entries with
      | none => none
      | some (initial, old) =>
          let value := Node.leaf pageId (initial ++ [entry])
          some {
            value
            initial
            old
            before_eq := by
              simpa [Node.toList] using
                (splitLast?_reconstruct splitResult).symm
            after_eq := by simp [value, Node.toList]
            rootId_eq := rfl }
  | fuel + 1, node@(.branch pageId children), entry =>
      match splitResult : splitLast? children with
      | none => none
      | some (initialChildren, last) =>
          match replaceLastStep fuel last entry with
          | none => none
          | some child =>
              let value := Node.branch pageId
                (initialChildren ++ [child.value])
              some {
                value
                initial := initialChildren.flatMap Node.toList ++ child.initial
                old := child.old
                before_eq := by
                  simp only [Node.toList, List.flatMap_append,
                    List.flatMap_singleton]
                  rw [← splitLast?_reconstruct splitResult,
                    List.flatMap_append, List.flatMap_singleton,
                    child.before_eq, List.append_assoc]
                after_eq := by
                  simp only [value, Node.toList, List.flatMap_append,
                    List.flatMap_singleton, child.after_eq,
                    List.append_assoc]
                rootId_eq := rfl }

def Node.replaceLast? (node : Node Value)
    (entry : PagedBTree.Entry Value) :
    Option (NodeReplacedLast node entry) :=
  replaceLastStep (node.height + 1) node entry

structure ReplacedLast (store : Store Value)
    (entry : PagedBTree.Entry Value) where
  value : Store Value
  initial : List (PagedBTree.Entry Value)
  old : PagedBTree.Entry Value
  before_eq : store.toList = initial ++ [old]
  after_eq : value.toList = initial ++ [entry]
  rootId_eq : value.root.rootId = store.root.rootId

def Store.replaceLast? (store : Store Value)
    (entry : PagedBTree.Entry Value)
    (ordered : ∀ initial old, store.toList = initial ++ [old] →
      (initial ++ [entry]).Pairwise (fun left right => left.1 < right.1)) :
    Option (ReplacedLast store entry) :=
  match store.root.replaceLast? entry with
  | none => none
  | some replaced =>
      let value : Store Value := {
        root := replaced.value
        nextPage := store.nextPage
        represents := by
          rw [replaced.after_eq]
          exact ordered replaced.initial replaced.old replaced.before_eq }
      some {
        value
        initial := replaced.initial
        old := replaced.old
        before_eq := replaced.before_eq
        after_eq := by
          change replaced.value.toList = replaced.initial ++ [entry]
          exact replaced.after_eq
        rootId_eq := replaced.rootId_eq }

theorem Store.replaceLast?_toList {store : Store Value}
    {entry : PagedBTree.Entry Value}
    {ordered : ∀ initial old, store.toList = initial ++ [old] →
      (initial ++ [entry]).Pairwise (fun left right => left.1 < right.1)}
    {result : ReplacedLast store entry}
    (_success : store.replaceLast? entry ordered = some result) :
    result.value.toList = result.initial ++ [entry] := by
  exact result.after_eq

theorem Store.replaceLast?_rootId {store : Store Value}
    {entry : PagedBTree.Entry Value}
    {ordered : ∀ initial old, store.toList = initial ++ [old] →
      (initial ++ [entry]).Pairwise (fun left right => left.1 < right.1)}
    {result : ReplacedLast store entry}
    (_success : store.replaceLast? entry ordered = some result) :
    result.value.root.rootId = store.root.rootId := by
  exact result.rootId_eq

end WidePageTree
end SQLeanite
