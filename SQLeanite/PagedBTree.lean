import Std

namespace SQLeanite
namespace PagedBTree

abbrev Entry (Value : Type) := Nat × Value

def KeysStrictlySorted (entries : List (Entry Value)) : Prop :=
  entries.Pairwise fun left right => left.1 < right.1

/-- Insert or replace a key in a sorted duplicate-free entry list. -/
def orderedInsert (key : Nat) (value : Value) :
    List (Entry Value) → List (Entry Value)
  | [] => [(key, value)]
  | entry :: entries =>
      if key < entry.1 then (key, value) :: entry :: entries
      else if entry.1 < key then entry :: orderedInsert key value entries
      else (key, value) :: entries

theorem mem_orderedInsert {candidate : Entry Value} {entries : List (Entry Value)}
    (member : candidate ∈ orderedInsert key value entries) :
    candidate = (key, value) ∨ candidate ∈ entries := by
  induction entries with
  | nil => simpa [orderedInsert] using member
  | cons entry entries induction =>
      simp only [orderedInsert] at member
      split at member
      · simp only [List.mem_cons] at member
        rcases member with equal | equal | member
        · exact .inl equal
        · exact .inr (by simp [equal])
        · exact .inr (.tail entry member)
      · split at member
        · simp only [List.mem_cons] at member
          rcases member with equal | member
          · exact .inr (by simp [equal])
          · exact (induction member).imp id (List.Mem.tail entry)
        · simp only [List.mem_cons] at member
          rcases member with equal | member
          · exact .inl equal
          · exact .inr (.tail entry member)

theorem orderedInsert_sorted (entries : List (Entry Value))
    (sorted : KeysStrictlySorted entries) :
    KeysStrictlySorted (orderedInsert key value entries) := by
  induction entries with
  | nil => simp [orderedInsert, KeysStrictlySorted]
  | cons entry entries induction =>
      simp only [KeysStrictlySorted, List.pairwise_cons] at sorted
      simp only [orderedInsert]
      split
      next keyLess =>
        simp only [KeysStrictlySorted, List.pairwise_cons]
        refine ⟨?_, sorted⟩
        intro candidate member
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · simpa [equal] using keyLess
        · exact Nat.lt_trans keyLess (sorted.1 candidate member)
      next keyNotLess =>
        split
        next entryLess =>
          simp only [KeysStrictlySorted, List.pairwise_cons]
          refine ⟨?_, induction sorted.2⟩
          intro candidate member
          rcases mem_orderedInsert member with equal | old
          · simpa [equal] using entryLess
          · exact sorted.1 candidate old
        next entryNotLess =>
          have equal : key = entry.1 := by omega
          subst key
          simp only [KeysStrictlySorted, List.pairwise_cons]
          exact sorted

def eraseKey (key : Nat) (entries : List (Entry Value)) : List (Entry Value) :=
  entries.filter fun entry => decide (entry.1 ≠ key)

theorem eraseKey_eq_filter (key : Nat) (entries : List (Entry Value)) :
    eraseKey key entries = entries.filter (fun entry => entry.1 ≠ key) := by
  rfl

structure LeafPage (Value : Type) where
  entries : List (Entry Value)
  deriving Repr

/-- Leaf capacity two keeps the executable split/merge core small while still
exercising every page-boundary case. -/
def LeafPage.WithinCapacity (page : LeafPage Value) : Prop :=
  page.entries.length ≤ 2

def paginate : List (Entry Value) → List (LeafPage Value)
  | [] => []
  | [entry] => [⟨[entry]⟩]
  | first :: second :: entries =>
      ⟨[first, second]⟩ :: paginate entries

def flattenPages (pages : List (LeafPage Value)) : List (Entry Value) :=
  pages.flatMap (·.entries)

theorem flattenPages_paginate : (entries : List (Entry Value)) →
    flattenPages (paginate entries) = entries
  | [] => rfl
  | [entry] => rfl
  | first :: second :: entries => by
      change [first, second] ++ flattenPages (paginate entries) =
        first :: second :: entries
      rw [flattenPages_paginate entries]
      rfl

theorem paginate_withinCapacity : (entries : List (Entry Value)) →
    ∀ page ∈ paginate entries, page.WithinCapacity
  | [] => by simp [paginate]
  | [entry] => by simp [paginate, LeafPage.WithinCapacity]
  | first :: second :: entries => by
      intro page member
      simp only [paginate, List.mem_cons] at member
      rcases member with equal | member
      · subst page
        simp [LeafPage.WithinCapacity]
      · exact paginate_withinCapacity entries page member

private theorem pageRefs_flatMap (pages : List (LeafPage Value)) :
    (List.ofFn fun pageId : Fin pages.length => pageId).flatMap
        (fun pageId => (pages.get pageId).entries) =
      flattenPages pages := by
  induction pages with
  | nil => simp [flattenPages]
  | cons page pages induction =>
      rw [List.ofFn_succ]
      simp only [List.flatMap_cons, flattenPages, List.flatMap_cons]
      apply congrArg (page.entries ++ ·)
      have tailIds :
          List.ofFn (fun pageId : Fin pages.length => pageId.succ) =
            (List.ofFn fun pageId : Fin pages.length => pageId).map Fin.succ := by
        apply List.ext_getElem
        · simp
        · intro index leftBound rightBound
          simp [List.getElem_ofFn]
      rw [tailIds]
      simpa only [List.flatMap_map, List.get_cons_succ', flattenPages] using induction

/-- A two-level B+tree. The root directory stores only in-range page ids and is
proof-carrying: every leaf occurs exactly once, in pager order. -/
structure Tree (Value : Type) where
  pages : List (LeafPage Value)
  children : List (Fin pages.length)
  coversPages : children = List.ofFn fun pageId => pageId

def Tree.empty : Tree Value := ⟨[], [], by simp⟩

def Tree.toList (tree : Tree Value) : List (Entry Value) :=
  tree.children.flatMap fun pageId => (tree.pages.get pageId).entries

theorem Tree.toList_eq_flattenPages (tree : Tree Value) :
    tree.toList = flattenPages tree.pages := by
  unfold Tree.toList flattenPages
  rw [tree.coversPages]
  exact pageRefs_flatMap tree.pages

def Tree.WellFormed (tree : Tree Value) : Prop :=
  KeysStrictlySorted tree.toList ∧
    ∀ page ∈ tree.pages, page.WithinCapacity

theorem Tree.empty_wellFormed : (Tree.empty : Tree Value).WellFormed := by
  simp [Tree.empty, Tree.WellFormed, Tree.toList, KeysStrictlySorted]

def Tree.ofList (entries : List (Entry Value)) : Tree Value :=
  let pages := paginate entries
  ⟨pages, List.ofFn (fun pageId => pageId), rfl⟩

theorem Tree.toList_ofList (entries : List (Entry Value)) :
    (Tree.ofList entries).toList = entries := by
  rw [Tree.toList_eq_flattenPages]
  exact flattenPages_paginate entries

def Tree.insert (tree : Tree Value) (key : Nat) (value : Value) : Tree Value :=
  Tree.ofList (orderedInsert key value tree.toList)

def Tree.delete (tree : Tree Value) (key : Nat) : Tree Value :=
  Tree.ofList (eraseKey key tree.toList)

theorem Tree.toList_insert (tree : Tree Value) (key : Nat) (value : Value) :
    (tree.insert key value).toList = orderedInsert key value tree.toList :=
  Tree.toList_ofList _

theorem Tree.toList_delete (tree : Tree Value) (key : Nat) :
    (tree.delete key).toList =
      tree.toList.filter (fun entry => entry.1 ≠ key) := by
  rw [Tree.delete, Tree.toList_ofList, eraseKey_eq_filter]

theorem Tree.toList_sorted (tree : Tree Value) (wellFormed : tree.WellFormed) :
    KeysStrictlySorted tree.toList := wellFormed.1

theorem Tree.insert_wellFormed (tree : Tree Value) (wellFormed : tree.WellFormed)
    (key : Nat) (value : Value) : (tree.insert key value).WellFormed := by
  constructor
  · rw [Tree.toList_insert]
    exact orderedInsert_sorted tree.toList wellFormed.1
  · exact paginate_withinCapacity _

theorem Tree.delete_wellFormed (tree : Tree Value) (wellFormed : tree.WellFormed)
    (key : Nat) : (tree.delete key).WellFormed := by
  constructor
  · rw [Tree.toList_delete]
    exact wellFormed.1.filter _
  · exact paginate_withinCapacity _

/-- All page references exposed by the tree are valid by construction. -/
def Tree.pageRefs (tree : Tree Value) : List (Fin tree.pages.length) :=
  tree.children

theorem Tree.pageRefs_length (tree : Tree Value) :
    tree.pageRefs.length = tree.pages.length := by
  rw [Tree.pageRefs, tree.coversPages]
  simp

structure OverflowLeafPage (Value : Type) where
  entries : List (Entry Value)
  hasThree : entries.length = 3
  deriving Repr

def OverflowLeafPage.split (page : OverflowLeafPage Value) :
    List (LeafPage Value) :=
  [⟨page.entries.take 2⟩, ⟨page.entries.drop 2⟩]

theorem OverflowLeafPage.split_preserves_toList
    (page : OverflowLeafPage Value) :
    flattenPages page.split = page.entries := by
  simp [OverflowLeafPage.split, flattenPages]

def mergeAdjacent (left right : LeafPage Value) : List (LeafPage Value) :=
  paginate (left.entries ++ right.entries)

theorem mergeAdjacent_preserves_toList (left right : LeafPage Value) :
    flattenPages (mergeAdjacent left right) = left.entries ++ right.entries :=
  flattenPages_paginate _

theorem insert_into_full_leaf_splits (first second third : Value) :
    ((Tree.ofList [(1, first), (2, second)]).insert 3 third).pages.length = 2 := by
  rfl

theorem delete_from_two_pages_merges (first second third : Value) :
    ((Tree.ofList [(1, first), (2, second), (3, third)]).delete 2).pages.length = 1 := by
  rfl

end PagedBTree
end SQLeanite
