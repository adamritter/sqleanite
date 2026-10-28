import SQLeanite.PersistentPageTree.NodeInsertStepDonePathAgrees
import SQLeanite.RecursiveBPlusTree.NodeToListDelete

namespace SQLeanite
namespace PersistentPageTree
open RecursiveBPlusTree

theorem Store.reuseFresh_getD_rootId (store : Store Value)
    (firstFresh : Nat) (freed : List PageId)
    (old : store.root.rootId < firstFresh) :
    ((store.reuseFresh? firstFresh freed).getD (store, freed)).1.root.rootId =
      store.root.rootId := by
  cases result : store.reuseFresh? firstFresh freed with
  | none => simp [result]
  | some pair =>
      rcases pair with ⟨reused, remaining⟩
      simpa [result] using Store.reuseFresh?_rootId old result

/-- Assign consecutive physical page IDs to an already verified logical tree.
This is the bulk-loading bridge: every logical node becomes exactly one
materialized page and the returned high-water mark is ready for later local
allocation. -/
def identifyFrom (nextPage : Nat) :
    RecursiveBPlusTree.Node Value → Node Value × Nat
  | .leaf entries => (.leaf nextPage entries, nextPage + 1)
  | .branch2 left separator right =>
      let leftResult := identifyFrom (nextPage + 1) left
      let rightResult := identifyFrom leftResult.2 right
      (.branch2 nextPage leftResult.1 separator rightResult.1, rightResult.2)
  | .branch3 left firstSeparator middle secondSeparator right =>
      let leftResult := identifyFrom (nextPage + 1) left
      let middleResult := identifyFrom leftResult.2 middle
      let rightResult := identifyFrom middleResult.2 right
      (.branch3 nextPage leftResult.1 firstSeparator middleResult.1
        secondSeparator rightResult.1, rightResult.2)

theorem identifyFrom_erases (nextPage : Nat)
    (node : RecursiveBPlusTree.Node Value) :
    (identifyFrom nextPage node).1.erase = node := by
  induction node generalizing nextPage with
  | leaf => rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp only [identifyFrom, Node.erase]
      rw [leftInduction, rightInduction]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [identifyFrom, Node.erase]
      rw [leftInduction, middleInduction, rightInduction]

def Store.empty (rootPage : Nat) : Store Value := {
  root := .leaf rootPage []
  nextPage := rootPage + 1
  rootValid := RecursiveBPlusTree.Node.empty_rootValid }

theorem identifyFrom_nextPage (nextPage : Nat)
    (node : RecursiveBPlusTree.Node Value) :
    (identifyFrom nextPage node).2 = nextPage + node.pageCount := by
  induction node generalizing nextPage with
  | leaf => rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp only [identifyFrom, RecursiveBPlusTree.Node.pageCount]
      rw [leftInduction, rightInduction]
      omega
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [identifyFrom, RecursiveBPlusTree.Node.pageCount]
      rw [leftInduction, middleInduction, rightInduction]
      omega

/-- Bulk identification allocates one consecutive, duplicate-free interval.
This is the base case for the database-wide allocator/freelist invariant. -/
theorem identifyFrom_pageIds (nextPage : Nat)
    (node : RecursiveBPlusTree.Node Value) :
    (identifyFrom nextPage node).1.pageIds =
      List.range' nextPage node.pageCount := by
  induction node generalizing nextPage with
  | leaf => rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp only [identifyFrom, Node.pageIds,
        RecursiveBPlusTree.Node.pageCount]
      rw [leftInduction, identifyFrom_nextPage, rightInduction]
      change List.range' nextPage 1 ++
          (List.range' (nextPage + 1) left.pageCount ++
            List.range' ((nextPage + 1) + left.pageCount) right.pageCount) = _
      rw [List.range'_append_1 (s := nextPage + 1)
        (m := left.pageCount) (n := right.pageCount)]
      simpa [Nat.add_assoc] using
        (List.range'_append_1 (s := nextPage) (m := 1)
          (n := left.pageCount + right.pageCount))
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [identifyFrom, Node.pageIds,
        RecursiveBPlusTree.Node.pageCount]
      rw [leftInduction, identifyFrom_nextPage, middleInduction,
        identifyFrom_nextPage, rightInduction]
      change List.range' nextPage 1 ++
          (List.range' (nextPage + 1) left.pageCount ++
            List.range' ((nextPage + 1) + left.pageCount) middle.pageCount ++
              List.range' (((nextPage + 1) + left.pageCount) +
                middle.pageCount) right.pageCount) = _
      rw [List.range'_append_1 (s := nextPage + 1)
        (m := left.pageCount) (n := middle.pageCount)]
      have rightStart : nextPage + 1 + left.pageCount + middle.pageCount =
          nextPage + 1 + (left.pageCount + middle.pageCount) := by omega
      rw [rightStart]
      rw [List.range'_append_1 (s := nextPage + 1)
        (m := left.pageCount + middle.pageCount) (n := right.pageCount)]
      simpa [Nat.add_assoc] using
        (List.range'_append_1 (s := nextPage) (m := 1)
          (n := left.pageCount + middle.pageCount + right.pageCount))

def Store.ofTree (rootPage : Nat) (node : RecursiveBPlusTree.Node Value)
    (valid : node.RootValid) : Store Value := {
  root := (identifyFrom rootPage node).1
  nextPage := (identifyFrom rootPage node).2
  rootValid := by simpa [identifyFrom_erases] using valid }

theorem Store.ofTree_represents (rootPage : Nat)
    (node : RecursiveBPlusTree.Node Value) (valid : node.RootValid) :
    (Store.ofTree rootPage node valid).Represents node.toList := by
  unfold Store.ofTree Store.Represents
  simp only
  rw [identifyFrom_erases]

def Store.build (rootPage : Nat)
    (entries : List (PagedBTree.Entry Value)) : Store Value :=
  entries.foldl (fun store entry => store.insert entry.1 entry.2)
    (Store.empty rootPage)

private theorem orderedInsert_at_end (accumulated : List (PagedBTree.Entry Value))
    (entry : PagedBTree.Entry Value)
    (before : ∀ old ∈ accumulated, old.1 < entry.1) :
    PagedBTree.orderedInsert entry.1 entry.2 accumulated =
      accumulated ++ [entry] := by
  induction accumulated with
  | nil => rfl
  | cons old accumulated induction =>
      simp only [PagedBTree.orderedInsert]
      have oldBefore := before old (by simp)
      rw [if_neg (Nat.not_lt_of_ge (Nat.le_of_lt oldBefore)),
        if_pos oldBefore]
      simp only [List.cons_append, List.cons.injEq, true_and]
      exact induction fun candidate member => before candidate (by simp [member])

private theorem fold_insert_sorted (store : Store Value)
    (entries : List (PagedBTree.Entry Value))
    (sorted : PagedBTree.KeysStrictlySorted entries)
    (before : ∀ old ∈ store.root.erase.toList, ∀ new ∈ entries,
      old.1 < new.1) :
    (entries.foldl (fun current entry => current.insert entry.1 entry.2)
      store).root.erase.toList = store.root.erase.toList ++ entries := by
  induction entries generalizing store with
  | nil => simp
  | cons entry entries induction =>
      simp only [PagedBTree.KeysStrictlySorted, List.pairwise_cons] at sorted
      have entryAfter : ∀ old ∈ store.root.erase.toList, old.1 < entry.1 :=
        fun old member => before old member entry (by simp)
      have nextBefore : ∀ old ∈ (store.insert entry.1 entry.2).root.erase.toList,
          ∀ new ∈ entries, old.1 < new.1 := by
        intro old oldMember new newMember
        rw [Store.insert_toList, orderedInsert_at_end] at oldMember
        · rw [List.mem_append] at oldMember
          rcases oldMember with oldMember | oldMember
          · exact before old oldMember new (by simp [newMember])
          · simp only [List.mem_singleton] at oldMember
            subst old
            exact sorted.1 new newMember
        · exact entryAfter
      rw [List.foldl_cons,
        induction (store := store.insert entry.1 entry.2) sorted.2 nextBefore,
        Store.insert_toList, orderedInsert_at_end _ entry entryAfter]
      simp [List.append_assoc]

/-- The bulk builder establishes the representation relation without decoding
or comparing its output.  This is the logical inverse needed by the later byte
encoder refinement. -/
theorem Store.build_represents (rootPage : Nat)
    (entries : List (PagedBTree.Entry Value))
    (sorted : PagedBTree.KeysStrictlySorted entries) :
    (Store.build rootPage entries).Represents entries := by
  unfold Store.build Store.Represents
  simpa [Store.empty, Node.erase, RecursiveBPlusTree.Node.toList] using
    fold_insert_sorted (Store.empty rootPage) entries sorted (by
      intro old member
      simp [Store.empty, Node.erase, RecursiveBPlusTree.Node.toList] at member)

inductive DeleteResult (Value : Type) where
  | done (node : Node Value) (freed : List PageId)
  | underflow (node : Node Value) (freed : List PageId)
  | empty (freed : List PageId)

/-- Repairing an interior underflow can promote the underflow node's page to a
new parent.  The child then needs the page released by the lower-level merge;
reusing it here preserves page count and, critically, prevents parent and child
from sharing one page ID.  The empty case is retained for totality and is
rejected later by the allocation validator if an impossible repair reaches it. -/
def reuseFreedRoot (under : Node Value) :
    List PageId → Node Value × List PageId
  | [] => (under, [])
  | pageId :: freed => (under.setRootId pageId, freed)

@[simp] theorem reuseFreedRoot_erase (under : Node Value)
    (freed : List PageId) :
    (reuseFreedRoot under freed).1.erase = under.erase := by
  cases freed <;> simp [reuseFreedRoot]

def DeleteResult.erase : DeleteResult Value →
    RecursiveBPlusTree.DeleteResult Value
  | .done node _ => .done node.erase
  | .underflow node _ => .underflow node.erase
  | .empty _ => .empty

def repairTwoLeft (pageId : PageId) (separator : Nat)
    (deficit : Option (Node Value)) (right : Node Value)
    (freed : List PageId) : DeleteResult Value :=
  match deficit, right with
  | some under, .branch3 rightId first firstSeparator middle secondSeparator last =>
      let reused := reuseFreedRoot under freed
      .done (.branch2 pageId
        (.branch2 under.rootId reused.1 separator first) firstSeparator
        (.branch2 rightId middle secondSeparator last)) reused.2
  | some under, .branch2 rightId first middleSeparator last =>
      .underflow (.branch3 pageId under separator first middleSeparator last)
        (rightId :: freed)
  | some under, _ => .underflow (.branch2 pageId under separator right) freed
  | none, _ => .underflow (right.setRootId pageId) (right.rootId :: freed)

def repairTwoRight (pageId : PageId) (left : Node Value)
    (separator : Nat) (deficit : Option (Node Value))
    (freed : List PageId) : DeleteResult Value :=
  match left, deficit with
  | .branch3 leftId first firstSeparator middle secondSeparator last, some under =>
      let reused := reuseFreedRoot under freed
      .done (.branch2 pageId
        (.branch2 leftId first firstSeparator middle) secondSeparator
        (.branch2 under.rootId last separator reused.1)) reused.2
  | .branch2 leftId first middleSeparator last, some under =>
      .underflow (.branch3 pageId first middleSeparator last separator under)
        (leftId :: freed)
  | _, some under => .underflow (.branch2 pageId left separator under) freed
  | _, none => .underflow (left.setRootId pageId) (left.rootId :: freed)

def repairThreeLeft (pageId : PageId) (firstSeparator : Nat)
    (deficit : Option (Node Value)) (middle : Node Value)
    (secondSeparator : Nat) (right : Node Value) (freed : List PageId) :
    DeleteResult Value :=
  match deficit, middle with
  | some under, .branch3 middleId first middleFirst second middleSecond third =>
      let reused := reuseFreedRoot under freed
      .done (.branch3 pageId
        (.branch2 under.rootId reused.1 firstSeparator first) middleFirst
        (.branch2 middleId second middleSecond third) secondSeparator right)
        reused.2
  | some under, .branch2 middleId first middleSeparator second =>
      .done (.branch2 pageId
        (.branch3 under.rootId (under.setRootId middleId) firstSeparator first
          middleSeparator second)
        secondSeparator right) freed
  | some under, _ =>
      .done (.branch3 pageId under firstSeparator middle secondSeparator right) freed
  | none, _ => .done (.branch2 pageId middle secondSeparator right) freed

def repairThreeMiddle (pageId : PageId) (left : Node Value)
    (firstSeparator : Nat) (deficit : Option (Node Value))
    (secondSeparator : Nat) (right : Node Value) (freed : List PageId) :
    DeleteResult Value :=
  match left, deficit with
  | .branch3 leftId first leftFirst second leftSecond third, some under =>
      let reused := reuseFreedRoot under freed
      .done (.branch3 pageId
        (.branch2 leftId first leftFirst second) leftSecond
        (.branch2 under.rootId third firstSeparator reused.1)
        secondSeparator right) reused.2
  | .branch2 leftId first leftSeparator second, some under =>
      .done (.branch2 pageId
        (.branch3 leftId first leftSeparator second firstSeparator under)
        secondSeparator right) freed
  | _, some under =>
      .done (.branch3 pageId left firstSeparator under secondSeparator right) freed
  | _, none => .done (.branch2 pageId left secondSeparator right) freed

def repairThreeRight (pageId : PageId) (left : Node Value)
    (firstSeparator : Nat) (middle : Node Value) (secondSeparator : Nat)
    (deficit : Option (Node Value)) (freed : List PageId) :
    DeleteResult Value :=
  match middle, deficit with
  | .branch3 middleId first middleFirst second middleSecond third, some under =>
      let reused := reuseFreedRoot under freed
      .done (.branch3 pageId left firstSeparator
        (.branch2 middleId first middleFirst second) middleSecond
        (.branch2 under.rootId third secondSeparator reused.1)) reused.2
  | .branch2 middleId first middleSeparator second, some under =>
      .done (.branch2 pageId left firstSeparator
        (.branch3 middleId first middleSeparator second secondSeparator under)) freed
  | _, some under =>
      .done (.branch3 pageId left firstSeparator middle secondSeparator under) freed
  | _, none => .done (.branch2 pageId left firstSeparator middle) freed

/-- Root-page identity carried by every nonempty deletion result.  The empty
case is repaired by `deleteCandidate` using the original root page. -/
def DeleteResult.PreservesRoot (pageId : PageId) :
    DeleteResult Value → Prop
  | .done node _ | .underflow node _ => node.rootId = pageId
  | .empty _ => True

private theorem repairTwoLeft_preservesRoot (pageId : PageId)
    (separator : Nat) (deficit : Option (Node Value)) (right : Node Value)
    (freed : List PageId) :
    (repairTwoLeft pageId separator deficit right freed).PreservesRoot pageId := by
  cases deficit <;> cases right <;>
    simp [repairTwoLeft, DeleteResult.PreservesRoot, reuseFreedRoot, Node.rootId,
      Node.setRootId]

private theorem repairTwoRight_preservesRoot (pageId : PageId)
    (left : Node Value) (separator : Nat) (deficit : Option (Node Value))
    (freed : List PageId) :
    (repairTwoRight pageId left separator deficit freed).PreservesRoot pageId := by
  cases left <;> cases deficit <;>
    simp [repairTwoRight, DeleteResult.PreservesRoot, reuseFreedRoot,
      Node.rootId, Node.setRootId]

private theorem repairThreeLeft_preservesRoot (pageId : PageId)
    (firstSeparator : Nat) (deficit : Option (Node Value))
    (middle : Node Value) (secondSeparator : Nat) (right : Node Value)
    (freed : List PageId) :
    (repairThreeLeft pageId firstSeparator deficit middle secondSeparator right
      freed).PreservesRoot pageId := by
  cases deficit <;> cases middle <;>
    simp [repairThreeLeft, DeleteResult.PreservesRoot, reuseFreedRoot,
      Node.rootId, Node.setRootId]

private theorem repairThreeMiddle_preservesRoot (pageId : PageId)
    (left : Node Value) (firstSeparator : Nat)
    (deficit : Option (Node Value)) (secondSeparator : Nat)
    (right : Node Value) (freed : List PageId) :
    (repairThreeMiddle pageId left firstSeparator deficit secondSeparator right
      freed).PreservesRoot pageId := by
  cases left <;> cases deficit <;>
    simp [repairThreeMiddle, DeleteResult.PreservesRoot, reuseFreedRoot,
      Node.rootId, Node.setRootId]

private theorem repairThreeRight_preservesRoot (pageId : PageId)
    (left : Node Value) (firstSeparator : Nat) (middle : Node Value)
    (secondSeparator : Nat) (deficit : Option (Node Value))
    (freed : List PageId) :
    (repairThreeRight pageId left firstSeparator middle secondSeparator deficit
      freed).PreservesRoot pageId := by
  cases middle <;> cases deficit <;>
    simp [repairThreeRight, DeleteResult.PreservesRoot, reuseFreedRoot,
      Node.rootId, Node.setRootId]

def Node.deleteStep (key : Nat) : Node Value → DeleteResult Value
  | .leaf pageId entries =>
      match PagedBTree.eraseKey key entries with
      | [] => .empty [pageId]
      | remaining => .done (.leaf pageId remaining) []
  | .branch2 pageId left separator right =>
      if key < separator then
        match left.deleteStep key with
        | .done updated freed =>
            .done (.branch2 pageId updated separator right) freed
        | .underflow under freed =>
            repairTwoLeft pageId separator (some under) right freed
        | .empty freed => repairTwoLeft pageId separator none right freed
      else
        match right.deleteStep key with
        | .done updated freed =>
            .done (.branch2 pageId left separator updated) freed
        | .underflow under freed =>
            repairTwoRight pageId left separator (some under) freed
        | .empty freed => repairTwoRight pageId left separator none freed
  | .branch3 pageId left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then
        match left.deleteStep key with
        | .done updated freed =>
            .done (.branch3 pageId updated firstSeparator middle
              secondSeparator right) freed
        | .underflow under freed =>
            repairThreeLeft pageId firstSeparator (some under) middle
              secondSeparator right freed
        | .empty freed => repairThreeLeft pageId firstSeparator none middle
            secondSeparator right freed
      else if key < secondSeparator then
        match middle.deleteStep key with
        | .done updated freed =>
            .done (.branch3 pageId left firstSeparator updated
              secondSeparator right) freed
        | .underflow under freed =>
            repairThreeMiddle pageId left firstSeparator (some under)
              secondSeparator right freed
        | .empty freed => repairThreeMiddle pageId left firstSeparator none
            secondSeparator right freed
      else
        match right.deleteStep key with
        | .done updated freed =>
            .done (.branch3 pageId left firstSeparator middle
              secondSeparator updated) freed
        | .underflow under freed =>
            repairThreeRight pageId left firstSeparator middle secondSeparator
              (some under) freed
        | .empty freed => repairThreeRight pageId left firstSeparator middle
            secondSeparator none freed

theorem Node.deleteStep_preservesRoot (node : Node Value) (key : Nat) :
    (node.deleteStep key).PreservesRoot node.rootId := by
  cases node with
  | leaf pageId entries =>
      simp only [Node.deleteStep, Node.rootId]
      generalize erased : PagedBTree.eraseKey key entries = remaining
      cases remaining <;> simp [DeleteResult.PreservesRoot, Node.rootId]
  | branch2 pageId left separator right =>
      simp only [Node.deleteStep, Node.rootId]
      split
      next =>
        cases changed : left.deleteStep key with
        | done => rfl
        | underflow under freed =>
            exact repairTwoLeft_preservesRoot pageId separator (some under)
              right freed
        | empty freed =>
            exact repairTwoLeft_preservesRoot pageId separator none right freed
      next =>
        cases changed : right.deleteStep key with
        | done => rfl
        | underflow under freed =>
            exact repairTwoRight_preservesRoot pageId left separator
              (some under) freed
        | empty freed =>
            exact repairTwoRight_preservesRoot pageId left separator none freed
  | branch3 pageId left firstSeparator middle secondSeparator right =>
      simp only [Node.deleteStep, Node.rootId]
      split
      next =>
        cases changed : left.deleteStep key with
        | done => rfl
        | underflow under freed =>
            exact repairThreeLeft_preservesRoot pageId firstSeparator
              (some under) middle secondSeparator right freed
        | empty freed =>
            exact repairThreeLeft_preservesRoot pageId firstSeparator none
              middle secondSeparator right freed
      next =>
        split
        next =>
          cases changed : middle.deleteStep key with
          | done => rfl
          | underflow under freed =>
              exact repairThreeMiddle_preservesRoot pageId left firstSeparator
                (some under) secondSeparator right freed
          | empty freed =>
              exact repairThreeMiddle_preservesRoot pageId left firstSeparator
                none secondSeparator right freed
        next =>
          cases changed : right.deleteStep key with
          | done => rfl
          | underflow under freed =>
              exact repairThreeRight_preservesRoot pageId left firstSeparator
                middle secondSeparator (some under) freed
          | empty freed =>
              exact repairThreeRight_preservesRoot pageId left firstSeparator
                middle secondSeparator none freed

def Node.deleteCandidate (node : Node Value) (key : Nat) : Node Value × List PageId :=
  match node.deleteStep key with
  | .done updated freed | .underflow updated freed => (updated, freed)
  | .empty freed => (.leaf node.rootId [], freed.filter (fun id => id ≠ node.rootId))

end PersistentPageTree

end SQLeanite
