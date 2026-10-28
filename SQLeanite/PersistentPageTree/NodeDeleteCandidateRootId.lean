import SQLeanite.PersistentPageTree.StoreReuseFreshGetDRootId

namespace SQLeanite
namespace PersistentPageTree
open RecursiveBPlusTree

theorem Node.deleteCandidate_rootId (node : Node Value) (key : Nat) :
    (node.deleteCandidate key).1.rootId = node.rootId := by
  have preserved := node.deleteStep_preservesRoot key
  unfold Node.deleteCandidate
  cases changed : node.deleteStep key with
  | done updated freed => simpa [changed, DeleteResult.PreservesRoot] using preserved
  | underflow updated freed =>
      simpa [changed, DeleteResult.PreservesRoot] using preserved
  | empty freed => rfl

theorem Node.deleteStep_erases (node : Node Value) (key : Nat) :
    (node.deleteStep key).erase = node.erase.deleteBalancedStep key := by
  induction node with
  | leaf pageId entries =>
      simp only [Node.deleteStep, RecursiveBPlusTree.Node.deleteBalancedStep,
        Node.erase]
      generalize remainingEq : PagedBTree.eraseKey key entries = remaining
      cases remaining <;> rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [Node.deleteStep,
        RecursiveBPlusTree.Node.deleteBalancedStep, Node.erase]
      split
      next =>
        rw [← leftInduction]
        cases changed : left.deleteStep key with
        | done updated freed => rfl
        | underflow under freed =>
            cases right <;>
              simp [repairTwoLeft, DeleteResult.erase, Node.erase,
                Node.erase_setRootId, RecursiveBPlusTree.repairTwoLeft]
        | empty freed =>
            cases right <;>
              simp [repairTwoLeft, DeleteResult.erase, Node.erase,
                Node.erase_setRootId, RecursiveBPlusTree.repairTwoLeft]
      next =>
        rw [← rightInduction]
        cases changed : right.deleteStep key with
        | done updated freed => rfl
        | underflow under freed =>
            cases left <;>
              simp [repairTwoRight, DeleteResult.erase, Node.erase,
                Node.erase_setRootId, RecursiveBPlusTree.repairTwoRight]
        | empty freed =>
            cases left <;>
              simp [repairTwoRight, DeleteResult.erase, Node.erase,
                Node.erase_setRootId, RecursiveBPlusTree.repairTwoRight]
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [Node.deleteStep,
        RecursiveBPlusTree.Node.deleteBalancedStep, Node.erase]
      split
      next =>
        rw [← leftInduction]
        cases changed : left.deleteStep key with
        | done updated freed => rfl
        | underflow under freed =>
            cases middle <;>
              simp [repairThreeLeft, DeleteResult.erase, Node.erase,
                RecursiveBPlusTree.repairThreeLeft]
        | empty freed =>
            cases middle <;>
              simp [repairThreeLeft, DeleteResult.erase, Node.erase,
                RecursiveBPlusTree.repairThreeLeft]
      next =>
        split
        next =>
          rw [← middleInduction]
          cases changed : middle.deleteStep key with
          | done updated freed => rfl
          | underflow under freed =>
              cases left <;>
                simp [repairThreeMiddle, DeleteResult.erase, Node.erase,
                  RecursiveBPlusTree.repairThreeMiddle]
          | empty freed =>
              cases left <;>
                simp [repairThreeMiddle, DeleteResult.erase, Node.erase,
                  RecursiveBPlusTree.repairThreeMiddle]
        next =>
          rw [← rightInduction]
          cases changed : right.deleteStep key with
          | done updated freed => rfl
          | underflow under freed =>
              cases middle <;>
                simp [repairThreeRight, DeleteResult.erase, Node.erase,
                  RecursiveBPlusTree.repairThreeRight]
          | empty freed =>
              cases middle <;>
                simp [repairThreeRight, DeleteResult.erase, Node.erase,
                  RecursiveBPlusTree.repairThreeRight]

theorem Node.deleteCandidate_erases (node : Node Value) (key : Nat) :
    (node.deleteCandidate key).1.erase = node.erase.deleteBalanced key := by
  unfold Node.deleteCandidate RecursiveBPlusTree.Node.deleteBalanced
  have erased := node.deleteStep_erases key
  cases changed : node.deleteStep key with
  | done updated freed =>
      simp only [changed, DeleteResult.erase] at erased
      rw [← erased]
  | underflow updated freed =>
      simp only [changed, DeleteResult.erase] at erased
      rw [← erased]
  | empty freed =>
      simp only [changed, DeleteResult.erase] at erased
      rw [← erased]
      simp [Node.erase]

/-- Stable deletion is admitted only when the localized borrow/merge candidate
passes the already proved recursive-tree invariant checker.  This is not a
logical-content check: `deleteCandidate_erases` proves its abstraction. -/
def Store.delete? (store : Store Value) (key : Nat) :
    Option (Store Value × List PageId) :=
  let changed := store.root.deleteCandidate key
  if valid : changed.1.erase.checkRootValid then
    some (⟨changed.1, store.nextPage,
      (RecursiveBPlusTree.Node.checkRootValid_iff changed.1.erase).mp valid⟩,
      changed.2)
  else none

theorem Store.delete?_rootId {store updated : Store Value} {key : Nat}
    {freed : List PageId}
    (success : store.delete? key = some (updated, freed)) :
    updated.root.rootId = store.root.rootId := by
  unfold Store.delete? at success
  dsimp only at success
  split at success
  next =>
    injection success with equal
    cases equal
    exact store.root.deleteCandidate_rootId key
  next => contradiction

theorem Store.delete?_toList {store : Store Value} {key : Nat}
    {updated : Store Value} {freed : List PageId}
    (success : store.delete? key = some (updated, freed)) :
    updated.root.erase.toList =
      store.root.erase.toList.filter (fun entry => entry.1 ≠ key) := by
  unfold Store.delete? at success
  dsimp only at success
  split at success
  next =>
    injection success with equal
    cases equal
    have candidate := store.root.deleteCandidate_erases key
    rw [candidate]
    exact store.root.erase.toList_deleteBalanced store.rootValid.routes key
  next => contradiction

/-- The materialized payload of one stable page.  Children are page numbers,
not nested values, which is the shape consumed by a pager/codec. -/
inductive Page (Value : Type) where
  | leaf (pageId : PageId) (entries : List (PagedBTree.Entry Value))
  | branch2 (pageId left : PageId) (separator : Nat) (right : PageId)
  | branch3 (pageId left : PageId) (firstSeparator : Nat) (middle : PageId)
      (secondSeparator : Nat) (right : PageId)
  deriving Repr, DecidableEq

def Page.pageId : Page Value → PageId
  | .leaf pageId _ | .branch2 pageId .. | .branch3 pageId .. => pageId

def Node.pages : Node Value → List (Page Value)
  | .leaf pageId entries => [.leaf pageId entries]
  | .branch2 pageId left separator right =>
      .branch2 pageId left.rootId separator right.rootId ::
        left.pages ++ right.pages
  | .branch3 pageId left firstSeparator middle secondSeparator right =>
      .branch3 pageId left.rootId firstSeparator middle.rootId secondSeparator
          right.rootId ::
        left.pages ++ middle.pages ++ right.pages

def findPage? (pageId : PageId) (pages : List (Page Value)) : Option (Page Value) :=
  pages.find? (fun page => page.pageId = pageId)

/-- Dirty pages are selected by stable identity.  New pages and pages whose
payload or child links changed are writes; byte encoding is intentionally a
later refinement of this exact delta. -/
def changedPages [DecidableEq Value] (before after : Node Value) :
    List (Page Value) :=
  after.pages.filter fun page => findPage? page.pageId before.pages != some page

theorem not_mem_changedPages [DecidableEq Value] (before after : Node Value)
    (page : Page Value) (member : page ∈ after.pages)
    (unchanged : page ∉ changedPages before after) :
    findPage? page.pageId before.pages = some page := by
  unfold changedPages at unchanged
  simp only [List.mem_filter, member, true_and, Bool.not_eq_true] at unchanged
  simpa using unchanged

end PersistentPageTree

end SQLeanite
