import SQLeanite.RecursiveBPlusTree.Entry

namespace SQLeanite
namespace PersistentPageTree
open RecursiveBPlusTree

abbrev PageId := Nat

inductive Node (Value : Type) where
  | leaf (pageId : PageId) (entries : List (PagedBTree.Entry Value))
  | branch2 (pageId : PageId) (left : Node Value) (separator : Nat)
      (right : Node Value)
  | branch3 (pageId : PageId) (left : Node Value) (firstSeparator : Nat)
      (middle : Node Value) (secondSeparator : Nat) (right : Node Value)
  deriving Repr, DecidableEq

def Node.rootId : Node Value → PageId
  | .leaf pageId _ | .branch2 pageId .. | .branch3 pageId .. => pageId

def Node.erase : Node Value → RecursiveBPlusTree.Node Value
  | .leaf _ entries => .leaf entries
  | .branch2 _ left separator right =>
      .branch2 left.erase separator right.erase
  | .branch3 _ left firstSeparator middle secondSeparator right =>
      .branch3 left.erase firstSeparator middle.erase secondSeparator right.erase

/-- Page-identity-preserving routed lookup.  Calling `erase.lookup` first
reconstructed the entire logical tree on every point operation; this version
follows the same single root-to-leaf path without allocating that shadow tree. -/
def Node.lookup (key : Nat) : Node Value → Option Value
  | .leaf _ entries => (entries.find? fun entry => entry.1 = key).map (·.2)
  | .branch2 _ left separator right =>
      if key < separator then left.lookup key else right.lookup key
  | .branch3 _ left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then left.lookup key
      else if key < secondSeparator then middle.lookup key
      else right.lookup key

theorem Node.lookup_eq_erase (node : Node Value) (key : Nat) :
    node.lookup key = node.erase.lookup key := by
  induction node with
  | leaf => rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [Node.lookup, Node.erase, RecursiveBPlusTree.Node.lookup]
      split <;> assumption
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [Node.lookup, Node.erase, RecursiveBPlusTree.Node.lookup]
      split
      next => exact leftInduction
      next => split <;> assumption

/-- Greatest entry by right-spine descent, again without allocating erasure. -/
def Node.last? : Node Value → Option (PagedBTree.Entry Value)
  | .leaf _ entries => entries.getLast?
  | .branch2 _ left _ right => right.last?.or left.last?
  | .branch3 _ left _ middle _ right =>
      right.last?.or (middle.last?.or left.last?)

theorem Node.last?_eq_erase (node : Node Value) :
    node.last? = node.erase.last? := by
  induction node with
  | leaf => rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp [Node.last?, Node.erase, RecursiveBPlusTree.Node.last?,
        leftInduction, rightInduction]
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp [Node.last?, Node.erase, RecursiveBPlusTree.Node.last?,
        leftInduction, middleInduction, rightInduction]

def Node.pageIds : Node Value → List PageId
  | .leaf pageId _ => [pageId]
  | .branch2 pageId left _ right => pageId :: left.pageIds ++ right.pageIds
  | .branch3 pageId left _ middle _ right =>
      pageId :: left.pageIds ++ middle.pageIds ++ right.pageIds

theorem Node.pageIds_length (node : Node Value) :
    node.pageIds.length = node.erase.pageCount := by
  induction node with
  | leaf => rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp [Node.pageIds, Node.erase, RecursiveBPlusTree.Node.pageCount,
        leftInduction, rightInduction]
      <;> omega
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp [Node.pageIds, Node.erase, RecursiveBPlusTree.Node.pageCount,
        leftInduction, middleInduction, rightInduction]
      <;> omega

@[simp] theorem Node.rootId_mem_pageIds (node : Node Value) :
    node.rootId ∈ node.pageIds := by
  cases node <;> simp [Node.rootId, Node.pageIds]

def Node.setRootId (pageId : PageId) : Node Value → Node Value
  | .leaf _ entries => .leaf pageId entries
  | .branch2 _ left separator right => .branch2 pageId left separator right
  | .branch3 _ left firstSeparator middle secondSeparator right =>
      .branch3 pageId left firstSeparator middle secondSeparator right

@[simp] theorem Node.rootId_setRootId (node : Node Value) (pageId : PageId) :
    (node.setRootId pageId).rootId = pageId := by
  cases node <;> rfl

@[simp] theorem Node.erase_setRootId (node : Node Value) (pageId : PageId) :
    (node.setRootId pageId).erase = node.erase := by
  cases node <;> rfl

inductive InsertResult (Value : Type) where
  | done (node : Node Value)
  | split (left : Node Value) (separator : Nat) (right : Node Value)

def InsertResult.erase : InsertResult Value →
    RecursiveBPlusTree.InsertResult Value
  | .done node => .done node.erase
  | .split left separator right => .split left.erase separator right.erase

/-- Local page insertion.  Existing nodes keep their page IDs.  A leaf split
allocates one page; an interior split allocates one page after the recursive
child update.  The returned `nextPage` is therefore also an executable account
of allocation work. -/
def Node.insertStep (nextPage key : Nat) (value : Value) :
    Node Value → InsertResult Value × Nat
  | .leaf pageId entries =>
      match PagedBTree.orderedInsert key value entries with
      | [first, second, third] =>
          (.split (.leaf pageId [first]) second.1
            (.leaf nextPage [second, third]), nextPage + 1)
      | updated => (.done (.leaf pageId updated), nextPage)
  | .branch2 pageId left separator right =>
      if key < separator then
        let (result, nextPage) := left.insertStep nextPage key value
        match result with
        | .done updated =>
            (.done (.branch2 pageId updated separator right), nextPage)
        | .split first promoted second =>
            (.done (.branch3 pageId first promoted second separator right),
              nextPage)
      else
        let (result, nextPage) := right.insertStep nextPage key value
        match result with
        | .done updated =>
            (.done (.branch2 pageId left separator updated), nextPage)
        | .split first promoted second =>
            (.done (.branch3 pageId left separator first promoted second),
              nextPage)
  | .branch3 pageId left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then
        let (result, nextPage) := left.insertStep nextPage key value
        match result with
        | .done updated =>
            (.done (.branch3 pageId updated firstSeparator middle
              secondSeparator right), nextPage)
        | .split first promoted second =>
            (.split (.branch2 pageId first promoted second) firstSeparator
              (.branch2 nextPage middle secondSeparator right), nextPage + 1)
      else if key < secondSeparator then
        let (result, nextPage) := middle.insertStep nextPage key value
        match result with
        | .done updated =>
            (.done (.branch3 pageId left firstSeparator updated
              secondSeparator right), nextPage)
        | .split first promoted second =>
            (.split (.branch2 pageId left firstSeparator first) promoted
              (.branch2 nextPage second secondSeparator right), nextPage + 1)
      else
        let (result, nextPage) := right.insertStep nextPage key value
        match result with
        | .done updated =>
            (.done (.branch3 pageId left firstSeparator middle
              secondSeparator updated), nextPage)
        | .split first promoted second =>
            (.split (.branch2 pageId left firstSeparator middle) secondSeparator
              (.branch2 nextPage first promoted second), nextPage + 1)

/-- Page-aware insertion keeps the root page stable.  When the root itself
splits, its left result is moved to one fresh page and the old root ID becomes
the new interior root. -/
def Node.insert (nextPage key : Nat) (value : Value) (node : Node Value) :
    Node Value × Nat :=
  match node.insertStep nextPage key value with
  | (.done updated, nextPage) => (updated, nextPage)
  | (.split left separator right, nextPage) =>
      (.branch2 node.rootId (left.setRootId nextPage) separator right,
        nextPage + 1)

/-- Two identified trees agree away from the one search path selected by
`key`.  Every sibling, separator, and page identity off that path is shared
definitionally. -/
inductive Node.PathAgrees (key : Nat) : Node Value → Node Value → Prop where
  | leaf (pageId : PageId) (before after : List (PagedBTree.Entry Value)) :
      PathAgrees key (.leaf pageId before) (.leaf pageId after)
  | branch2Left (pageId : PageId) (before after : Node Value)
      (separator : Nat) (right : Node Value)
      (route : key < separator) (child : PathAgrees key before after) :
      PathAgrees key (.branch2 pageId before separator right)
        (.branch2 pageId after separator right)
  | branch2Right (pageId : PageId) (left : Node Value) (separator : Nat)
      (before after : Node Value) (route : ¬key < separator)
      (child : PathAgrees key before after) :
      PathAgrees key (.branch2 pageId left separator before)
        (.branch2 pageId left separator after)
  | branch3Left (pageId : PageId) (before after : Node Value)
      (firstSeparator : Nat) (middle : Node Value) (secondSeparator : Nat)
      (right : Node Value) (route : key < firstSeparator)
      (child : PathAgrees key before after) :
      PathAgrees key
        (.branch3 pageId before firstSeparator middle secondSeparator right)
        (.branch3 pageId after firstSeparator middle secondSeparator right)
  | branch3Middle (pageId : PageId) (left : Node Value)
      (firstSeparator : Nat) (before after : Node Value)
      (secondSeparator : Nat) (right : Node Value)
      (leftRoute : ¬key < firstSeparator) (route : key < secondSeparator)
      (child : PathAgrees key before after) :
      PathAgrees key
        (.branch3 pageId left firstSeparator before secondSeparator right)
        (.branch3 pageId left firstSeparator after secondSeparator right)
  | branch3Right (pageId : PageId) (left : Node Value)
      (firstSeparator : Nat) (middle : Node Value) (secondSeparator : Nat)
      (before after : Node Value) (leftRoute : ¬key < firstSeparator)
      (middleRoute : ¬key < secondSeparator)
      (child : PathAgrees key before after) :
      PathAgrees key
        (.branch3 pageId left firstSeparator middle secondSeparator before)
        (.branch3 pageId left firstSeparator middle secondSeparator after)

/-- Updating one search path without allocating preserves the complete page
identity set, not merely the root identity.  This is the physical frame fact
used to keep separately allocated SQLite index runs disjoint from table-page
updates. -/
theorem Node.PathAgrees.pageIds_eq {key : Nat} {before after : Node Value}
    (agrees : Node.PathAgrees key before after) :
    after.pageIds = before.pageIds := by
  induction agrees <;> simp_all [Node.pageIds]

/-- A no-allocation path update preserves tree height as well as page
identity.  This lets decoder fuel bounds transport from the validated old
tree without recounting the post-state tree. -/
theorem Node.PathAgrees.height_eq {key : Nat} {before after : Node Value}
    (agrees : Node.PathAgrees key before after) :
    after.erase.height = before.erase.height := by
  induction agrees <;>
    simp_all [Node.erase, RecursiveBPlusTree.Node.height]

/-- Allocation is monotone: insertion never moves the high-water mark
backwards. -/
theorem Node.insertStep_nextPage_le (node : Node Value)
    (nextPage key : Nat) (value : Value) :
    nextPage ≤ (node.insertStep nextPage key value).2 := by
  induction node generalizing nextPage with
  | leaf pageId entries =>
      simp only [Node.insertStep]
      generalize inserted : PagedBTree.orderedInsert key value entries = result
      cases result with
      | nil => simp
      | cons first rest =>
        cases rest with
        | nil => simp
        | cons second rest =>
          cases rest with
          | nil => simp
          | cons third rest =>
            cases rest <;> simp
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [Node.insertStep]
      split
      next =>
        cases result : left.insertStep nextPage key value with
        | mk outcome nextPage' =>
          have bound := leftInduction nextPage
          rw [result] at bound
          cases outcome <;> exact bound
      next =>
        cases result : right.insertStep nextPage key value with
        | mk outcome nextPage' =>
          have bound := rightInduction nextPage
          rw [result] at bound
          cases outcome <;> exact bound
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [Node.insertStep]
      split
      next =>
        cases result : left.insertStep nextPage key value with
        | mk outcome nextPage' =>
          have bound := leftInduction nextPage
          rw [result] at bound
          cases outcome <;> simp [result] <;> omega
      next =>
        split
        next =>
          cases result : middle.insertStep nextPage key value with
          | mk outcome nextPage' =>
            have bound := middleInduction nextPage
            rw [result] at bound
            cases outcome <;> simp [result] <;> omega
        next =>
          cases result : right.insertStep nextPage key value with
          | mk outcome nextPage' =>
            have bound := rightInduction nextPage
            rw [result] at bound
            cases outcome <;> simp [result] <;> omega

theorem Node.insert_nextPage_le (node : Node Value)
    (nextPage key : Nat) (value : Value) :
    nextPage ≤ (node.insert nextPage key value).2 := by
  unfold Node.insert
  cases result : node.insertStep nextPage key value with
  | mk outcome nextPage' =>
      have bound := node.insertStep_nextPage_le nextPage key value
      rw [result] at bound
      cases outcome <;> simp [result] <;> omega

/-- Every split advances the page high-water mark. -/
theorem Node.insertStep_split_allocates (node : Node Value)
    (nextPage key : Nat) (value : Value) (left : Node Value)
    (separator : Nat) (right : Node Value) (nextPage' : Nat)
    (success : node.insertStep nextPage key value =
      (.split left separator right, nextPage')) :
    nextPage < nextPage' := by
  induction node generalizing nextPage left separator right nextPage' with
  | leaf pageId entries =>
      unfold Node.insertStep at success
      generalize contentsEq : PagedBTree.orderedInsert key value entries =
        contents at success
      cases contents with
      | nil => cases success
      | cons first rest =>
        cases rest with
        | nil => cases success
        | cons second rest =>
          cases rest with
          | nil => cases success
          | cons third rest =>
            cases rest with
            | nil => cases success; omega
            | cons fourth rest => cases success
  | branch2 pageId oldLeft oldSeparator oldRight leftInduction rightInduction =>
      simp only [Node.insertStep] at success
      split at success <;>
        first
        | cases childResult : oldLeft.insertStep nextPage key value <;>
            rename_i outcome childNext <;> rw [childResult] at success <;>
            cases outcome <;> cases success
        | cases childResult : oldRight.insertStep nextPage key value <;>
            rename_i outcome childNext <;> rw [childResult] at success <;>
            cases outcome <;> cases success
  | branch3 pageId oldLeft firstSeparator oldMiddle secondSeparator oldRight
      leftInduction middleInduction rightInduction =>
      simp only [Node.insertStep] at success
      split at success
      next =>
        cases childResult : oldLeft.insertStep nextPage key value with
        | mk outcome childNext =>
          rw [childResult] at success
          cases outcome with
          | done updated => cases success
          | split first promoted second =>
            have allocated := leftInduction nextPage first promoted second
              childNext childResult
            cases success
            omega
      next =>
        split at success
        next =>
          cases childResult : oldMiddle.insertStep nextPage key value with
          | mk outcome childNext =>
            rw [childResult] at success
            cases outcome with
            | done updated => cases success
            | split first promoted second =>
              have allocated := middleInduction nextPage first promoted second
                childNext childResult
              cases success
              omega
        next =>
          cases childResult : oldRight.insertStep nextPage key value with
          | mk outcome childNext =>
            rw [childResult] at success
            cases outcome with
            | done updated => cases success
            | split first promoted second =>
              have allocated := rightInduction nextPage first promoted second
                childNext childResult
              cases success
              omega

end PersistentPageTree

end SQLeanite
