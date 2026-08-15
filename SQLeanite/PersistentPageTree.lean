import SQLeanite.RecursiveBPlusTree

namespace SQLeanite
namespace PersistentPageTree

open RecursiveBPlusTree

/-!
# Stable page identities for the recursive B+ tree

`RecursiveBPlusTree` proves the logical insertion and deletion algorithms.  This
module adds the piece a persistent database needs but a purely functional tree
does not: stable page identities.  The erasure map deliberately forgets only
those identities, so the executable page mutation and the previously proved
tree algorithm cannot silently diverge.
-/

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

/-- A successful no-allocation insertion changes exactly one search path. -/
theorem Node.insertStep_done_pathAgrees (node : Node Value)
    (nextPage key : Nat) (value : Value) (updated : Node Value)
    (success : node.insertStep nextPage key value = (.done updated, nextPage)) :
    Node.PathAgrees key node updated := by
  induction node generalizing nextPage updated with
  | leaf pageId entries =>
      unfold Node.insertStep at success
      generalize contentsEq : PagedBTree.orderedInsert key value entries =
        contents at success
      cases contents with
      | nil => cases success; exact .leaf pageId entries []
      | cons first rest =>
        cases rest with
        | nil => cases success; exact .leaf pageId entries [first]
        | cons second rest =>
          cases rest with
          | nil => cases success; exact .leaf pageId entries [first, second]
          | cons third rest =>
            cases rest with
            | nil => cases success
            | cons fourth rest =>
              cases success
              exact .leaf pageId entries
                (first :: second :: third :: fourth :: rest)
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [Node.insertStep] at success
      split at success
      next route =>
        cases childResult : left.insertStep nextPage key value with
        | mk outcome childNext =>
          rw [childResult] at success
          cases outcome with
          | done child =>
            have childNextEq : childNext = nextPage :=
              congrArg Prod.snd success
            have childPath := leftInduction nextPage child (by
              simpa [childNextEq] using childResult)
            cases success
            exact .branch2Left pageId left child separator right route
              childPath
          | split first promoted second =>
            have allocated := left.insertStep_split_allocates nextPage key value
              first promoted second childNext childResult
            have childNextEq : childNext = nextPage :=
              congrArg Prod.snd success
            omega
      next route =>
        cases childResult : right.insertStep nextPage key value with
        | mk outcome childNext =>
          rw [childResult] at success
          cases outcome with
          | done child =>
            have childNextEq : childNext = nextPage :=
              congrArg Prod.snd success
            have childPath := rightInduction nextPage child (by
              simpa [childNextEq] using childResult)
            cases success
            exact .branch2Right pageId left separator right child route
              childPath
          | split first promoted second =>
            have allocated := right.insertStep_split_allocates nextPage key value
              first promoted second childNext childResult
            have childNextEq : childNext = nextPage :=
              congrArg Prod.snd success
            omega
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [Node.insertStep] at success
      split at success
      next leftRoute =>
        cases childResult : left.insertStep nextPage key value with
        | mk outcome childNext =>
          rw [childResult] at success
          cases outcome with
          | done child =>
            have childNextEq : childNext = nextPage :=
              congrArg Prod.snd success
            have childPath := leftInduction nextPage child (by
              simpa [childNextEq] using childResult)
            cases success
            exact .branch3Left pageId left child firstSeparator middle
              secondSeparator right leftRoute
              childPath
          | split first promoted second => cases success
      next leftRoute =>
        split at success
        next middleRoute =>
          cases childResult : middle.insertStep nextPage key value with
          | mk outcome childNext =>
            rw [childResult] at success
            cases outcome with
            | done child =>
              have childNextEq : childNext = nextPage :=
                congrArg Prod.snd success
              have childPath := middleInduction nextPage child (by
                simpa [childNextEq] using childResult)
              cases success
              exact .branch3Middle pageId left firstSeparator middle child
                secondSeparator right leftRoute middleRoute
                childPath
            | split first promoted second => cases success
        next middleRoute =>
          cases childResult : right.insertStep nextPage key value with
          | mk outcome childNext =>
            rw [childResult] at success
            cases outcome with
            | done child =>
              have childNextEq : childNext = nextPage :=
                congrArg Prod.snd success
              have childPath := rightInduction nextPage child (by
                simpa [childNextEq] using childResult)
              cases success
              exact .branch3Right pageId left firstSeparator middle
                secondSeparator right child leftRoute middleRoute
                childPath
            | split first promoted second => cases success

theorem Node.insert_pathAgrees_of_noAllocation (node : Node Value)
    (nextPage key : Nat) (value : Value)
    (noAllocation : (node.insert nextPage key value).2 = nextPage) :
    Node.PathAgrees key node (node.insert nextPage key value).1 := by
  unfold Node.insert at noAllocation ⊢
  cases stepResult : node.insertStep nextPage key value with
  | mk outcome nextPage' =>
    rw [stepResult] at noAllocation
    cases outcome with
    | done updated =>
      change nextPage' = nextPage at noAllocation
      change Node.PathAgrees key node updated
      subst nextPage'
      exact node.insertStep_done_pathAgrees nextPage key value updated stepResult
    | split left separator right =>
      change nextPage' + 1 = nextPage at noAllocation
      have allocated := node.insertStep_split_allocates nextPage key value left
        separator right nextPage' stepResult
      omega

theorem Node.insertStep_done_rootId (node : Node Value) (nextPage key : Nat)
    (value : Value) (updated : Node Value) (nextPage' : Nat)
    (success : node.insertStep nextPage key value = (.done updated, nextPage')) :
    updated.rootId = node.rootId := by
  induction node generalizing nextPage updated nextPage' with
  | leaf pageId entries =>
      unfold Node.insertStep at success
      generalize contentsEq : PagedBTree.orderedInsert key value entries = contents at success
      cases contents with
      | nil => cases success; rfl
      | cons first rest =>
          cases rest with
          | nil => cases success; rfl
          | cons second rest =>
              cases rest with
              | nil => cases success; rfl
              | cons third rest =>
                  cases rest with
                  | nil => cases success
                  | cons fourth rest => cases success; rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [Node.insertStep] at success
      split at success
      next =>
        cases childResult : left.insertStep nextPage key value with
        | mk result childNext =>
            rw [childResult] at success
            cases result <;> cases success <;> rfl
      next =>
        cases childResult : right.insertStep nextPage key value with
        | mk result childNext =>
            rw [childResult] at success
            cases result <;> cases success <;> rfl
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [Node.insertStep] at success
      split at success
      next =>
        cases childResult : left.insertStep nextPage key value with
        | mk result childNext =>
            rw [childResult] at success
            cases result <;> cases success <;> rfl
      next =>
        split at success
        next =>
          cases childResult : middle.insertStep nextPage key value with
          | mk result childNext =>
              rw [childResult] at success
              cases result <;> cases success <;> rfl
        next =>
          cases childResult : right.insertStep nextPage key value with
          | mk result childNext =>
              rw [childResult] at success
              cases result <;> cases success <;> rfl

theorem Node.insert_rootId (node : Node Value) (nextPage key : Nat)
    (value : Value) :
    (node.insert nextPage key value).1.rootId = node.rootId := by
  unfold Node.insert
  cases stepResult : node.insertStep nextPage key value with
  | mk result nextPage' =>
      cases result with
      | done updated =>
          exact node.insertStep_done_rootId nextPage key value updated nextPage'
            stepResult
      | split => rfl

theorem Node.insertStep_erases (node : Node Value) (nextPage key : Nat)
    (value : Value) :
    (node.insertStep nextPage key value).1.erase =
      node.erase.insertStep key value := by
  induction node with
  | leaf pageId entries =>
      simp only [Node.insertStep, Node.erase,
        RecursiveBPlusTree.Node.insertStep]
      generalize updatedEq : PagedBTree.orderedInsert key value entries = updated
      cases updated with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest =>
                  cases rest <;> rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp only [Node.insertStep, Node.erase,
        RecursiveBPlusTree.Node.insertStep]
      split
      next =>
        rw [← leftInduction]
        cases left.insertStep nextPage key value <;>
          rename_i result nextPage' <;> cases result <;> rfl
      next =>
        rw [← rightInduction]
        cases right.insertStep nextPage key value <;>
          rename_i result nextPage' <;> cases result <;> rfl
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [Node.insertStep, Node.erase,
        RecursiveBPlusTree.Node.insertStep]
      split
      next =>
        rw [← leftInduction]
        cases left.insertStep nextPage key value <;>
          rename_i result nextPage' <;> cases result <;> rfl
      next =>
        split
        next =>
          rw [← middleInduction]
          cases middle.insertStep nextPage key value <;>
            rename_i result nextPage' <;> cases result <;> rfl
        next =>
          rw [← rightInduction]
          cases right.insertStep nextPage key value <;>
            rename_i result nextPage' <;> cases result <;> rfl

theorem Node.insert_erases (node : Node Value) (nextPage key : Nat)
    (value : Value) :
    (node.insert nextPage key value).1.erase = node.erase.insert key value := by
  unfold Node.insert RecursiveBPlusTree.Node.insert
  have step := node.insertStep_erases nextPage key value
  cases stepResult : node.insertStep nextPage key value with
  | mk outcome nextPage' =>
      rw [stepResult] at step
      cases outcome with
      | done updated =>
          simp only [InsertResult.erase] at step
          rw [← step]
      | split left separator right =>
          simp only [InsertResult.erase] at step
          rw [← step]
          simp [stepResult, Node.erase]

/-- A proof-carrying persistent tree.  `nextPage` is a high-water mark;
`rootValid` is inherited from the verified logical tree through erasure. -/
structure Store (Value : Type) where
  root : Node Value
  nextPage : Nat
  rootValid : root.erase.RootValid

def Store.insert (store : Store Value) (key : Nat) (value : Value) : Store Value :=
  let inserted := store.root.insert store.nextPage key value
  { root := inserted.1
    nextPage := inserted.2
    rootValid := by
      rw [store.root.insert_erases store.nextPage key value]
      exact store.root.erase.insert_rootValid store.rootValid key value }

@[simp] theorem Store.insert_rootId (store : Store Value) (key : Nat)
    (value : Value) :
    (store.insert key value).root.rootId = store.root.rootId := by
  unfold Store.insert
  exact store.root.insert_rootId store.nextPage key value

theorem Store.insert_toList (store : Store Value) (key : Nat) (value : Value) :
    (store.insert key value).root.erase.toList =
      PagedBTree.orderedInsert key value store.root.erase.toList := by
  unfold Store.insert
  simp only
  rw [store.root.insert_erases]
  exact store.root.erase.toList_insert_rootValid store.rootValid key value

/-- The logical representation relation used by the database layer. -/
def Store.Represents (store : Store Value)
    (entries : List (PagedBTree.Entry Value)) : Prop :=
  store.root.erase.toList = entries

theorem Store.insert_represents (store : Store Value)
    (entries : List (PagedBTree.Entry Value)) (represented : store.Represents entries)
    (key : Nat) (value : Value) :
    (store.insert key value).Represents
      (PagedBTree.orderedInsert key value entries) := by
  unfold Store.Represents at represented ⊢
  rw [Store.insert_toList, represented]

/-- Relabel physical identities without changing the logical tree.  This is
used when a delete-then-insert mutation releases enough old pages to house all
nodes introduced by the insertion: the new nodes consume those released IDs
instead of extending the file past later index roots. -/
def replacementPageId (replacements : List (PageId × PageId))
    (pageId : PageId) : PageId :=
  match replacements.find? (fun replacement => replacement.1 == pageId) with
  | some replacement => replacement.2
  | none => pageId

theorem replacementPageId_range_zip_of_lt (firstFresh count pageId : Nat)
    (freed : List PageId) (old : pageId < firstFresh) :
    replacementPageId
      ((List.range' firstFresh count).zip (freed.take count)) pageId = pageId := by
  unfold replacementPageId
  cases found : ((List.range' firstFresh count).zip (freed.take count)).find?
      (fun replacement => replacement.1 == pageId) with
  | none => rfl
  | some replacement =>
      have selected := List.find?_some found
      have member := List.mem_of_find?_eq_some found
      have firstMember :=
        (List.of_mem_zip member).1
      simp only [beq_iff_eq] at selected
      have lower := (List.mem_range'_1.mp firstMember).1
      omega

def Node.relabelPageIds (replacements : List (PageId × PageId)) :
    Node Value → Node Value
  | .leaf pageId entries => .leaf (replacementPageId replacements pageId) entries
  | .branch2 pageId left separator right =>
      .branch2 (replacementPageId replacements pageId)
        (left.relabelPageIds replacements) separator
        (right.relabelPageIds replacements)
  | .branch3 pageId left firstSeparator middle secondSeparator right =>
      .branch3 (replacementPageId replacements pageId)
        (left.relabelPageIds replacements) firstSeparator
        (middle.relabelPageIds replacements) secondSeparator
        (right.relabelPageIds replacements)

@[simp] theorem Node.relabelPageIds_erase (node : Node Value)
    (replacements : List (PageId × PageId)) :
    (node.relabelPageIds replacements).erase = node.erase := by
  induction node with
  | leaf => rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      simp [Node.relabelPageIds, Node.erase, leftInduction, rightInduction]
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp [Node.relabelPageIds, Node.erase, leftInduction, middleInduction,
        rightInduction]

theorem Node.relabelPageIds_rootId_range_zip_of_lt
    (node : Node Value) (firstFresh count : Nat) (freed : List PageId)
    (old : node.rootId < firstFresh) :
    (node.relabelPageIds
      ((List.range' firstFresh count).zip (freed.take count))).rootId =
        node.rootId := by
  cases node <;> simp only [Node.relabelPageIds, Node.rootId] <;>
    apply replacementPageId_range_zip_of_lt <;>
    simpa only [Node.rootId] using old

/-- Recycle a prefix of `freed` for every identity allocated at or above
`firstFresh`.  Success resets the high-water mark because no fresh identity
survives; unused released pages are returned to the caller's freelist. -/
def Store.reuseFresh? (store : Store Value) (firstFresh : Nat)
    (freed : List PageId) : Option (Store Value × List PageId) :=
  if ordered : firstFresh ≤ store.nextPage then
    let count := store.nextPage - firstFresh
    if enough : count ≤ freed.length then
      let replacements := (List.range' firstFresh count).zip (freed.take count)
      let root := store.root.relabelPageIds replacements
      some ({
        root
        nextPage := firstFresh
        rootValid := by
          dsimp only [root]
          rw [Node.relabelPageIds_erase]
          exact store.rootValid }, freed.drop count)
    else none
  else none

theorem Store.reuseFresh?_toList {store reused : Store Value}
    {firstFresh : Nat} {freed remaining : List PageId}
    (success : store.reuseFresh? firstFresh freed = some (reused, remaining)) :
    reused.root.erase.toList = store.root.erase.toList := by
  unfold Store.reuseFresh? at success
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      cases Option.some.inj success
      simp
    next => contradiction
  next => contradiction

theorem Store.reuseFresh?_rootId {store reused : Store Value}
    {firstFresh : Nat} {freed remaining : List PageId}
    (old : store.root.rootId < firstFresh)
    (success : store.reuseFresh? firstFresh freed = some (reused, remaining)) :
    reused.root.rootId = store.root.rootId := by
  unfold Store.reuseFresh? at success
  split at success
  next =>
    dsimp only at success
    split at success
    next =>
      injection success with equal
      cases equal
      exact store.root.relabelPageIds_rootId_range_zip_of_lt firstFresh
        (store.nextPage - firstFresh) freed old
    next => contradiction
  next => contradiction

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

/-! ## Stable-identity deletion

The logical 2-3 tree already implements borrow, merge, underflow propagation,
and root shrink.  The following algorithm is the same state machine with page
identities threaded through every constructor.  Parent IDs remain parent IDs;
an absorbed interior page is returned in the freed-page list. -/

inductive DeleteResult (Value : Type) where
  | done (node : Node Value) (freed : List PageId)
  | underflow (node : Node Value) (freed : List PageId)
  | empty (freed : List PageId)

/-- Repairing an interior underflow can promote the underflow node's page to a
new parent.  The child then needs the page released by the lower-level merge;
reusing it here preserves page count and, critically, prevents parent and child
from sharing one page ID.  The empty case is retained for totality and is
rejected later by the allocation validator if an impossible repair reaches it. -/
private def reuseFreedRoot (under : Node Value) :
    List PageId → Node Value × List PageId
  | [] => (under, [])
  | pageId :: freed => (under.setRootId pageId, freed)

@[simp] private theorem reuseFreedRoot_erase (under : Node Value)
    (freed : List PageId) :
    (reuseFreedRoot under freed).1.erase = under.erase := by
  cases freed <;> simp [reuseFreedRoot]

def DeleteResult.erase : DeleteResult Value →
    RecursiveBPlusTree.DeleteResult Value
  | .done node _ => .done node.erase
  | .underflow node _ => .underflow node.erase
  | .empty _ => .empty

private def repairTwoLeft (pageId : PageId) (separator : Nat)
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

private def repairTwoRight (pageId : PageId) (left : Node Value)
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

private def repairThreeLeft (pageId : PageId) (firstSeparator : Nat)
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

private def repairThreeMiddle (pageId : PageId) (left : Node Value)
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

private def repairThreeRight (pageId : PageId) (left : Node Value)
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
private def DeleteResult.PreservesRoot (pageId : PageId) :
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
