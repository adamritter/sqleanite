import SQLeanite.PersistentPageTree.PageId
import SQLeanite.RecursiveBPlusTree.NodeInsertStepValid

namespace SQLeanite
namespace PersistentPageTree
open RecursiveBPlusTree

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

theorem Node.insert_pageIds_of_noAllocation (node : Node Value)
    (nextPage key : Nat) (value : Value)
    (noAllocation : (node.insert nextPage key value).2 = nextPage) :
    (node.insert nextPage key value).1.pageIds = node.pageIds :=
  (node.insert_pathAgrees_of_noAllocation nextPage key value
    noAllocation).pageIds_eq

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

theorem Store.insert_height_of_noAllocation (store : Store Value)
    (key : Nat) (value : Value)
    (noAllocation : (store.insert key value).nextPage = store.nextPage) :
    (store.insert key value).root.erase.height = store.root.erase.height := by
  exact (store.root.insert_pathAgrees_of_noAllocation store.nextPage key value
    (by simpa [Store.insert] using noAllocation)).height_eq

@[simp] theorem Store.insert_rootId (store : Store Value) (key : Nat)
    (value : Value) :
    (store.insert key value).root.rootId = store.root.rootId := by
  unfold Store.insert
  exact store.root.insert_rootId store.nextPage key value

theorem Store.insert_pageIds_of_noAllocation (store : Store Value)
    (key : Nat) (value : Value)
    (noAllocation : (store.insert key value).nextPage = store.nextPage) :
    (store.insert key value).root.pageIds = store.root.pageIds := by
  unfold Store.insert at noAllocation ⊢
  exact store.root.insert_pageIds_of_noAllocation store.nextPage key value
    noAllocation

theorem Store.nextPage_le_insert (store : Store Value)
    (key : Nat) (value : Value) :
    store.nextPage ≤ (store.insert key value).nextPage := by
  unfold Store.insert
  exact store.root.insert_nextPage_le store.nextPage key value

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

end PersistentPageTree

end SQLeanite
