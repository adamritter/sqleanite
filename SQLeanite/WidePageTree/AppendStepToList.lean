import SQLeanite.WidePageTree.NumberedBranchesRootNePendingBytePage

namespace SQLeanite
namespace WidePageTree

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
