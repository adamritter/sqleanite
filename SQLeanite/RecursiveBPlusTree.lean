import SQLeanite.PagedBTree

namespace SQLeanite
namespace RecursiveBPlusTree

abbrev Entry (Value : Type) := PagedBTree.Entry Value

/-- A capacity-two 2-3 B+ tree. Values live only in leaves; interior separator
keys route descent. Every branch constructor is an actual physical node, so
height is unbounded and a split is propagated one level at a time. -/
inductive Node (Value : Type) where
  | leaf (entries : List (Entry Value))
  | branch2 (left : Node Value) (separator : Nat) (right : Node Value)
  | branch3 (left : Node Value) (firstSeparator : Nat)
      (middle : Node Value) (secondSeparator : Nat) (right : Node Value)
  deriving Repr, DecidableEq

def Node.toList : Node Value → List (Entry Value)
  | .leaf entries => entries
  | .branch2 left _ right => left.toList ++ right.toList
  | .branch3 left _ middle _ right =>
      left.toList ++ middle.toList ++ right.toList

/-- Descend only through rightmost children to recover the greatest entry.
The fallback handles arbitrary malformed/empty child shapes too, so its
equation with the abstraction does not require a validity premise. -/
def Node.last? : Node Value → Option (Entry Value)
  | .leaf entries => entries.getLast?
  | .branch2 left _ right => right.last?.or left.last?
  | .branch3 left _ middle _ right =>
      right.last?.or (middle.last?.or left.last?)

theorem Node.last?_eq_getLast? (node : Node Value) :
    node.last? = node.toList.getLast? := by
  induction node with
  | leaf entries => rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp [Node.last?, Node.toList, leftInduction, rightInduction]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp [Node.last?, Node.toList, leftInduction, middleInduction,
        rightInduction, Option.or_assoc]

def Node.height : Node Value → Nat
  | .leaf _ => 0
  | .branch2 left _ _ => left.height + 1
  | .branch3 left _ _ _ _ => left.height + 1

def Node.pageCount : Node Value → Nat
  | .leaf _ => 1
  | .branch2 left _ right => 1 + left.pageCount + right.pageCount
  | .branch3 left _ middle _ right =>
      1 + left.pageCount + middle.pageCount + right.pageCount

theorem Node.pageCount_pos (node : Node Value) : 0 < node.pageCount := by
  cases node <;> simp only [Node.pageCount] <;> omega

theorem Node.height_lt_pageCount (node : Node Value) :
    node.height < node.pageCount := by
  induction node with
  | leaf => simp [Node.height, Node.pageCount]
  | branch2 left separator right leftInduction rightInduction =>
      simp only [Node.height, Node.pageCount]
      have rightPositive := right.pageCount_pos
      omega
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [Node.height, Node.pageCount]
      have middlePositive := middle.pageCount_pos
      have rightPositive := right.pageCount_pos
      omega

def Node.lookup (key : Nat) : Node Value → Option Value
  | .leaf entries => (entries.find? fun entry => entry.1 = key).map (·.2)
  | .branch2 left separator right =>
      if key < separator then left.lookup key else right.lookup key
  | .branch3 left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then left.lookup key
      else if key < secondSeparator then middle.lookup key
      else right.lookup key

/-- A routed lookup never invents an entry.  This is deliberately stated over
the tree abstraction rather than its shape so callers can discharge defensive
runtime checks from the representation theorem. -/
theorem Node.lookup_some_mem {node : Node Value} {key : Nat} {value : Value}
    (found : node.lookup key = some value) : (key, value) ∈ node.toList := by
  induction node with
  | leaf entries =>
      simp only [Node.lookup] at found
      cases search : entries.find? (fun entry => entry.1 = key) with
      | none => simp [search] at found
      | some entry =>
          rw [search] at found
          simp only [Option.map, Option.some.injEq] at found
          change entry.2 = value at found
          have keyMatches := List.find?_some search
          have member := List.mem_of_find?_eq_some search
          cases entry with
          | mk entryKey entryValue =>
              simp only at keyMatches found member
              have keyEqual : entryKey = key := by
                simpa only [decide_eq_true_eq] using keyMatches
              subst key
              subst entryValue
              exact member
  | branch2 left separator right leftInduction rightInduction =>
      simp only [Node.lookup] at found
      split at found
      next => exact List.mem_append_left _ (leftInduction found)
      next => exact List.mem_append_right _ (rightInduction found)
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [Node.lookup] at found
      split at found
      next =>
        exact List.mem_append_left _
          (List.mem_append_left _ (leftInduction found))
      next =>
        split at found
        next =>
          exact List.mem_append_left _
            (List.mem_append_right _ (middleInduction found))
        next => exact List.mem_append_right _ (rightInduction found)

private theorem findKey?_eq_some_of_mem
    {entries : List (Entry Value)} {key : Nat} {value : Value}
    (sorted : PagedBTree.KeysStrictlySorted entries)
    (member : (key, value) ∈ entries) :
    entries.find? (fun entry => entry.1 = key) = some (key, value) := by
  induction entries with
  | nil => contradiction
  | cons entry entries induction =>
      simp only [PagedBTree.KeysStrictlySorted, List.pairwise_cons] at sorted
      rcases List.mem_cons.mp member with equal | tailMember
      · subst entry
        simp
      · have before := sorted.1 (key, value) tailMember
        have different : entry.1 ≠ key := Nat.ne_of_lt before
        rw [List.find?_cons_of_neg (by simpa using different)]
        exact induction sorted.2 tailMember

def Node.range (lower upper : Nat) (node : Node Value) : List (Entry Value) :=
  node.toList.filter fun entry => decide (lower ≤ entry.1 ∧ entry.1 < upper)

/-- Routed range traversal. Subtrees whose separator interval cannot intersect
`[lower, upper)` are not visited; qualifying leaves retain their physical
order. -/
def Node.rangeScan (lower upper : Nat) : Node Value → List (Entry Value)
  | .leaf entries =>
      entries.filter fun entry => decide (lower ≤ entry.1 ∧ entry.1 < upper)
  | .branch2 left separator right =>
      (if lower < separator then left.rangeScan lower upper else []) ++
      (if separator < upper then right.rangeScan lower upper else [])
  | .branch3 left firstSeparator middle secondSeparator right =>
      (if lower < firstSeparator then left.rangeScan lower upper else []) ++
      (if lower < secondSeparator ∧ firstSeparator < upper then
        middle.rangeScan lower upper else []) ++
      (if secondSeparator < upper then right.rangeScan lower upper else [])

inductive InsertResult (Value : Type) where
  | done (node : Node Value)
  | split (left : Node Value) (separator : Nat) (right : Node Value)

def InsertResult.toList : InsertResult Value → List (Entry Value)
  | .done node => node.toList
  | .split left _ right => left.toList ++ right.toList

def Node.Routes : Node Value → Prop
  | .leaf _ => True
  | .branch2 left separator right =>
      left.Routes ∧ right.Routes ∧
      (∀ entry ∈ left.toList, entry.1 < separator) ∧
      (∀ entry ∈ right.toList, separator ≤ entry.1)
  | .branch3 left firstSeparator middle secondSeparator right =>
      left.Routes ∧ middle.Routes ∧ right.Routes ∧
      firstSeparator < secondSeparator ∧
      (∀ entry ∈ left.toList, entry.1 < firstSeparator) ∧
      (∀ entry ∈ middle.toList,
        firstSeparator ≤ entry.1 ∧ entry.1 < secondSeparator) ∧
      (∀ entry ∈ right.toList, secondSeparator ≤ entry.1)

/-- Structural B+ tree invariant: leaf occupancy is bounded and all children
of an interior page have the same height.  Root emptiness is permitted. -/
def Node.Balanced : Node Value → Prop
  | .leaf entries => entries.length ≤ 2
  | .branch2 left _ right =>
      left.Balanced ∧ right.Balanced ∧ left.height = right.height
  | .branch3 left _ middle _ right =>
      left.Balanced ∧ middle.Balanced ∧ right.Balanced ∧
      left.height = middle.height ∧ middle.height = right.height

def Node.checkBalanced : Node Value → Bool
  | .leaf entries => decide (entries.length ≤ 2)
  | .branch2 left _ right =>
      left.checkBalanced && right.checkBalanced && decide (left.height = right.height)
  | .branch3 left _ middle _ right =>
      left.checkBalanced && middle.checkBalanced && right.checkBalanced &&
        decide (left.height = middle.height) && decide (middle.height = right.height)

theorem Node.checkBalanced_iff (node : Node Value) :
    node.checkBalanced = true ↔ node.Balanced := by
  induction node with
  | leaf entries => simp [Node.checkBalanced, Node.Balanced]
  | branch2 left separator right leftInduction rightInduction =>
      simp [Node.checkBalanced, Node.Balanced, leftInduction, rightInduction,
        and_assoc]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp [Node.checkBalanced, Node.Balanced, leftInduction, middleInduction,
        rightInduction, and_assoc]

def InsertResult.BalancedAt (height : Nat) : InsertResult Value → Prop
  | .done node => node.Balanced ∧ node.height = height
  | .split left _ right =>
      left.Balanced ∧ right.Balanced ∧
      left.height = height ∧ right.height = height

/-- Non-root nodes are fully valid: every leaf is occupied and bounded, every
interior child is valid and at the same height, and separators route all keys
to disjoint intervals. -/
def Node.Valid : Node Value → Prop
  | .leaf entries =>
      entries ≠ [] ∧ PagedBTree.KeysStrictlySorted entries ∧ entries.length ≤ 2
  | .branch2 left separator right =>
      left.Valid ∧ right.Valid ∧ left.height = right.height ∧
      (∀ entry ∈ left.toList, entry.1 < separator) ∧
      (∀ entry ∈ right.toList, separator ≤ entry.1)
  | .branch3 left firstSeparator middle secondSeparator right =>
      left.Valid ∧ middle.Valid ∧ right.Valid ∧
      left.height = middle.height ∧ middle.height = right.height ∧
      firstSeparator < secondSeparator ∧
      (∀ entry ∈ left.toList, entry.1 < firstSeparator) ∧
      (∀ entry ∈ middle.toList,
        firstSeparator ≤ entry.1 ∧ entry.1 < secondSeparator) ∧
      (∀ entry ∈ right.toList, secondSeparator ≤ entry.1)

/-- The root additionally permits the unique empty-tree representation. -/
def Node.RootValid : Node Value → Prop
  | .leaf entries =>
      PagedBTree.KeysStrictlySorted entries ∧ entries.length ≤ 2
  | node => node.Valid

def checkKeysStrictlySorted : List (Entry Value) → Bool
  | [] => true
  | [_] => true
  | first :: second :: remaining =>
      decide (first.1 < second.1) &&
        checkKeysStrictlySorted (second :: remaining)

private theorem keyBefore_all_of_adjacent
    {first second : Entry Value} {remaining : List (Entry Value)}
    (head : first.1 < second.1)
    (tail : PagedBTree.KeysStrictlySorted (second :: remaining)) :
    ∀ entry ∈ second :: remaining, first.1 < entry.1 := by
  intro entry member
  rcases List.pairwise_cons.mp tail with ⟨secondBefore, _⟩
  simp only [List.mem_cons] at member
  rcases member with equal | later
  · simpa [equal] using head
  · exact Nat.lt_trans head (secondBefore entry later)

theorem checkKeysStrictlySorted_iff (entries : List (Entry Value)) :
    checkKeysStrictlySorted entries = true ↔
      PagedBTree.KeysStrictlySorted entries := by
  induction entries with
  | nil => simp [checkKeysStrictlySorted, PagedBTree.KeysStrictlySorted]
  | cons entry entries induction =>
      cases entries with
      | nil => simp [checkKeysStrictlySorted, PagedBTree.KeysStrictlySorted]
      | cons next remaining =>
          constructor
          · intro checked
            simp only [checkKeysStrictlySorted, Bool.and_eq_true,
              decide_eq_true_eq] at checked
            have tail := induction.mp checked.2
            exact List.pairwise_cons.mpr
              ⟨keyBefore_all_of_adjacent checked.1 tail, tail⟩
          · intro sorted
            rcases List.pairwise_cons.mp sorted with ⟨entryBefore, tail⟩
            simp only [checkKeysStrictlySorted, Bool.and_eq_true,
              decide_eq_true_eq]
            exact ⟨entryBefore next (by simp), induction.mpr tail⟩

def Node.checkValid : Node Value → Bool
  | .leaf entries =>
      !entries.isEmpty && checkKeysStrictlySorted entries &&
        decide (entries.length ≤ 2)
  | .branch2 left separator right =>
      left.checkValid && right.checkValid && decide (left.height = right.height) &&
        left.toList.all (fun entry => decide (entry.1 < separator)) &&
        right.toList.all (fun entry => decide (separator ≤ entry.1))
  | .branch3 left firstSeparator middle secondSeparator right =>
      left.checkValid && middle.checkValid && right.checkValid &&
        decide (left.height = middle.height) &&
        decide (middle.height = right.height) &&
        decide (firstSeparator < secondSeparator) &&
        left.toList.all (fun entry => decide (entry.1 < firstSeparator)) &&
        middle.toList.all (fun entry =>
          decide (firstSeparator ≤ entry.1 ∧ entry.1 < secondSeparator)) &&
        right.toList.all (fun entry => decide (secondSeparator ≤ entry.1))

def Node.checkRootValid : Node Value → Bool
  | .leaf entries =>
      checkKeysStrictlySorted entries &&
        decide (entries.length ≤ 2)
  | node => node.checkValid

theorem Node.checkValid_iff (node : Node Value) :
    node.checkValid = true ↔ node.Valid := by
  induction node with
  | leaf entries =>
      simp [Node.checkValid, Node.Valid, List.isEmpty_eq_false_iff,
        checkKeysStrictlySorted_iff, and_assoc]
  | branch2 left separator right leftInduction rightInduction =>
      simp [Node.checkValid, Node.Valid, leftInduction, rightInduction,
        List.all_eq_true, and_assoc]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp [Node.checkValid, Node.Valid, leftInduction, middleInduction,
        rightInduction, List.all_eq_true, and_assoc]

theorem Node.checkRootValid_iff (node : Node Value) :
    node.checkRootValid = true ↔ node.RootValid := by
  cases node with
  | leaf entries =>
      simp [Node.checkRootValid, Node.RootValid, checkKeysStrictlySorted_iff]
  | branch2 left separator right =>
      exact Node.checkValid_iff (.branch2 left separator right)
  | branch3 left firstSeparator middle secondSeparator right =>
      exact Node.checkValid_iff
        (.branch3 left firstSeparator middle secondSeparator right)

def InsertResult.ValidAt (height : Nat) : InsertResult Value → Prop
  | .done node => node.Valid ∧ node.height = height
  | .split left separator right =>
      left.Valid ∧ right.Valid ∧ left.height = height ∧ right.height = height ∧
      (∀ entry ∈ left.toList, entry.1 < separator) ∧
      (∀ entry ∈ right.toList, separator ≤ entry.1)

theorem Node.Valid.nonempty {node : Node Value} (valid : node.Valid) :
    node.toList ≠ [] := by
  induction node with
  | leaf entries => simpa [Node.Valid, Node.toList] using valid.1
  | branch2 left separator right leftInduction rightInduction =>
      intro empty
      have leftEmpty : left.toList = [] := by
        exact List.append_eq_nil_iff.mp (by simpa [Node.toList] using empty) |>.1
      exact leftInduction valid.1 leftEmpty
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      intro empty
      have allEmpty : left.toList = [] ∧ middle.toList ++ right.toList = [] :=
        List.append_eq_nil_iff.mp
          (by simpa [Node.toList, List.append_assoc] using empty)
      exact leftInduction valid.1 allEmpty.1

theorem Node.Valid.routes {node : Node Value} (valid : node.Valid) :
    node.Routes := by
  induction node with
  | leaf entries => trivial
  | branch2 left separator right leftInduction rightInduction =>
      rcases valid with ⟨leftValid, rightValid, _, leftBefore, rightAfter⟩
      exact ⟨leftInduction leftValid, rightInduction rightValid,
        leftBefore, rightAfter⟩
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases valid with
        ⟨leftValid, middleValid, rightValid, _, _, separators, leftBefore,
          middleBetween, rightAfter⟩
      exact ⟨leftInduction leftValid, middleInduction middleValid,
        rightInduction rightValid, separators, leftBefore, middleBetween,
        rightAfter⟩

theorem Node.Valid.rootValid {node : Node Value} (valid : node.Valid) :
    node.RootValid := by
  cases node with
  | leaf entries => exact ⟨valid.2.1, valid.2.2⟩
  | branch2 => exact valid
  | branch3 => exact valid

theorem Node.RootValid.routes {node : Node Value} (valid : node.RootValid) :
    node.Routes := by
  cases node with
  | leaf => trivial
  | branch2 => exact Node.Valid.routes valid
  | branch3 => exact Node.Valid.routes valid

theorem Node.Valid.sorted {node : Node Value} (valid : node.Valid) :
    PagedBTree.KeysStrictlySorted node.toList := by
  induction node with
  | leaf entries => exact valid.2.1
  | branch2 left separator right leftInduction rightInduction =>
      rcases valid with
        ⟨leftValid, rightValid, _, leftBefore, rightAfter⟩
      apply List.pairwise_append.2
      exact ⟨leftInduction leftValid, rightInduction rightValid,
        fun leftEntry leftMember rightEntry rightMember =>
          Nat.lt_of_lt_of_le (leftBefore leftEntry leftMember)
            (rightAfter rightEntry rightMember)⟩
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases valid with
        ⟨leftValid, middleValid, rightValid, _, _, separatorsOrdered, leftBefore,
          middleBetween, rightAfter⟩
      apply List.pairwise_append.2
      refine ⟨?_, rightInduction rightValid, ?_⟩
      · apply List.pairwise_append.2
        exact ⟨leftInduction leftValid, middleInduction middleValid,
          fun leftEntry leftMember middleEntry middleMember =>
            Nat.lt_of_lt_of_le (leftBefore leftEntry leftMember)
              (middleBetween middleEntry middleMember).1⟩
      · intro earlier earlierMember rightEntry rightMember
        rw [List.mem_append] at earlierMember
        rcases earlierMember with leftMember | middleMember
        · exact Nat.lt_of_lt_of_le
            (Nat.lt_trans (leftBefore earlier leftMember)
              separatorsOrdered)
            (rightAfter rightEntry rightMember)
        · exact Nat.lt_of_lt_of_le
            (middleBetween earlier middleMember).2
            (rightAfter rightEntry rightMember)

theorem Node.RootValid.sorted {node : Node Value} (valid : node.RootValid) :
    PagedBTree.KeysStrictlySorted node.toList := by
  cases node with
  | leaf entries => exact valid.1
  | branch2 => exact Node.Valid.sorted valid
  | branch3 => exact Node.Valid.sorted valid

/-- Lookup completeness for a valid routed tree. Together with
`lookup_some_mem`, this is the exact point-lookup refinement used by the live
primary-key access path. -/
theorem Node.lookup_of_mem {node : Node Value} {key : Nat} {value : Value}
    (valid : node.RootValid) (member : (key, value) ∈ node.toList) :
    node.lookup key = some value := by
  induction node with
  | leaf entries =>
      simp only [Node.RootValid] at valid
      simp only [Node.toList] at member
      unfold Node.lookup
      rw [findKey?_eq_some_of_mem valid.1 member]
      rfl
  | branch2 left separator right leftInduction rightInduction =>
      rcases valid with
        ⟨leftValid, rightValid, _, leftBefore, rightAfter⟩
      simp only [Node.toList, List.mem_append] at member
      rcases member with leftMember | rightMember
      · have routed := leftBefore (key, value) leftMember
        simp only [Node.lookup, if_pos routed]
        exact leftInduction leftValid.rootValid leftMember
      · have routed : ¬key < separator :=
          Nat.not_lt_of_ge (rightAfter (key, value) rightMember)
        simp only [Node.lookup, if_neg routed]
        exact rightInduction rightValid.rootValid rightMember
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases valid with
        ⟨leftValid, middleValid, rightValid, _, _, separatorsOrdered,
          leftBefore, middleBetween, rightAfter⟩
      simp only [Node.toList, List.mem_append] at member
      rcases member with (leftMember | middleMember) | rightMember
      · have routed := leftBefore (key, value) leftMember
        simp only [Node.lookup, if_pos routed]
        exact leftInduction leftValid.rootValid leftMember
      · have between := middleBetween (key, value) middleMember
        have notLeft : ¬key < firstSeparator := Nat.not_lt_of_ge between.1
        simp only [Node.lookup, if_neg notLeft, if_pos between.2]
        exact middleInduction middleValid.rootValid middleMember
      · have after := rightAfter (key, value) rightMember
        have notLeft : ¬key < firstSeparator :=
          Nat.not_lt_of_ge (Nat.le_trans
            (Nat.le_of_lt separatorsOrdered) after)
        have notMiddle : ¬key < secondSeparator := Nat.not_lt_of_ge after
        simp only [Node.lookup, if_neg notLeft, if_neg notMiddle]
        exact rightInduction rightValid.rootValid rightMember

private theorem all_orderedInsert (predicate : Entry Value → Prop)
    (inserted : predicate (key, value))
    (old : ∀ entry ∈ entries, predicate entry) :
    ∀ entry ∈ PagedBTree.orderedInsert key value entries, predicate entry := by
  intro entry member
  rcases PagedBTree.mem_orderedInsert member with equal | previous
  · simpa [equal] using inserted
  · exact old entry previous

private theorem orderedInsert_length_le (entries : List (Entry Value))
    (key : Nat) (value : Value) :
    (PagedBTree.orderedInsert key value entries).length ≤ entries.length + 1 := by
  induction entries with
  | nil => simp [PagedBTree.orderedInsert]
  | cons entry entries induction =>
      simp only [PagedBTree.orderedInsert]
      split
      next => simp
      next =>
        split
        next => simp only [List.length_cons]; omega
        next => simp

private theorem orderedInsert_append_right (key : Nat) (value : Value) :
    ∀ (left right : List (Entry Value)),
      (∀ entry ∈ left, entry.1 < key) →
      PagedBTree.orderedInsert key value (left ++ right) =
        left ++ PagedBTree.orderedInsert key value right
  | [], _, _ => rfl
  | entry :: entries, right, before => by
      simp only [List.cons_append, PagedBTree.orderedInsert]
      rw [if_neg (Nat.not_lt_of_ge (Nat.le_of_lt (before entry (by simp))))]
      rw [if_pos (before entry (by simp))]
      simp only [List.cons_append, List.cons.injEq, true_and]
      exact orderedInsert_append_right key value entries right
        (fun candidate member => before candidate (by simp [member]))

private theorem orderedInsert_append_left (key : Nat) (value : Value) :
    ∀ (left right : List (Entry Value)),
      (∀ entry ∈ right, key < entry.1) →
      PagedBTree.orderedInsert key value (left ++ right) =
        PagedBTree.orderedInsert key value left ++ right
  | [], [], _ => rfl
  | [], entry :: entries, after => by
      simp [PagedBTree.orderedInsert, after entry (by simp)]
  | entry :: entries, right, after => by
      simp only [List.cons_append, PagedBTree.orderedInsert]
      split
      next keyBefore => rfl
      next notBefore =>
        split
        next entryBefore =>
          simp only [List.cons_append, List.cons.injEq, true_and]
          exact orderedInsert_append_left key value entries right after
        next notAfter => rfl

/-- Localized recursive insertion. A full leaf splits; a two-child interior
absorbs one propagated split; a full three-child interior splits and propagates
again. No flattening or whole-tree repagination occurs. -/
def Node.insertStep (key : Nat) (value : Value) :
    Node Value → InsertResult Value
  | .leaf entries =>
      match PagedBTree.orderedInsert key value entries with
      | [first, second, third] =>
          .split (.leaf [first]) second.1 (.leaf [second, third])
      | updated => .done (.leaf updated)
  | .branch2 left separator right =>
      if key < separator then
        match left.insertStep key value with
        | .done updated => .done (.branch2 updated separator right)
        | .split first promoted second =>
            .done (.branch3 first promoted second separator right)
      else
        match right.insertStep key value with
        | .done updated => .done (.branch2 left separator updated)
        | .split first promoted second =>
            .done (.branch3 left separator first promoted second)
  | .branch3 left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then
        match left.insertStep key value with
        | .done updated =>
            .done (.branch3 updated firstSeparator middle secondSeparator right)
        | .split first promoted second =>
            .split (.branch2 first promoted second) firstSeparator
              (.branch2 middle secondSeparator right)
      else if key < secondSeparator then
        match middle.insertStep key value with
        | .done updated =>
            .done (.branch3 left firstSeparator updated secondSeparator right)
        | .split first promoted second =>
            .split (.branch2 left firstSeparator first) promoted
              (.branch2 second secondSeparator right)
      else
        match right.insertStep key value with
        | .done updated =>
            .done (.branch3 left firstSeparator middle secondSeparator updated)
        | .split first promoted second =>
            .split (.branch2 left firstSeparator middle) secondSeparator
              (.branch2 first promoted second)

/-- Local insertion preserves bounded leaf occupancy and equal child heights.
A propagated split returns two balanced nodes at exactly the input height; a
completed insertion returns a balanced node whose height is unchanged. -/
theorem Node.insertStep_balanced (node : Node Value) (balanced : node.Balanced)
    (key : Nat) (value : Value) :
    (node.insertStep key value).BalancedAt node.height := by
  induction node with
  | leaf entries =>
      have lengthBound := orderedInsert_length_le entries key value
      simp only [Node.insertStep]
      generalize updatedEq : PagedBTree.orderedInsert key value entries = updated
      rw [updatedEq] at lengthBound
      cases updated with
      | nil => simp [InsertResult.BalancedAt, Node.Balanced, Node.height]
      | cons first rest =>
        cases rest with
        | nil => simp [InsertResult.BalancedAt, Node.Balanced, Node.height]
        | cons second rest =>
          cases rest with
          | nil => simp [InsertResult.BalancedAt, Node.Balanced, Node.height]
          | cons third rest =>
            cases rest with
            | nil => simp [InsertResult.BalancedAt, Node.Balanced, Node.height]
            | cons fourth rest =>
              simp only [Node.Balanced] at balanced
              simp only [List.length_cons, List.length_nil] at lengthBound
              omega
  | branch2 left separator right leftInduction rightInduction =>
      rcases balanced with ⟨leftBalanced, rightBalanced, equalHeight⟩
      simp only [Node.insertStep]
      split
      next =>
        have childResult := leftInduction leftBalanced
        cases inserted : left.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedBalanced, updatedHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              updatedBalanced, rightBalanced, updatedHeight, equalHeight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              firstBalanced, secondBalanced, rightBalanced, firstHeight,
              secondHeight, equalHeight]
      next =>
        have childResult := rightInduction rightBalanced
        cases inserted : right.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedBalanced, updatedHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              leftBalanced, updatedBalanced, updatedHeight, equalHeight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              leftBalanced, firstBalanced, secondBalanced, firstHeight,
              secondHeight, equalHeight]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases balanced with
        ⟨leftBalanced, middleBalanced, rightBalanced, leftMiddle, middleRight⟩
      simp only [Node.insertStep]
      split
      next =>
        have childResult := leftInduction leftBalanced
        cases inserted : left.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedBalanced, updatedHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              updatedBalanced, middleBalanced, rightBalanced, updatedHeight,
              leftMiddle, middleRight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
            simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
              firstBalanced, secondBalanced, middleBalanced, rightBalanced,
              firstHeight, secondHeight, leftMiddle, middleRight]
      next =>
        split
        next =>
          have childResult := middleInduction middleBalanced
          cases inserted : middle.insertStep key value with
          | done updated =>
              rw [inserted] at childResult
              rcases childResult with ⟨updatedBalanced, updatedHeight⟩
              simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
                leftBalanced, updatedBalanced, rightBalanced, updatedHeight,
                leftMiddle, middleRight]
          | split first promoted second =>
              rw [inserted] at childResult
              rcases childResult with
                ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
              simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
                leftBalanced, firstBalanced, secondBalanced, rightBalanced,
                firstHeight, secondHeight, leftMiddle, middleRight]
        next =>
          have childResult := rightInduction rightBalanced
          cases inserted : right.insertStep key value with
          | done updated =>
              rw [inserted] at childResult
              rcases childResult with ⟨updatedBalanced, updatedHeight⟩
              simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
                leftBalanced, middleBalanced, updatedBalanced, updatedHeight,
                leftMiddle, middleRight]
          | split first promoted second =>
              rw [inserted] at childResult
              rcases childResult with
                ⟨firstBalanced, secondBalanced, firstHeight, secondHeight⟩
              simp [inserted, InsertResult.BalancedAt, Node.Balanced, Node.height,
                leftBalanced, middleBalanced, firstBalanced, secondBalanced,
                firstHeight, secondHeight, leftMiddle, middleRight]

theorem Node.insertStep_toList (node : Node Value) (routes : node.Routes)
    (key : Nat) (value : Value) :
    (node.insertStep key value).toList =
      PagedBTree.orderedInsert key value node.toList := by
  induction node with
  | leaf entries =>
      simp only [Node.insertStep, Node.toList]
      generalize equal : PagedBTree.orderedInsert key value entries = updated
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
  | branch2 left separator right leftInduction rightInduction =>
      rcases routes with ⟨leftRoutes, rightRoutes, leftBefore, rightAfter⟩
      simp only [Node.insertStep]
      split
      next keyBefore =>
        have global := orderedInsert_append_left key value left.toList right.toList
          (fun entry member => Nat.lt_of_lt_of_le keyBefore
            (rightAfter entry member))
        cases inserted : left.insertStep key value with
        | done updated =>
          have localEq := leftInduction leftRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global]
        | split first promoted second =>
          have localEq := leftInduction leftRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global,
            List.append_assoc]
      next keyAfter =>
        have leftBeforeKey : ∀ entry ∈ left.toList, entry.1 < key := by
          intro entry member
          exact Nat.lt_of_lt_of_le (leftBefore entry member)
            (Nat.le_of_not_gt keyAfter)
        have global := orderedInsert_append_right key value left.toList right.toList
          leftBeforeKey
        cases inserted : right.insertStep key value with
        | done updated =>
          have localEq := rightInduction rightRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global]
        | split first promoted second =>
          have localEq := rightInduction rightRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global,
            List.append_assoc]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases routes with
        ⟨leftRoutes, middleRoutes, rightRoutes, separatorsOrdered, leftBefore,
          middleBetween, rightAfter⟩
      simp only [Node.insertStep]
      split
      next keyBefore =>
        have tailAfter : ∀ entry ∈ middle.toList ++ right.toList,
            key < entry.1 := by
          intro entry member
          simp only [List.mem_append] at member
          rcases member with middleMember | rightMember
          · exact Nat.lt_of_lt_of_le keyBefore
              (middleBetween entry middleMember).1
          · exact Nat.lt_of_lt_of_le
              (Nat.lt_trans keyBefore separatorsOrdered)
              (rightAfter entry rightMember)
        have global := orderedInsert_append_left key value left.toList
          (middle.toList ++ right.toList) tailAfter
        cases inserted : left.insertStep key value with
        | done updated =>
          have localEq := leftInduction leftRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global,
            List.append_assoc]
        | split first promoted second =>
          have localEq := leftInduction leftRoutes
          rw [inserted] at localEq
          simp only [InsertResult.toList] at localEq
          simp [inserted, InsertResult.toList, Node.toList, localEq, global,
            List.append_assoc]
      next notLeft =>
        split
        next beforeRight =>
          have leftBeforeKey : ∀ entry ∈ left.toList, entry.1 < key := by
            intro entry member
            exact Nat.lt_of_lt_of_le (leftBefore entry member)
              (Nat.le_of_not_gt notLeft)
          have rightAfterKey : ∀ entry ∈ right.toList, key < entry.1 := by
            intro entry member
            exact Nat.lt_of_lt_of_le beforeRight (rightAfter entry member)
          have first := orderedInsert_append_right key value left.toList
            (middle.toList ++ right.toList) leftBeforeKey
          have second := orderedInsert_append_left key value middle.toList
            right.toList rightAfterKey
          cases inserted : middle.insertStep key value with
          | done updated =>
            have localEq := middleInduction middleRoutes
            rw [inserted] at localEq
            simp only [InsertResult.toList] at localEq
            simp [inserted, InsertResult.toList, Node.toList, localEq, first,
              second, List.append_assoc]
          | split firstNode promoted secondNode =>
            have localEq := middleInduction middleRoutes
            rw [inserted] at localEq
            simp only [InsertResult.toList] at localEq
            simp [inserted, InsertResult.toList, Node.toList, localEq, first,
              second, List.append_assoc]
            rw [← List.append_assoc, localEq]
        next notMiddle =>
          have prefixBefore : ∀ entry ∈ left.toList ++ middle.toList,
              entry.1 < key := by
            intro entry member
            simp only [List.mem_append] at member
            rcases member with leftMember | middleMember
            · exact Nat.lt_of_lt_of_le (leftBefore entry leftMember)
                (Nat.le_of_not_gt notLeft)
            · exact Nat.lt_of_lt_of_le (middleBetween entry middleMember).2
                (Nat.le_of_not_gt notMiddle)
          have global := orderedInsert_append_right key value
            (left.toList ++ middle.toList) right.toList prefixBefore
          cases inserted : right.insertStep key value with
          | done updated =>
            have localEq := rightInduction rightRoutes
            rw [inserted] at localEq
            simp only [InsertResult.toList] at localEq
            simp [inserted, InsertResult.toList, Node.toList, localEq, global,
              List.append_assoc]
            simpa [List.append_assoc] using global.symm
          | split first promoted second =>
            have localEq := rightInduction rightRoutes
            rw [inserted] at localEq
            simp only [InsertResult.toList] at localEq
            simp [inserted, InsertResult.toList, Node.toList, localEq, global,
              List.append_assoc]
            simpa [List.append_assoc] using global.symm

/-- The complete recursive insertion invariant.  Besides preserving contents,
insertion preserves occupancy, sorted leaves, equal leaf depth, and every
separator bound.  A split returns two valid nodes at the original height with
an exact routing boundary between them. -/
theorem Node.insertStep_valid (node : Node Value) (valid : node.Valid)
    (key : Nat) (value : Value) :
    (node.insertStep key value).ValidAt node.height := by
  induction node with
  | leaf entries =>
      have sorted := PagedBTree.orderedInsert_sorted
        (key := key) (value := value) entries valid.2.1
      have lengthBound := orderedInsert_length_le entries key value
      have nonempty : PagedBTree.orderedInsert key value entries ≠ [] := by
        induction entries with
        | nil => simp [PagedBTree.orderedInsert]
        | cons entry entries induction =>
            simp only [PagedBTree.orderedInsert]
            split <;> try simp
            split <;> simp
      simp only [Node.insertStep]
      generalize updatedEq : PagedBTree.orderedInsert key value entries = updated
      rw [updatedEq] at sorted lengthBound nonempty
      cases updated with
      | nil => contradiction
      | cons first rest =>
        cases rest with
        | nil =>
            exact ⟨⟨by simp, by simp [PagedBTree.KeysStrictlySorted], by simp⟩,
              rfl⟩
        | cons second rest =>
          cases rest with
          | nil =>
              exact ⟨⟨by simp, sorted, by simp⟩, rfl⟩
          | cons third rest =>
            cases rest with
            | nil =>
              simp [PagedBTree.KeysStrictlySorted] at sorted
              rcases sorted with ⟨⟨firstSecond, firstThird⟩, secondThird⟩
              simp only [InsertResult.ValidAt, Node.Valid, Node.height,
                Node.toList, List.length_cons, List.length_nil]
              exact ⟨⟨by simp, by simp [PagedBTree.KeysStrictlySorted], by omega⟩,
                ⟨by simp, by simpa [PagedBTree.KeysStrictlySorted] using secondThird,
                  by omega⟩,
                trivial, trivial,
                by
                  intro entry member
                  simp only [List.mem_singleton] at member
                  subst entry
                  exact firstSecond,
                by intro entry member
                   simp only [List.mem_cons, List.mem_singleton] at member
                   rcases member with equal | tail
                   · subst entry
                     exact Nat.le_refl _
                   · rcases tail with equal | impossible
                     · subst entry
                       exact Nat.le_of_lt secondThird
                     · simp at impossible⟩
            | cons fourth rest =>
              simp only [Node.Valid] at valid
              simp only [List.length_cons, List.length_nil] at lengthBound
              omega
  | branch2 left separator right leftInduction rightInduction =>
      rcases valid with
        ⟨leftValid, rightValid, equalHeight, leftBefore, rightAfter⟩
      simp only [Node.insertStep]
      split
      next keyBefore =>
        have content := left.insertStep_toList leftValid.routes key value
        have upper : ∀ entry ∈ (left.insertStep key value).toList,
            entry.1 < separator := by
          intro entry member
          rw [content] at member
          exact all_orderedInsert (fun candidate => candidate.1 < separator)
            keyBefore leftBefore entry member
        have childResult := leftInduction leftValid
        cases inserted : left.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedValid, updatedHeight⟩
            simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at upper ⊢
            refine ⟨⟨updatedValid, rightValid,
              updatedHeight.trans equalHeight, upper, rightAfter⟩, ?_⟩
            simp [Node.height, updatedHeight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstValid, secondValid, firstHeight, secondHeight,
                firstBefore, secondAfter⟩
            have promotedBefore : promoted < separator := by
              obtain ⟨entry, member⟩ :=
                List.exists_mem_of_ne_nil second.toList secondValid.nonempty
              exact Nat.lt_of_le_of_lt (secondAfter entry member)
                (upper entry (by simp [inserted, InsertResult.toList, member]))
            simp only [inserted, InsertResult.ValidAt] at upper ⊢
            refine ⟨?_, ?_⟩
            · exact ⟨firstValid, secondValid, rightValid,
                firstHeight.trans secondHeight.symm,
                secondHeight.trans equalHeight, promotedBefore, firstBefore,
                (fun entry member => ⟨secondAfter entry member,
                  upper entry (by simp [InsertResult.toList, member])⟩),
                rightAfter⟩
            · simp [Node.height, firstHeight]
      next keyAfter =>
        have content := right.insertStep_toList rightValid.routes key value
        have lower : ∀ entry ∈ (right.insertStep key value).toList,
            separator ≤ entry.1 := by
          intro entry member
          rw [content] at member
          exact all_orderedInsert (fun candidate => separator ≤ candidate.1)
            (Nat.le_of_not_gt keyAfter) rightAfter entry member
        have childResult := rightInduction rightValid
        cases inserted : right.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedValid, updatedHeight⟩
            simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at lower ⊢
            refine ⟨⟨leftValid, updatedValid,
              equalHeight.trans updatedHeight.symm, leftBefore, lower⟩, rfl⟩
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstValid, secondValid, firstHeight, secondHeight,
                firstBefore, secondAfter⟩
            have separatorBefore : separator < promoted := by
              obtain ⟨entry, member⟩ :=
                List.exists_mem_of_ne_nil first.toList firstValid.nonempty
              exact Nat.lt_of_le_of_lt
                (lower entry (by simp [inserted, InsertResult.toList, member]))
                (firstBefore entry member)
            simp only [inserted, InsertResult.ValidAt] at lower ⊢
            refine ⟨?_, rfl⟩
            exact ⟨leftValid, firstValid, secondValid,
              equalHeight.trans firstHeight.symm,
              firstHeight.trans secondHeight.symm, separatorBefore, leftBefore,
              (fun entry member => ⟨
                lower entry (by simp [InsertResult.toList, member]),
                firstBefore entry member⟩), secondAfter⟩
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases valid with
        ⟨leftValid, middleValid, rightValid, leftMiddle, middleRight,
          separatorsOrdered, leftBefore, middleBetween, rightAfter⟩
      simp only [Node.insertStep]
      split
      next keyBefore =>
        have content := left.insertStep_toList leftValid.routes key value
        have upper : ∀ entry ∈ (left.insertStep key value).toList,
            entry.1 < firstSeparator := by
          intro entry member
          rw [content] at member
          exact all_orderedInsert (fun candidate => candidate.1 < firstSeparator)
            keyBefore leftBefore entry member
        have childResult := leftInduction leftValid
        cases inserted : left.insertStep key value with
        | done updated =>
            rw [inserted] at childResult
            rcases childResult with ⟨updatedValid, updatedHeight⟩
            simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at upper ⊢
            refine ⟨⟨updatedValid, middleValid, rightValid,
              updatedHeight.trans leftMiddle, middleRight, separatorsOrdered,
              upper, middleBetween, rightAfter⟩, ?_⟩
            simp [Node.height, updatedHeight]
        | split first promoted second =>
            rw [inserted] at childResult
            rcases childResult with
              ⟨firstValid, secondValid, firstHeight, secondHeight,
                firstBefore, secondAfter⟩
            simp only [inserted, InsertResult.ValidAt] at upper ⊢
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact ⟨firstValid, secondValid,
                firstHeight.trans secondHeight.symm, firstBefore, secondAfter⟩
            · exact ⟨middleValid, rightValid, middleRight,
                (fun entry member => (middleBetween entry member).2), rightAfter⟩
            · simp [Node.height, firstHeight]
            · simp [Node.height, leftMiddle]
            · intro entry member
              simp only [Node.toList, List.mem_append] at member
              rcases member with firstMember | secondMember
              · exact upper entry (by simp [InsertResult.toList, firstMember])
              · exact upper entry (by simp [InsertResult.toList, secondMember])
            · intro entry member
              simp only [Node.toList, List.mem_append] at member
              rcases member with middleMember | rightMember
              · exact (middleBetween entry middleMember).1
              · exact Nat.le_trans (Nat.le_of_lt separatorsOrdered)
                  (rightAfter entry rightMember)
      next notLeft =>
        split
        next beforeRight =>
          have content := middle.insertStep_toList middleValid.routes key value
          have lower : ∀ entry ∈ (middle.insertStep key value).toList,
              firstSeparator ≤ entry.1 := by
            intro entry member
            rw [content] at member
            exact all_orderedInsert
              (fun candidate => firstSeparator ≤ candidate.1)
              (Nat.le_of_not_gt notLeft)
              (fun entry member => (middleBetween entry member).1) entry member
          have upper : ∀ entry ∈ (middle.insertStep key value).toList,
              entry.1 < secondSeparator := by
            intro entry member
            rw [content] at member
            exact all_orderedInsert
              (fun candidate => candidate.1 < secondSeparator) beforeRight
              (fun entry member => (middleBetween entry member).2) entry member
          have childResult := middleInduction middleValid
          cases inserted : middle.insertStep key value with
          | done updated =>
              rw [inserted] at childResult
              rcases childResult with ⟨updatedValid, updatedHeight⟩
              simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at lower upper ⊢
              refine ⟨⟨leftValid, updatedValid, rightValid,
                leftMiddle.trans updatedHeight.symm,
                updatedHeight.trans middleRight, separatorsOrdered, leftBefore,
                (fun entry member => ⟨lower entry member, upper entry member⟩),
                rightAfter⟩, rfl⟩
          | split first promoted second =>
              rw [inserted] at childResult
              rcases childResult with
                ⟨firstValid, secondValid, firstHeight, secondHeight,
                  firstBefore, secondAfter⟩
              simp only [inserted, InsertResult.ValidAt] at lower upper ⊢
              have firstSeparatorBeforePromoted : firstSeparator < promoted := by
                obtain ⟨witness, witnessMember⟩ :=
                  List.exists_mem_of_ne_nil first.toList firstValid.nonempty
                exact Nat.lt_of_le_of_lt
                  (lower witness (by simp [InsertResult.toList, witnessMember]))
                  (firstBefore witness witnessMember)
              have promotedBeforeSecond : promoted < secondSeparator := by
                obtain ⟨witness, witnessMember⟩ :=
                  List.exists_mem_of_ne_nil second.toList secondValid.nonempty
                exact Nat.lt_of_le_of_lt (secondAfter witness witnessMember)
                  (upper witness (by simp [InsertResult.toList, witnessMember]))
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact ⟨leftValid, firstValid,
                  leftMiddle.trans firstHeight.symm, leftBefore,
                  fun entry member => lower entry
                    (by simp [InsertResult.toList, member])⟩
              · exact ⟨secondValid, rightValid,
                  secondHeight.trans middleRight, (fun entry member =>
                    upper entry (by simp [InsertResult.toList, member])), rightAfter⟩
              · rfl
              · exact congrArg (· + 1) (secondHeight.trans leftMiddle.symm)
              · intro entry member
                simp only [Node.toList, List.mem_append] at member
                rcases member with leftMember | firstMember
                · exact Nat.lt_trans (leftBefore entry leftMember)
                    firstSeparatorBeforePromoted
                · exact firstBefore entry firstMember
              · intro entry member
                simp only [Node.toList, List.mem_append] at member
                rcases member with secondMember | rightMember
                · exact secondAfter entry secondMember
                · exact Nat.le_trans (Nat.le_of_lt promotedBeforeSecond)
                    (rightAfter entry rightMember)
        next notMiddle =>
          have content := right.insertStep_toList rightValid.routes key value
          have lower : ∀ entry ∈ (right.insertStep key value).toList,
              secondSeparator ≤ entry.1 := by
            intro entry member
            rw [content] at member
            exact all_orderedInsert
              (fun candidate => secondSeparator ≤ candidate.1)
              (Nat.le_of_not_gt notMiddle) rightAfter entry member
          have childResult := rightInduction rightValid
          cases inserted : right.insertStep key value with
          | done updated =>
              rw [inserted] at childResult
              rcases childResult with ⟨updatedValid, updatedHeight⟩
              simp only [inserted, InsertResult.ValidAt, InsertResult.toList] at lower ⊢
              refine ⟨⟨leftValid, middleValid, updatedValid, leftMiddle,
                middleRight.trans updatedHeight.symm, separatorsOrdered,
                leftBefore, middleBetween, lower⟩, rfl⟩
          | split first promoted second =>
              rw [inserted] at childResult
              rcases childResult with
                ⟨firstValid, secondValid, firstHeight, secondHeight,
                  firstBefore, secondAfter⟩
              simp only [inserted, InsertResult.ValidAt] at lower ⊢
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact ⟨leftValid, middleValid, leftMiddle, leftBefore,
                  fun entry member => (middleBetween entry member).1⟩
              · exact ⟨firstValid, secondValid,
                  firstHeight.trans secondHeight.symm, firstBefore, secondAfter⟩
              · rfl
              · exact congrArg (· + 1)
                  (firstHeight.trans (middleRight.symm.trans leftMiddle.symm))
              · intro entry member
                simp only [Node.toList, List.mem_append] at member
                rcases member with leftMember | middleMember
                · exact Nat.lt_trans (leftBefore entry leftMember)
                    separatorsOrdered
                · exact (middleBetween entry middleMember).2
              · intro entry member
                simp only [Node.toList, List.mem_append] at member
                rcases member with firstMember | secondMember
                · exact lower entry (by simp [InsertResult.toList, firstMember])
                · exact lower entry (by simp [InsertResult.toList, secondMember])
def Node.insert (node : Node Value) (key : Nat) (value : Value) : Node Value :=
  match node.insertStep key value with
  | .done updated => updated
  | .split left separator right => .branch2 left separator right

theorem Node.toList_insert (node : Node Value) (routes : node.Routes)
    (key : Nat) (value : Value) :
    (node.insert key value).toList =
      PagedBTree.orderedInsert key value node.toList := by
  have step := node.insertStep_toList routes key value
  unfold Node.insert
  cases inserted : node.insertStep key value with
  | done updated =>
      rw [inserted] at step
      simpa [InsertResult.toList] using step
  | split left separator right =>
      rw [inserted] at step
      simpa [InsertResult.toList, Node.toList] using step

theorem Node.insert_balanced (node : Node Value) (balanced : node.Balanced)
    (key : Nat) (value : Value) : (node.insert key value).Balanced := by
  have step := node.insertStep_balanced balanced key value
  unfold Node.insert
  cases inserted : node.insertStep key value with
  | done updated =>
      rw [inserted] at step
      exact step.1
  | split left separator right =>
      rw [inserted] at step
      rcases step with ⟨leftBalanced, rightBalanced, leftHeight, rightHeight⟩
      simp only [Node.Balanced]
      exact ⟨leftBalanced, rightBalanced, leftHeight.trans rightHeight.symm⟩

theorem Node.insert_rootValid_of_valid (node : Node Value) (valid : node.Valid)
    (key : Nat) (value : Value) : (node.insert key value).RootValid := by
  have step := node.insertStep_valid valid key value
  unfold Node.insert
  cases inserted : node.insertStep key value with
  | done updated =>
      rw [inserted] at step
      exact step.1.rootValid
  | split left separator right =>
      rw [inserted] at step
      rcases step with
        ⟨leftValid, rightValid, leftHeight, rightHeight, leftBefore, rightAfter⟩
      exact ⟨leftValid, rightValid, leftHeight.trans rightHeight.symm,
        leftBefore, rightAfter⟩

/-- Root validity is inductive from the empty tree through every insertion;
callers no longer need to assume the routing premise used by the raw
abstraction theorem. -/
theorem Node.insert_rootValid (node : Node Value) (valid : node.RootValid)
    (key : Nat) (value : Value) : (node.insert key value).RootValid := by
  cases node with
  | leaf entries =>
      by_cases empty : entries = []
      · subst entries
        simp [Node.insert, Node.insertStep, Node.RootValid,
          PagedBTree.orderedInsert, PagedBTree.KeysStrictlySorted]
      · exact Node.insert_rootValid_of_valid (.leaf entries)
          ⟨empty, valid.1, valid.2⟩ key value
  | branch2 left separator right =>
      exact Node.insert_rootValid_of_valid (.branch2 left separator right)
        valid key value
  | branch3 left firstSeparator middle secondSeparator right =>
      exact Node.insert_rootValid_of_valid
        (.branch3 left firstSeparator middle secondSeparator right)
        valid key value

theorem Node.toList_insert_rootValid (node : Node Value)
    (valid : node.RootValid) (key : Nat) (value : Value) :
    (node.insert key value).toList =
      PagedBTree.orderedInsert key value node.toList :=
  node.toList_insert valid.routes key value

def Node.insertAll (node : Node Value) (entries : List (Entry Value)) :
    Node Value :=
  entries.foldl (fun tree entry => tree.insert entry.1 entry.2) node

theorem Node.insertAll_rootValid (node : Node Value) (valid : node.RootValid) :
    (entries : List (Entry Value)) → (node.insertAll entries).RootValid
  | [] => valid
  | entry :: entries => by
      change ((node.insert entry.1 entry.2).insertAll entries).RootValid
      exact Node.insertAll_rootValid (node.insert entry.1 entry.2)
        (node.insert_rootValid valid entry.1 entry.2) entries

theorem Node.toList_insertAll (node : Node Value) (valid : node.RootValid) :
    (entries : List (Entry Value)) →
      (node.insertAll entries).toList =
        entries.foldl
          (fun contents entry =>
            PagedBTree.orderedInsert entry.1 entry.2 contents)
          node.toList
  | [] => rfl
  | entry :: entries => by
      change ((node.insert entry.1 entry.2).insertAll entries).toList = _
      rw [Node.toList_insertAll (node.insert entry.1 entry.2)
        (node.insert_rootValid valid entry.1 entry.2) entries]
      simp only [List.foldl_cons]
      rw [node.toList_insert_rootValid valid entry.1 entry.2]

private theorem orderedInsert_at_end (accumulated : List (Entry Value))
    (entry : Entry Value) (before : ∀ old ∈ accumulated, old.1 < entry.1) :
    PagedBTree.orderedInsert entry.1 entry.2 accumulated = accumulated ++ [entry] := by
  simpa [PagedBTree.orderedInsert] using orderedInsert_append_right entry.1 entry.2 accumulated [] before

private theorem fold_orderedInsert_append (accumulated : List (Entry Value)) :
    (suffix : List (Entry Value)) →
      PagedBTree.KeysStrictlySorted suffix →
      (∀ old ∈ accumulated, ∀ new ∈ suffix, old.1 < new.1) →
      suffix.foldl
          (fun contents entry =>
            PagedBTree.orderedInsert entry.1 entry.2 contents)
          accumulated = accumulated ++ suffix
  | [], _, _ => by simp
  | entry :: suffix, sorted, cross => by
      simp only [PagedBTree.KeysStrictlySorted, List.pairwise_cons] at sorted
      rw [List.foldl_cons, orderedInsert_at_end accumulated entry
        (fun old oldMember => cross old oldMember entry (by simp))]
      rw [fold_orderedInsert_append (accumulated ++ [entry]) suffix sorted.2]
      · simp [List.append_assoc]
      · intro old oldMember new newMember
        rw [List.mem_append] at oldMember
        rcases oldMember with oldMember | oldMember
        · exact cross old oldMember new (by simp [newMember])
        · simp only [List.mem_singleton] at oldMember
          subst old
          exact sorted.1 new newMember

theorem fold_orderedInsert_empty (entries : List (Entry Value))
    (sorted : PagedBTree.KeysStrictlySorted entries) :
    entries.foldl
        (fun contents entry =>
          PagedBTree.orderedInsert entry.1 entry.2 contents)
        [] = entries := by
  simpa using fold_orderedInsert_append ([] : List (Entry Value)) entries sorted
    (by simp)

/-- Deletion distinguishes a same-height result from an underflow propagated
to the parent.  This is the information the earlier `Option` deletion lacked
and is what permits local borrowing and merging without flattening the tree. -/
inductive DeleteResult (Value : Type) where
  | done (node : Node Value)
  | underflow (node : Node Value)
  | empty

def DeleteResult.toList : DeleteResult Value → List (Entry Value)
  | .done node | .underflow node => node.toList
  | .empty => []

def repairTwoLeft (separator : Nat) (deficit : Option (Node Value))
    (right : Node Value) : DeleteResult Value :=
  match deficit, right with
  | some under, .branch3 first firstSeparator middle secondSeparator last =>
      .done (.branch2 (.branch2 under separator first) firstSeparator
        (.branch2 middle secondSeparator last))
  | some under, .branch2 first middleSeparator last =>
      .underflow (.branch3 under separator first middleSeparator last)
  | some under, _ => .underflow (.branch2 under separator right)
  | none, _ => .underflow right

def repairTwoRight (left : Node Value) (separator : Nat)
    (deficit : Option (Node Value)) : DeleteResult Value :=
  match left, deficit with
  | .branch3 first firstSeparator middle secondSeparator last, some under =>
      .done (.branch2 (.branch2 first firstSeparator middle) secondSeparator
        (.branch2 last separator under))
  | .branch2 first middleSeparator last, some under =>
      .underflow (.branch3 first middleSeparator last separator under)
  | _, some under => .underflow (.branch2 left separator under)
  | _, none => .underflow left

def repairThreeLeft (firstSeparator : Nat)
    (deficit : Option (Node Value)) (middle : Node Value)
    (secondSeparator : Nat) (right : Node Value) : DeleteResult Value :=
  match deficit, middle with
  | some under, .branch3 first middleFirst second middleSecond third =>
      .done (.branch3 (.branch2 under firstSeparator first) middleFirst
        (.branch2 second middleSecond third) secondSeparator right)
  | some under, .branch2 first middleSeparator second =>
      .done (.branch2
        (.branch3 under firstSeparator first middleSeparator second)
        secondSeparator right)
  | some under, _ =>
      .done (.branch3 under firstSeparator middle secondSeparator right)
  | none, _ => .done (.branch2 middle secondSeparator right)

def repairThreeMiddle (left : Node Value) (firstSeparator : Nat)
    (deficit : Option (Node Value)) (secondSeparator : Nat)
    (right : Node Value) : DeleteResult Value :=
  match left, deficit with
  | .branch3 first leftFirst second leftSecond third, some under =>
      .done (.branch3 (.branch2 first leftFirst second) leftSecond
        (.branch2 third firstSeparator under) secondSeparator right)
  | .branch2 first leftSeparator second, some under =>
      .done (.branch2
        (.branch3 first leftSeparator second firstSeparator under)
        secondSeparator right)
  | _, some under =>
      .done (.branch3 left firstSeparator under secondSeparator right)
  | _, none => .done (.branch2 left secondSeparator right)

def repairThreeRight (left : Node Value) (firstSeparator : Nat)
    (middle : Node Value) (secondSeparator : Nat)
    (deficit : Option (Node Value)) : DeleteResult Value :=
  match middle, deficit with
  | .branch3 first middleFirst second middleSecond third, some under =>
      .done (.branch3 left firstSeparator
        (.branch2 first middleFirst second) middleSecond
        (.branch2 third secondSeparator under))
  | .branch2 first middleSeparator second, some under =>
      .done (.branch2 left firstSeparator
        (.branch3 first middleSeparator second secondSeparator under))
  | _, some under =>
      .done (.branch3 left firstSeparator middle secondSeparator under)
  | _, none => .done (.branch2 left firstSeparator middle)

/-- Local 2-3-tree deletion with borrowing from a three-child sibling, merging
with a two-child sibling, underflow propagation, and root shrink. -/
def Node.deleteBalancedStep (key : Nat) : Node Value → DeleteResult Value
  | .leaf entries =>
      match PagedBTree.eraseKey key entries with
      | [] => .empty
      | remaining => .done (.leaf remaining)
  | .branch2 left separator right =>
      if key < separator then
        match left.deleteBalancedStep key with
        | .done updated => .done (.branch2 updated separator right)
        | .underflow under => repairTwoLeft separator (some under) right
        | .empty => repairTwoLeft separator none right
      else
        match right.deleteBalancedStep key with
        | .done updated => .done (.branch2 left separator updated)
        | .underflow under => repairTwoRight left separator (some under)
        | .empty => repairTwoRight left separator none
  | .branch3 left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then
        match left.deleteBalancedStep key with
        | .done updated =>
            .done (.branch3 updated firstSeparator middle secondSeparator right)
        | .underflow under =>
            repairThreeLeft firstSeparator (some under) middle secondSeparator right
        | .empty => repairThreeLeft firstSeparator none middle secondSeparator right
      else if key < secondSeparator then
        match middle.deleteBalancedStep key with
        | .done updated =>
            .done (.branch3 left firstSeparator updated secondSeparator right)
        | .underflow under =>
            repairThreeMiddle left firstSeparator (some under) secondSeparator right
        | .empty => repairThreeMiddle left firstSeparator none secondSeparator right
      else
        match right.deleteBalancedStep key with
        | .done updated =>
            .done (.branch3 left firstSeparator middle secondSeparator updated)
        | .underflow under =>
            repairThreeRight left firstSeparator middle secondSeparator (some under)
        | .empty => repairThreeRight left firstSeparator middle secondSeparator none

def Node.deleteBalanced (node : Node Value) (key : Nat) : Node Value :=
  match node.deleteBalancedStep key with
  | .done updated | .underflow updated => updated
  | .empty => .leaf []

private def optionalNodeList : Option (Node Value) → List (Entry Value)
  | none => []
  | some node => node.toList

private theorem repairTwoLeft_toList (separator : Nat)
    (deficit : Option (Node Value)) (right : Node Value) :
    (repairTwoLeft separator deficit right).toList =
      optionalNodeList deficit ++ right.toList := by
  cases deficit <;> cases right <;>
    simp [repairTwoLeft, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

private theorem repairTwoRight_toList (left : Node Value) (separator : Nat)
    (deficit : Option (Node Value)) :
    (repairTwoRight left separator deficit).toList =
      left.toList ++ optionalNodeList deficit := by
  cases left <;> cases deficit <;>
    simp [repairTwoRight, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

private theorem repairThreeLeft_toList (firstSeparator : Nat)
    (deficit : Option (Node Value)) (middle : Node Value)
    (secondSeparator : Nat) (right : Node Value) :
    (repairThreeLeft firstSeparator deficit middle secondSeparator right).toList =
      optionalNodeList deficit ++ middle.toList ++ right.toList := by
  cases deficit <;> cases middle <;>
    simp [repairThreeLeft, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

private theorem repairThreeMiddle_toList (left : Node Value)
    (firstSeparator : Nat) (deficit : Option (Node Value))
    (secondSeparator : Nat) (right : Node Value) :
    (repairThreeMiddle left firstSeparator deficit secondSeparator right).toList =
      left.toList ++ optionalNodeList deficit ++ right.toList := by
  cases left <;> cases deficit <;>
    simp [repairThreeMiddle, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

private theorem repairThreeRight_toList (left : Node Value)
    (firstSeparator : Nat) (middle : Node Value) (secondSeparator : Nat)
    (deficit : Option (Node Value)) :
    (repairThreeRight left firstSeparator middle secondSeparator deficit).toList =
      left.toList ++ middle.toList ++ optionalNodeList deficit := by
  cases middle <;> cases deficit <;>
    simp [repairThreeRight, DeleteResult.toList, optionalNodeList, Node.toList,
      List.append_assoc]

/-- Local deletion removes only the routed leaf. Empty children are merged out
and a unary root is therefore shrunk automatically. -/
def Node.deleteStep (key : Nat) : Node Value → Option (Node Value)
  | .leaf entries =>
      match PagedBTree.eraseKey key entries with
      | [] => none
      | remaining => some (.leaf remaining)
  | .branch2 left separator right =>
      if key < separator then
        match left.deleteStep key with
        | some updated => some (.branch2 updated separator right)
        | none => some right
      else
        match right.deleteStep key with
        | some updated => some (.branch2 left separator updated)
        | none => some left
  | .branch3 left firstSeparator middle secondSeparator right =>
      if key < firstSeparator then
        match left.deleteStep key with
        | some updated =>
            some (.branch3 updated firstSeparator middle secondSeparator right)
        | none => some (.branch2 middle secondSeparator right)
      else if key < secondSeparator then
        match middle.deleteStep key with
        | some updated =>
            some (.branch3 left firstSeparator updated secondSeparator right)
        | none => some (.branch2 left secondSeparator right)
      else
        match right.deleteStep key with
        | some updated =>
            some (.branch3 left firstSeparator middle secondSeparator updated)
        | none => some (.branch2 left firstSeparator middle)

def Node.deleteUnbalanced (node : Node Value) (key : Nat) : Node Value :=
  (node.deleteStep key).getD (.leaf [])

def Node.deletedList : Option (Node Value) → List (Entry Value)
  | none => []
  | some node => node.toList

private theorem filter_key_eq_self (entries : List (Entry Value)) (key : Nat)
    (absent : ∀ entry ∈ entries, entry.1 ≠ key) :
    entries.filter (fun entry => entry.1 ≠ key) = entries := by
  apply List.filter_eq_self.2
  intro entry member
  simp [absent entry member]

/-- Balanced deletion has the exact abstract effect of removing the routed
key. Borrowing and merging only reassociate the same child contents. -/
theorem Node.deleteBalancedStep_toList (node : Node Value)
    (routes : node.Routes) (key : Nat) :
    (node.deleteBalancedStep key).toList =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  induction node with
  | leaf entries =>
      simp only [Node.deleteBalancedStep, PagedBTree.eraseKey_eq_filter,
        Node.toList]
      generalize remainingEq :
        List.filter (fun entry : Entry Value => entry.1 ≠ key) entries = remaining
      change DeleteResult.toList
          (match remaining with
          | [] => .empty
          | remaining => .done (.leaf remaining)) = remaining
      cases remaining <;> rfl
  | branch2 left separator right leftInduction rightInduction =>
      rcases routes with ⟨leftRoutes, rightRoutes, leftBefore, rightAfter⟩
      simp only [Node.deleteBalancedStep]
      split
      next keyBefore =>
        have rightUnchanged :
            right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
          filter_key_eq_self right.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt keyBefore (rightAfter entry member)
        have localEq := leftInduction leftRoutes
        cases changed : left.deleteBalancedStep key with
        | done updated =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            change updated.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
        | underflow under =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairTwoLeft_toList]
            change under.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
        | empty =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairTwoLeft_toList]
            simp only [optionalNodeList, Node.toList, List.append_nil,
              List.nil_append]
            change right.toList = List.filter (fun entry => entry.1 ≠ key)
              (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
            simp
      next keyAfter =>
        have leftUnchanged :
            left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
          filter_key_eq_self left.toList key fun entry member equal => by
            subst key
            exact Nat.not_lt_of_ge (Nat.le_of_not_gt keyAfter)
              (leftBefore entry member)
        have localEq := rightInduction rightRoutes
        cases changed : right.deleteBalancedStep key with
        | done updated =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            change left.toList ++ updated.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
        | underflow under =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairTwoRight_toList]
            change left.toList ++ under.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
        | empty =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairTwoRight_toList]
            simp only [optionalNodeList, Node.toList, List.append_nil,
              List.nil_append]
            change left.toList = List.filter (fun entry => entry.1 ≠ key)
              (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
            simp
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases routes with
        ⟨leftRoutes, middleRoutes, rightRoutes, separatorsOrdered, leftBefore,
          middleBetween, rightAfter⟩
      simp only [Node.deleteBalancedStep]
      split
      next keyBefore =>
        have middleUnchanged :
            middle.toList.filter (fun entry => entry.1 ≠ key) = middle.toList :=
          filter_key_eq_self middle.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt keyBefore (middleBetween entry member).1
        have rightUnchanged :
            right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
          filter_key_eq_self right.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt (Nat.lt_trans keyBefore separatorsOrdered)
              (rightAfter entry member)
        have localEq := leftInduction leftRoutes
        cases changed : left.deleteBalancedStep key with
        | done updated =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            change updated.toList ++ middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
        | underflow under =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairThreeLeft_toList]
            change under.toList ++ middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
        | empty =>
            rw [changed] at localEq
            simp only [DeleteResult.toList] at localEq
            rw [repairThreeLeft_toList]
            simp only [optionalNodeList, Node.toList, List.append_nil,
              List.nil_append]
            change middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
            simp
      next notLeft =>
        split
        next beforeRight =>
          have leftUnchanged :
              left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
            filter_key_eq_self left.toList key fun entry member equal => by
              subst key
              exact Nat.not_lt_of_ge (Nat.le_of_not_gt notLeft)
                (leftBefore entry member)
          have rightUnchanged :
              right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
            filter_key_eq_self right.toList key fun entry member equal => by
              subst key
              exact Nat.not_le_of_gt beforeRight (rightAfter entry member)
          have localEq := middleInduction middleRoutes
          cases changed : middle.deleteBalancedStep key with
          | done updated =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              change left.toList ++ updated.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
          | underflow under =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              rw [repairThreeMiddle_toList]
              change left.toList ++ under.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
          | empty =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              rw [repairThreeMiddle_toList]
              simp only [optionalNodeList, Node.toList, List.append_nil,
                List.nil_append]
              change left.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
              simp
        next notMiddle =>
          have leftUnchanged :
              left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
            filter_key_eq_self left.toList key fun entry member equal => by
              subst key
              exact Nat.not_lt_of_ge (Nat.le_of_not_gt notLeft)
                (leftBefore entry member)
          have middleUnchanged :
              middle.toList.filter (fun entry => entry.1 ≠ key) = middle.toList :=
            filter_key_eq_self middle.toList key fun entry member equal => by
              subst key
              exact Nat.not_lt_of_ge (Nat.le_of_not_gt notMiddle)
                (middleBetween entry member).2
          have localEq := rightInduction rightRoutes
          cases changed : right.deleteBalancedStep key with
          | done updated =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              change left.toList ++ middle.toList ++ updated.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]
          | underflow under =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              rw [repairThreeRight_toList]
              change left.toList ++ middle.toList ++ under.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]
          | empty =>
              rw [changed] at localEq
              simp only [DeleteResult.toList] at localEq
              rw [repairThreeRight_toList]
              simp only [optionalNodeList, Node.toList, List.append_nil,
                List.nil_append]
              change left.toList ++ middle.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]
              simp

theorem Node.toList_deleteBalanced (node : Node Value) (routes : node.Routes)
    (key : Nat) :
    (node.deleteBalanced key).toList =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  have step := node.deleteBalancedStep_toList routes key
  unfold Node.deleteBalanced
  cases changed : node.deleteBalancedStep key with
  | done updated =>
      rw [changed] at step
      exact step
  | underflow updated =>
      rw [changed] at step
      exact step
  | empty =>
      rw [changed] at step
      simpa [DeleteResult.toList, Node.toList] using step

/-- The public deletion uses the localized borrow/merge algorithm whenever its
full invariant check succeeds. A malformed or unexpectedly rejected candidate
is rebuilt through proved insertion, so callers receive a valid root by
construction rather than relying on an unchecked postcondition. -/
def Node.delete (node : Node Value) (key : Nat) : Node Value :=
  let candidate := node.deleteBalanced key
  if candidate.checkRootValid then candidate
  else
    (Node.leaf ([] : List (Entry Value))).insertAll
      (node.toList.filter fun entry => entry.1 ≠ key)

theorem Node.delete_rootValid (node : Node Value) (key : Nat) :
    (node.delete key).RootValid := by
  simp only [Node.delete]
  split
  next accepted => exact (Node.checkRootValid_iff _).mp accepted
  next =>
    apply Node.insertAll_rootValid
    simp [Node.RootValid, PagedBTree.KeysStrictlySorted]

theorem Node.toList_delete (node : Node Value) (valid : node.RootValid)
    (key : Nat) :
    (node.delete key).toList =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  have localized := node.toList_deleteBalanced valid.routes key
  have filteredSorted :
      PagedBTree.KeysStrictlySorted
        (node.toList.filter (fun entry => entry.1 ≠ key)) :=
    valid.sorted.filter _
  simp only [Node.delete]
  split
  next => exact localized
  next =>
    rw [Node.toList_insertAll]
    · simp only [Node.toList]
      exact fold_orderedInsert_empty _ filteredSorted
    · simp [Node.RootValid, PagedBTree.KeysStrictlySorted]

/-- Local deletion has the exact abstract effect of removing the requested
key.  The proof follows the same routed child as the implementation and uses
the routing bounds to show that every untouched sibling is unchanged by the
abstract filter. -/
theorem Node.deleteStep_toList (node : Node Value) (routes : node.Routes)
    (key : Nat) :
    Node.deletedList (node.deleteStep key) =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  induction node with
  | leaf entries =>
      simp only [Node.deleteStep, PagedBTree.eraseKey_eq_filter, Node.toList]
      generalize remainingEq :
        List.filter (fun entry : Entry Value => entry.1 ≠ key) entries = remaining
      change Node.deletedList
          (match remaining with
          | [] => none
          | remaining => some (.leaf remaining)) = remaining
      cases remaining <;> rfl
  | branch2 left separator right leftInduction rightInduction =>
      rcases routes with ⟨leftRoutes, rightRoutes, leftBefore, rightAfter⟩
      simp only [Node.deleteStep]
      split
      next keyBefore =>
        have rightUnchanged :
            right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
          filter_key_eq_self right.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt keyBefore (rightAfter entry member)
        have localEq := leftInduction leftRoutes
        cases deleted : left.deleteStep key with
        | none =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change right.toList = List.filter (fun entry => entry.1 ≠ key)
              (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
            simp
        | some updated =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change updated.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, ← localEq, rightUnchanged]
      next keyAfter =>
        have leftUnchanged :
            left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
          filter_key_eq_self left.toList key fun entry member equal => by
            subst key
            exact Nat.not_lt_of_ge (Nat.le_of_not_gt keyAfter)
              (leftBefore entry member)
        have localEq := rightInduction rightRoutes
        cases deleted : right.deleteStep key with
        | none =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change left.toList = List.filter (fun entry => entry.1 ≠ key)
              (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
            simp
        | some updated =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change left.toList ++ updated.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ right.toList)
            rw [List.filter_append, leftUnchanged, ← localEq]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases routes with
        ⟨leftRoutes, middleRoutes, rightRoutes, separatorsOrdered, leftBefore,
          middleBetween, rightAfter⟩
      simp only [Node.deleteStep]
      split
      next keyBefore =>
        have middleUnchanged :
            middle.toList.filter (fun entry => entry.1 ≠ key) = middle.toList :=
          filter_key_eq_self middle.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt keyBefore (middleBetween entry member).1
        have rightUnchanged :
            right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
          filter_key_eq_self right.toList key fun entry member equal => by
            subst key
            exact Nat.not_le_of_gt (Nat.lt_trans keyBefore separatorsOrdered)
              (rightAfter entry member)
        have localEq := leftInduction leftRoutes
        cases deleted : left.deleteStep key with
        | none =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
            simp
        | some updated =>
            rw [deleted] at localEq
            simp only [Node.deletedList] at localEq
            change updated.toList ++ middle.toList ++ right.toList =
              List.filter (fun entry => entry.1 ≠ key)
                (left.toList ++ middle.toList ++ right.toList)
            rw [List.filter_append, List.filter_append, ← localEq,
              middleUnchanged, rightUnchanged]
      next notLeft =>
        split
        next beforeRight =>
          have leftUnchanged :
              left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
            filter_key_eq_self left.toList key fun entry member equal => by
              subst key
              exact Nat.not_lt_of_ge (Nat.le_of_not_gt notLeft)
                (leftBefore entry member)
          have rightUnchanged :
              right.toList.filter (fun entry => entry.1 ≠ key) = right.toList :=
            filter_key_eq_self right.toList key fun entry member equal => by
              subst key
              exact Nat.not_le_of_gt beforeRight (rightAfter entry member)
          have localEq := middleInduction middleRoutes
          cases deleted : middle.deleteStep key with
          | none =>
              rw [deleted] at localEq
              simp only [Node.deletedList] at localEq
              change left.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
              simp
          | some updated =>
              rw [deleted] at localEq
              simp only [Node.deletedList] at localEq
              change left.toList ++ updated.toList ++ right.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                ← localEq, rightUnchanged]
        next notMiddle =>
          have leftUnchanged :
              left.toList.filter (fun entry => entry.1 ≠ key) = left.toList :=
            filter_key_eq_self left.toList key fun entry member equal => by
              subst key
              exact Nat.not_lt_of_ge (Nat.le_of_not_gt notLeft)
                (leftBefore entry member)
          have middleUnchanged :
              middle.toList.filter (fun entry => entry.1 ≠ key) = middle.toList :=
            filter_key_eq_self middle.toList key fun entry member equal => by
              subst key
              exact Nat.not_lt_of_ge (Nat.le_of_not_gt notMiddle)
                (middleBetween entry member).2
          have localEq := rightInduction rightRoutes
          cases deleted : right.deleteStep key with
          | none =>
              rw [deleted] at localEq
              simp only [Node.deletedList] at localEq
              change left.toList ++ middle.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]
              simp
          | some updated =>
              rw [deleted] at localEq
              simp only [Node.deletedList] at localEq
              change left.toList ++ middle.toList ++ updated.toList =
                List.filter (fun entry => entry.1 ≠ key)
                  (left.toList ++ middle.toList ++ right.toList)
              rw [List.filter_append, List.filter_append, leftUnchanged,
                middleUnchanged, ← localEq]

theorem Node.toList_deleteUnbalanced (node : Node Value) (routes : node.Routes)
    (key : Nat) :
    (node.deleteUnbalanced key).toList =
      node.toList.filter (fun entry => entry.1 ≠ key) := by
  have step := node.deleteStep_toList routes key
  unfold Node.deleteUnbalanced
  cases deleted : node.deleteStep key with
  | none =>
      rw [deleted] at step
      simpa only [Node.deletedList, Node.toList, Option.getD_none] using step
  | some updated =>
      rw [deleted] at step
      simpa only [Node.deletedList, Option.getD_some] using step

def Tree (Value : Type) := Node Value

def Tree.empty : Tree Value := .leaf []

theorem Node.toList_empty : (Tree.empty : Tree Value).toList = [] := rfl

theorem Node.range_eq_filter (node : Node Value) (lower upper : Nat) :
    node.range lower upper =
      node.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
  rfl

/-- The pruned recursive range iterator is exactly the abstract range filter.
The proof discharges each skipped subtree from its separator interval. -/
theorem Node.rangeScan_eq_range (node : Node Value) (routes : node.Routes)
    (lower upper : Nat) : node.rangeScan lower upper = node.range lower upper := by
  induction node with
  | leaf entries => rfl
  | branch2 left separator right leftInduction rightInduction =>
      rcases routes with ⟨leftRoutes, rightRoutes, leftBefore, rightAfter⟩
      have leftPart :
          (if lower < separator then left.rangeScan lower upper else []) =
            left.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact leftInduction leftRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          exact Nat.not_lt_of_ge inside.1
            (Nat.lt_of_lt_of_le (leftBefore entry member)
              (Nat.le_of_not_gt misses))
      have rightPart :
          (if separator < upper then right.rangeScan lower upper else []) =
            right.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact rightInduction rightRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          exact Nat.not_lt_of_ge
            (Nat.le_trans (Nat.le_of_not_gt misses) (rightAfter entry member))
            inside.2
      unfold Node.rangeScan Node.range Node.toList
      rw [leftPart, rightPart, List.filter_append]
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      rcases routes with
        ⟨leftRoutes, middleRoutes, rightRoutes, separatorsOrdered, leftBefore,
          middleBetween, rightAfter⟩
      have leftPart :
          (if lower < firstSeparator then left.rangeScan lower upper else []) =
            left.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact leftInduction leftRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          exact Nat.not_lt_of_ge inside.1
            (Nat.lt_of_lt_of_le (leftBefore entry member)
              (Nat.le_of_not_gt misses))
      have middlePart :
          (if lower < secondSeparator ∧ firstSeparator < upper then
              middle.rangeScan lower upper else []) =
            middle.toList.filter
              (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact middleInduction middleRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          have between := middleBetween entry member
          apply misses
          constructor <;> omega
      have rightPart :
          (if secondSeparator < upper then right.rangeScan lower upper else []) =
            right.toList.filter (fun entry => lower ≤ entry.1 ∧ entry.1 < upper) := by
        split
        next => exact rightInduction rightRoutes
        next misses =>
          symm
          apply List.filter_eq_nil_iff.2
          intro entry member
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          intro inside
          exact Nat.not_lt_of_ge
            (Nat.le_trans (Nat.le_of_not_gt misses) (rightAfter entry member))
            inside.2
      unfold Node.rangeScan Node.range Node.toList
      rw [leftPart, middlePart, rightPart, List.filter_append,
        List.filter_append]

theorem Node.insert_empty (key : Nat) (value : Value) :
    (Tree.empty : Tree Value).insert key value = .leaf [(key, value)] := by
  rfl

theorem Node.empty_balanced : (Tree.empty : Tree Value).Balanced := by
  simp [Tree.empty, Node.Balanced]

theorem Node.empty_rootValid : (Tree.empty : Tree Value).RootValid := by
  simp [Tree.empty, Node.RootValid, PagedBTree.KeysStrictlySorted]

end RecursiveBPlusTree
end SQLeanite
