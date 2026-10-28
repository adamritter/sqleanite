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

theorem findKey?_eq_some_of_mem
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

end RecursiveBPlusTree

end SQLeanite
