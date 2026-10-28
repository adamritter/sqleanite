import SQLeanite.CoreData.BuildDeclaredKeyMapGetOfHidden

namespace SQLeanite
namespace CoreJoin

inductive Side where
  | left
  | right
  deriving Repr, DecidableEq

structure ColumnRef where
  side : Side
  column : Nat
  deriving Repr, DecidableEq

abbrev JoinedRow := Core.Row × Core.Row

def ColumnRef.value (reference : ColumnRef) (row : JoinedRow) : Core.Value :=
  match reference.side with
  | .left => row.1.values[reference.column]?.getD .null
  | .right => row.2.values[reference.column]?.getD .null

inductive Operand where
  | column (reference : ColumnRef)
  | coercedColumn (affinity : SQLite.Affinity) (reference : ColumnRef)
  | literal (value : Core.Value)
  | mergedColumn (affinity : Option SQLite.Affinity) (left right : Nat)
  deriving DecidableEq

def Operand.value : Operand → JoinedRow → Core.Value
  | .column reference, row => reference.value row
  | .coercedColumn affinity reference, row =>
      SQLite.PhysicalAffinity.comparison affinity (reference.value row)
  | .literal value, _ => value
  | .mergedColumn affinity left right, row =>
      let first := (ColumnRef.mk .left left).value row
      let value := if first = .null then (ColumnRef.mk .right right).value row else first
      match affinity with
      | none => value
      | some aff => SQLite.PhysicalAffinity.comparison aff value

def Operand.leftOnly : Operand → Bool
  | .column reference | .coercedColumn _ reference => reference.side == .left
  | .literal _ => true
  | .mergedColumn .. => false

theorem Operand.coercedColumn_null (affinity : SQLite.Affinity) (reference : ColumnRef)
    (row : JoinedRow) (missing : reference.value row = .null) :
    (Operand.coercedColumn affinity reference).value row = .null := by
  simp [Operand.value, missing, SQLite.PhysicalAffinity.comparison_null]

theorem Operand.mergedColumn_missing (left right : Nat) (row : JoinedRow)
    (missing : (ColumnRef.mk .left left).value row = .null) :
    (Operand.mergedColumn none left right).value row = (ColumnRef.mk .right right).value row := by
  simp [Operand.value, missing]

theorem Operand.mergedColumn_present (left right : Nat) (row : JoinedRow)
    (present : (ColumnRef.mk .left left).value row ≠ .null) :
    (Operand.mergedColumn none left right).value row = (ColumnRef.mk .left left).value row := by
  simp [Operand.value, present]

inductive Predicate where
  | truthy (operand : Operand)
  | equalCollated (kind : SQLite.Collation.Kind) (left right : Operand)
  | compareCollated (kind : SQLite.Collation.Kind) (operation : PhysicalQuery.Comparison) (left right : Operand)
  | equal (left right : Operand)
  | notEqual (left right : Operand)
  | compare (operation : PhysicalQuery.Comparison) (left right : Operand)
  | isNull (operand : Operand)
  | not (predicate : Predicate)
  | and (left right : Predicate)
  | or (left right : Predicate)
  deriving DecidableEq

def Predicate.eval : Predicate → JoinedRow → Truth
  | .equalCollated kind left right, row => SQLite.Collation.sqlEquals kind (left.value row) (right.value row)
  | .compareCollated kind operation left right, row =>
      SQLite.Collation.sqlCompare kind operation (left.value row) (right.value row)
  | .truthy operand, row => SQLite.PhysicalAffinity.truth (operand.value row)
  | .equal left right, row => PhysicalQuery.sqlEquals (left.value row) (right.value row)
  | .notEqual left right, row => Truth.not (PhysicalQuery.sqlEquals (left.value row) (right.value row))
  | .compare operation left right, row =>
      PhysicalQuery.sqlCompare operation (left.value row) (right.value row)
  | .isNull operand, row => if operand.value row = .null then .true else .false
  | .not predicate, row => Truth.not (predicate.eval row)
  | .and left right, row => Truth.and (left.eval row) (right.eval row)
  | .or left right, row => Truth.or (left.eval row) (right.eval row)

def Predicate.constant (truth : Bool) : Predicate :=
  if truth then .isNull (.literal .null) else .not (.isNull (.literal .null))

theorem Predicate.constant_eval (truth : Bool) (row : JoinedRow) :
    (Predicate.constant truth).eval row = (if truth then .true else .false) := by
  cases truth <;> rfl

def Predicate.setCollation (kind : SQLite.Collation.Kind) : Predicate → Predicate
  | .equal left right | .equalCollated _ left right => .equalCollated kind left right
  | .notEqual left right => .not (.equalCollated kind left right)
  | .compare operation left right | .compareCollated _ operation left right =>
      .compareCollated kind operation left right
  | .not predicate => .not (Predicate.setCollation kind predicate)
  | .and left right => .and (Predicate.setCollation kind left) (Predicate.setCollation kind right)
  | .or left right => .or (Predicate.setCollation kind left) (Predicate.setCollation kind right)
  | predicate => predicate

/-- Retain the original BINARY constructors used by the rowid planner. -/
def Predicate.withCollation (kind : SQLite.Collation.Kind) (predicate : Predicate) : Predicate :=
  if kind == .binary then predicate else Predicate.setCollation kind predicate

theorem Predicate.withCollation_binary (predicate : Predicate) :
    Predicate.withCollation .binary predicate = predicate := rfl

/-- NULL-safe equality expressed in the existing three-valued predicate
language. Both non-NULL guards suppress UNKNOWN from ordinary equality. -/
def Predicate.isEqual (left right : Operand) : Predicate :=
  .or (.and (.isNull left) (.isNull right))
    (.and (.not (.isNull left)) (.and (.not (.isNull right)) (.equal left right)))

/-- IS TRUE/FALSE is a two-valued truth test, including when its input is NULL. -/
def Predicate.isTruth (operand : Operand) (expected : Bool) : Predicate :=
  .and (.not (.isNull operand)) (if expected then .truthy operand else .not (.truthy operand))

theorem Predicate.isEqual_null_left (left right : Operand) (row : JoinedRow)
    (missing : left.value row = .null) :
    (Predicate.isEqual left right).eval row = (Predicate.isNull right).eval row := by
  cases found : right.value row <;>
    simp [Predicate.isEqual, Predicate.eval, missing, found, Truth.and, Truth.or, Truth.not]

theorem Predicate.isEqual_present (left right : Operand) (row : JoinedRow)
    (leftPresent : left.value row ≠ .null) (rightPresent : right.value row ≠ .null) :
    (Predicate.isEqual left right).eval row = (Predicate.equal left right).eval row := by
  simp only [Predicate.isEqual, Predicate.eval, leftPresent, rightPresent, ↓reduceIte, Truth.not]
  cases PhysicalQuery.sqlEquals (left.value row) (right.value row) <;> rfl

theorem Predicate.isTruth_null (operand : Operand) (expected : Bool) (row : JoinedRow)
    (missing : operand.value row = .null) :
    (Predicate.isTruth operand expected).eval row = .false := by
  cases expected <;>
    simp [Predicate.isTruth, Predicate.eval, missing, Truth.and, Truth.not]

/-- Membership is a disjunction of ordinary, nullable equalities. Empty
lists are false even for a NULL left operand. -/
def Predicate.membership (kind : SQLite.Collation.Kind) (left : Operand) : List Operand → Predicate
  | [] => .not (.isNull (.literal .null))
  | right :: rest => .or (.equalCollated kind left right) (Predicate.membership kind left rest)

theorem Predicate.membership_eval (kind : SQLite.Collation.Kind) (left : Operand)
    (choices : List Operand) (row : JoinedRow) :
    (Predicate.membership kind left choices).eval row =
      choices.foldr (fun right result => Truth.or
        (SQLite.Collation.sqlEquals kind (left.value row) (right.value row)) result) .false := by
  induction choices with
  | nil => rfl
  | cons right rest ih => simp only [Predicate.membership, Predicate.eval, List.foldr_cons, ih]

theorem Predicate.membership_null (kind : SQLite.Collation.Kind) (left : Operand)
    (choices : List Operand) (row : JoinedRow) (missing : left.value row = .null) :
    (Predicate.membership kind left choices).eval row =
      (if choices.isEmpty then .false else .unknown) := by
  rw [Predicate.membership_eval]
  induction choices with
  | nil => rfl
  | cons right rest ih =>
      rw [List.foldr_cons, ih]
      simp only [missing, SQLite.Collation.sqlEquals]
      cases rest <;> rfl

def Predicate.leftOnly : Predicate → Bool
  | .equal left right | .notEqual left right | .compare _ left right |
      .equalCollated _ left right | .compareCollated _ _ left right =>
      left.leftOnly && right.leftOnly
  | .truthy operand | .isNull operand => operand.leftOnly
  | .not predicate => predicate.leftOnly
  | .and left right | .or left right => left.leftOnly && right.leftOnly

private theorem Operand.value_leftOnly {operand : Operand}
    (only : operand.leftOnly = true) (left : Core.Row)
    (firstRight secondRight : Core.Row) :
    operand.value (left, firstRight) = operand.value (left, secondRight) := by
  cases operand with
  | mergedColumn => simp [Operand.leftOnly] at only
  | literal => rfl
  | column reference =>
      cases reference with
      | mk side column =>
          cases side <;> simp [Operand.leftOnly, Operand.value,
            ColumnRef.value] at only ⊢
  | coercedColumn affinity reference =>
      cases reference with
      | mk side column =>
          cases side <;> simp [Operand.leftOnly, Operand.value,
            ColumnRef.value] at only ⊢

theorem Predicate.eval_leftOnly {predicate : Predicate}
    (only : predicate.leftOnly = true) (left : Core.Row)
    (firstRight secondRight : Core.Row) :
    predicate.eval (left, firstRight) = predicate.eval (left, secondRight) := by
  induction predicate with
  | equal first second | notEqual first second | compare _ first second | equalCollated _ first second | compareCollated _ _ first second =>
      simp only [Predicate.leftOnly, Bool.and_eq_true] at only
      simp [Predicate.eval,
        Operand.value_leftOnly only.1 left firstRight secondRight,
        Operand.value_leftOnly only.2 left firstRight secondRight]
  | truthy operand | isNull operand =>
      simp [Predicate.eval,
        Operand.value_leftOnly only left firstRight secondRight]
  | not predicate induction =>
      simp [Predicate.eval, induction only]
  | and first second firstInduction secondInduction =>
      simp only [Predicate.leftOnly, Bool.and_eq_true] at only
      simp [Predicate.eval, firstInduction only.1, secondInduction only.2]
  | or first second firstInduction secondInduction =>
      simp only [Predicate.leftOnly, Bool.and_eq_true] at only
      simp [Predicate.eval, firstInduction only.1, secondInduction only.2]

theorem Predicate.truthy_null (operand : Operand) (row : JoinedRow)
    (missing : operand.value row = .null) : (Predicate.truthy operand).eval row = .unknown := by
  simp [Predicate.eval, missing, SQLite.PhysicalAffinity.truth]

def crossRows (left right : List Core.Row) : List JoinedRow :=
  left.flatMap fun leftRow => right.map fun rightRow => (leftRow, rightRow)

/-- Matches for one left row in the rowid equijoin specification. -/
def rowidMatches (left : Core.Row) (right : List Core.Row) : List JoinedRow :=
  right.filterMap fun rightRow =>
    if left.rowid = rightRow.rowid then some (left, rightRow) else none

def rowidJoinSpec (left right : List Core.Row) : List JoinedRow :=
  left.flatMap fun leftRow => rowidMatches leftRow right

/-- Linear merge join for the primary-key case. Core table rows are already
strictly rowid-sorted, so no preparatory sort or transient cross product is
needed. -/
def mergeRowids : List Core.Row → List Core.Row → List JoinedRow
  | [], _ => []
  | _, [] => []
  | left :: leftRows, right :: rightRows =>
      if left.rowid.value < right.rowid.value then
        mergeRowids leftRows (right :: rightRows)
      else if right.rowid.value < left.rowid.value then
        mergeRowids (left :: leftRows) rightRows
      else
        (left, right) :: mergeRowids leftRows rightRows
termination_by left right => left.length + right.length

private theorem rowidMatches_lt (left right : Core.Row)
    (rightRows : List Core.Row)
    (before : left.rowid.value < right.rowid.value)
    (sorted : (right :: rightRows).Pairwise Core.Row.keyLess) :
    rowidMatches left (right :: rightRows) = [] := by
  simp only [List.pairwise_cons] at sorted
  unfold rowidMatches
  simp only [List.filterMap_cons]
  have unequal : left.rowid ≠ right.rowid := by
    intro equal
    rw [equal] at before
    omega
  rw [if_neg unequal]
  apply List.filterMap_eq_nil_iff.2
  intro candidate member
  have after := sorted.1 candidate member
  rw [if_neg]
  intro equal
  unfold Core.Row.keyLess at after
  rw [← equal] at after
  omega

private theorem rowidJoinSpec_dropRight (left : Core.Row)
    (leftRows : List Core.Row) (right : Core.Row) (rightRows : List Core.Row)
    (before : right.rowid.value < left.rowid.value)
    (sorted : (left :: leftRows).Pairwise Core.Row.keyLess) :
    rowidJoinSpec (left :: leftRows) (right :: rightRows) =
      rowidJoinSpec (left :: leftRows) rightRows := by
  simp only [List.pairwise_cons] at sorted
  unfold rowidJoinSpec
  simp only [List.flatMap_cons]
  have headUnequal : left.rowid ≠ right.rowid := by
    intro equal
    rw [equal] at before
    omega
  have headDrop : rowidMatches left (right :: rightRows) =
      rowidMatches left rightRows := by
    simp [rowidMatches, headUnequal]
  rw [headDrop]
  congr 1
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro candidate member
  have leftBefore := sorted.1 candidate member
  have candidateUnequal : candidate.rowid ≠ right.rowid := by
    intro equal
    unfold Core.Row.keyLess at leftBefore
    rw [equal] at leftBefore
    omega
  simp [rowidMatches, candidateUnequal]

private theorem rowidJoinSpec_equal (left : Core.Row) (leftRows : List Core.Row)
    (right : Core.Row) (rightRows : List Core.Row)
    (equal : left.rowid.value = right.rowid.value)
    (leftSorted : (left :: leftRows).Pairwise Core.Row.keyLess)
    (rightSorted : (right :: rightRows).Pairwise Core.Row.keyLess) :
    rowidJoinSpec (left :: leftRows) (right :: rightRows) =
      (left, right) :: rowidJoinSpec leftRows rightRows := by
  have rowidEqual : left.rowid = right.rowid := by
    apply FileFormat.SignedInteger.ext
    exact equal
  simp only [List.pairwise_cons] at leftSorted rightSorted
  unfold rowidJoinSpec
  simp only [List.flatMap_cons]
  have headMatches : rowidMatches left (right :: rightRows) = [(left, right)] := by
    unfold rowidMatches
    simp only [List.filterMap_cons, if_pos rowidEqual]
    have tailEmpty : List.filterMap
        (fun candidate =>
          if left.rowid = candidate.rowid then some (left, candidate) else none)
        rightRows = [] := by
      apply List.filterMap_eq_nil_iff.2
      intro candidate member
      have after := rightSorted.1 candidate member
      rw [if_neg]
      intro candidateEqual
      unfold Core.Row.keyLess at after
      rw [← candidateEqual, rowidEqual] at after
      omega
    rw [tailEmpty]
  rw [headMatches]
  simp only [List.singleton_append, List.cons.injEq, true_and]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro candidate member
  have after := leftSorted.1 candidate member
  have candidateUnequal : candidate.rowid ≠ right.rowid := by
    intro candidateEqual
    unfold Core.Row.keyLess at after
    rw [candidateEqual, ← rowidEqual] at after
    omega
  simp [rowidMatches, candidateUnequal]

/-- The linear merge is exactly the nested-loop rowid equijoin specification,
not merely a set approximation or cardinality result. -/
theorem mergeRowids_eq_spec (left right : List Core.Row)
    (leftSorted : left.Pairwise Core.Row.keyLess)
    (rightSorted : right.Pairwise Core.Row.keyLess) :
    mergeRowids left right = rowidJoinSpec left right := by
  induction left generalizing right with
  | nil => simp [mergeRowids, rowidJoinSpec]
  | cons left leftRows leftInduction =>
      induction right with
      | nil => simp [mergeRowids, rowidJoinSpec, rowidMatches]
      | cons right rightRows rightInduction =>
        simp only [mergeRowids]
        split
        next leftBefore =>
          rw [leftInduction (right :: rightRows) leftSorted.tail rightSorted]
          unfold rowidJoinSpec
          simp only [List.flatMap_cons]
          rw [rowidMatches_lt left right rightRows leftBefore rightSorted]
          simp
        next notLeftBefore =>
          split
          next rightBefore =>
            rw [rightInduction rightSorted.tail]
            exact (rowidJoinSpec_dropRight left leftRows right rightRows
              rightBefore leftSorted).symm
          next notRightBefore =>
            have equal : left.rowid.value = right.rowid.value := by omega
            rw [leftInduction rightRows leftSorted.tail rightSorted.tail]
            exact (rowidJoinSpec_equal left leftRows right rightRows equal
              leftSorted rightSorted).symm

/-- Keep the prefix of a primary table which can still match a right-hand
row.  The physical range reader uses this predicate before the logical merge
join, so a small right table does not force a scan of an unrelated large left
table. -/
def rowidAtMost (bound : Core.Integer) (row : Core.Row) : Bool :=
  decide (row.rowid.value ≤ bound.value)

private theorem rowidMatches_eq_nil_of_bound (left : Core.Row)
    (right : List Core.Row) (bound : Core.Integer)
    (leftAfter : bound.value < left.rowid.value)
    (rightBounded : ∀ row ∈ right, row.rowid.value ≤ bound.value) :
    rowidMatches left right = [] := by
  unfold rowidMatches
  apply List.filterMap_eq_nil_iff.2
  intro row member
  rw [if_neg]
  intro equal
  have bounded := rightBounded row member
  rw [← equal] at bounded
  omega

/-- Discarding left rows above an upper bound loses no rowid join result when
all right rows are at or below that bound. -/
theorem rowidJoinSpec_filter_left_atMost (left right : List Core.Row)
    (bound : Core.Integer)
    (rightBounded : ∀ row ∈ right, row.rowid.value ≤ bound.value) :
    rowidJoinSpec (left.filter (rowidAtMost bound)) right =
      rowidJoinSpec left right := by
  induction left with
  | nil => rfl
  | cons row rows induction =>
      by_cases before : row.rowid.value ≤ bound.value
      · have kept : rowidAtMost bound row = true := by
          simp [rowidAtMost, before]
        simp only [List.filter_cons, kept, Bool.true_eq, if_true]
        change rowidMatches row right ++
            rowidJoinSpec (rows.filter (rowidAtMost bound)) right =
          rowidMatches row right ++ rowidJoinSpec rows right
        rw [induction]
      · have after : bound.value < row.rowid.value := by omega
        have noMatches := rowidMatches_eq_nil_of_bound row right bound after
          rightBounded
        have dropped : rowidAtMost bound row = false := by
          simp [rowidAtMost, before]
        simp only [List.filter_cons, dropped, Bool.false_eq, if_false]
        change rowidJoinSpec (rows.filter (rowidAtMost bound)) right =
          rowidMatches row right ++ rowidJoinSpec rows right
        rw [noMatches, List.nil_append, induction]

/-- The page-directed bounded-left merge is the complete nested-loop rowid
join, not merely a sound subset. -/
theorem mergeRowids_filter_left_atMost_eq_spec (left right : List Core.Row)
    (bound : Core.Integer)
    (leftSorted : left.Pairwise Core.Row.keyLess)
    (rightSorted : right.Pairwise Core.Row.keyLess)
    (rightBounded : ∀ row ∈ right, row.rowid.value ≤ bound.value) :
    mergeRowids (left.filter (rowidAtMost bound)) right =
      rowidJoinSpec left right := by
  rw [mergeRowids_eq_spec (left.filter (rowidAtMost bound)) right
    (leftSorted.filter _) rightSorted]
  exact rowidJoinSpec_filter_left_atMost left right bound rightBounded

def selects (predicate : Option Predicate) (row : JoinedRow) : Bool :=
  match predicate with
  | none => true
  | some predicate => predicate.eval row = .true

def matchingRows (on where_ : Option Predicate) (rows : List JoinedRow) :
    List JoinedRow :=
  rows.filter fun row => selects on row && selects where_ row

theorem matchingRows_unconstrained (rows : List JoinedRow) :
    matchingRows none none rows = rows := by
  simp [matchingRows, selects]

inductive JoinKind where
  | inner
  | left
  deriving DecidableEq, Repr

private def zeroInteger : Core.Integer := ⟨0, by simp, by decide⟩

/-- A synthetic right row for LEFT JOIN null extension. Its rowid is never
observable as a SQL rowid in the supported projection language; every declared
right column is represented by NULL. -/
def nullRow (width : Nat) : Core.Row :=
  ⟨zeroInteger, List.replicate width .null⟩

def selectsLeft (predicate : Predicate) (row : Core.Row) : Bool :=
  selects (some predicate) (row, nullRow 0)

theorem selects_leftOnly {predicate : Predicate}
    (only : predicate.leftOnly = true) (left right : Core.Row) :
    selects (some predicate) (left, right) = selectsLeft predicate left := by
  simp only [selects, selectsLeft]
  rw [Predicate.eval_leftOnly only left right (nullRow 0)]

end CoreJoin

end SQLeanite
