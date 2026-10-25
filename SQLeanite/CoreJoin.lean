import SQLeanite.SQLite.Collation
import SQLeanite.SQLite.PhysicalAffinity
import SQLeanite.Core
import SQLeanite.CoreDistinct
import SQLeanite.PhysicalQuery

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
  deriving DecidableEq

def Operand.value : Operand → JoinedRow → Core.Value
  | .column reference, row => reference.value row
  | .coercedColumn affinity reference, row =>
      SQLite.PhysicalAffinity.comparison affinity (reference.value row)
  | .literal value, _ => value

def Operand.leftOnly : Operand → Bool
  | .column reference | .coercedColumn _ reference => reference.side == .left
  | .literal _ => true

theorem Operand.coercedColumn_null (affinity : SQLite.Affinity) (reference : ColumnRef)
    (row : JoinedRow) (missing : reference.value row = .null) :
    (Operand.coercedColumn affinity reference).value row = .null := by
  simp [Operand.value, missing, SQLite.PhysicalAffinity.comparison_null]

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

private theorem filterMappedRight_leftOnly (on : Option Predicate)
    {where_ : Predicate} (only : where_.leftOnly = true)
    (left : Core.Row) (right : List Core.Row) :
    ((right.map fun row => (left, row)).filter fun joined =>
        selects on joined && selects (some where_) joined) =
      if selectsLeft where_ left then
        (right.map fun row => (left, row)).filter (selects on)
      else [] := by
  induction right with
  | nil => simp
  | cons row rows induction =>
      simp only [List.map_cons, List.filter_cons]
      rw [selects_leftOnly only left row]
      by_cases passes : selectsLeft where_ left = true <;>
        simp [List.filter_cons, passes, induction]

private theorem matchingMappedRight_leftOnly (on : Option Predicate)
    {where_ : Predicate} (only : where_.leftOnly = true)
    (left : Core.Row) (right : List Core.Row) :
    matchingRows on (some where_) (right.map fun row => (left, row)) =
      if selectsLeft where_ left then
        matchingRows on none (right.map fun row => (left, row))
      else [] := by
  unfold matchingRows
  have withoutWhere : (fun row : JoinedRow => selects on row && selects none row) =
      selects on := by
    funext row
    simp [selects]
  rw [withoutWhere]
  exact filterMappedRight_leftOnly on only left right

theorem matchingRows_pushLeft (on : Option Predicate)
    {where_ : Predicate} (only : where_.leftOnly = true)
    (left right : List Core.Row) :
    matchingRows on (some where_) (crossRows left right) =
      matchingRows on none
        (crossRows (left.filter (selectsLeft where_)) right) := by
  induction left with
  | nil => rfl
  | cons row rows induction =>
      rw [show crossRows (row :: rows) right =
        (right.map fun rightRow => (row, rightRow)) ++
          crossRows rows right by rfl]
      rw [show matchingRows on (some where_)
          ((right.map fun rightRow => (row, rightRow)) ++
            crossRows rows right) =
        matchingRows on (some where_)
            (right.map fun rightRow => (row, rightRow)) ++
          matchingRows on (some where_) (crossRows rows right) by
            simp [matchingRows]]
      rw [matchingMappedRight_leftOnly on only row right]
      rw [induction]
      by_cases passes : selectsLeft where_ row = true <;>
        simp [List.filter_cons, passes, crossRows, matchingRows]

def leftOuterFor (on : Option Predicate) (rightWidth : Nat)
    (left : Core.Row) (right : List Core.Row) : List JoinedRow :=
  let candidates := (right.map fun row => (left, row)).filter (selects on)
  if candidates.isEmpty then [(left, nullRow rightWidth)] else candidates

def leftOuterRows (on : Option Predicate) (rightWidth : Nat)
    (left right : List Core.Row) : List JoinedRow :=
  left.flatMap fun row => leftOuterFor on rightWidth row right

theorem leftOuterFor_unconstrained_empty (rightWidth : Nat) (left : Core.Row) :
    leftOuterFor none rightWidth left [] = [(left, nullRow rightWidth)] := rfl

theorem leftOuterFor_nonempty (on : Option Predicate) (rightWidth : Nat)
    (left : Core.Row) (right : List Core.Row) :
    (leftOuterFor on rightWidth left right).isEmpty = false := by
  unfold leftOuterFor
  generalize (List.map (fun row => (left, row)) right).filter (selects on) = candidates
  cases empty : candidates.isEmpty <;> simp [empty]

theorem leftOuterFor_eq_null_of_no_match (on : Option Predicate)
    (rightWidth : Nat) (left : Core.Row) (right : List Core.Row)
    (noneMatch : ((right.map fun row => (left, row)).filter (selects on)).isEmpty = true) :
    leftOuterFor on rightWidth left right = [(left, nullRow rightWidth)] := by
  simp [leftOuterFor, noneMatch]

theorem leftOuterFor_eq_matches_of_some_match (on : Option Predicate)
    (rightWidth : Nat) (left : Core.Row) (right : List Core.Row)
    (someMatch : ((right.map fun row => (left, row)).filter (selects on)).isEmpty = false) :
    leftOuterFor on rightWidth left right =
      (right.map fun row => (left, row)).filter (selects on) := by
  simp [leftOuterFor, someMatch]

theorem leftOuterFor_preserves_left (on : Option Predicate) (rightWidth : Nat)
    (left : Core.Row) (right : List Core.Row) (joined : JoinedRow)
    (member : joined ∈ leftOuterFor on rightWidth left right) :
    joined.1 = left := by
  simp only [leftOuterFor] at member
  split at member
  · simp only [List.mem_singleton] at member
    subst joined
    rfl
  · simp only [List.mem_filter, List.mem_map] at member
    rcases member.1 with ⟨rightRow, _, equal⟩
    rw [← equal]

private theorem filterLeftOuterFor_leftOnly (on : Option Predicate)
    (rightWidth : Nat) {where_ : Predicate}
    (only : where_.leftOnly = true) (left : Core.Row)
    (right : List Core.Row) :
    (leftOuterFor on rightWidth left right).filter (selects (some where_)) =
      if selectsLeft where_ left then leftOuterFor on rightWidth left right
      else [] := by
  by_cases passes : selectsLeft where_ left = true
  · rw [if_pos passes]
    apply List.filter_eq_self.2
    intro joined member
    rw [selects_leftOnly only joined.1 joined.2]
    rw [leftOuterFor_preserves_left on rightWidth left right joined member]
    exact passes
  · rw [if_neg passes]
    apply List.filter_eq_nil_iff.2
    intro joined member
    simp only [Bool.not_eq_true]
    rw [selects_leftOnly only joined.1 joined.2]
    rw [leftOuterFor_preserves_left on rightWidth left right joined member]
    cases result : selectsLeft where_ left <;> simp_all

theorem leftOuterRows_pushLeft (on : Option Predicate) (rightWidth : Nat)
    {where_ : Predicate} (only : where_.leftOnly = true)
    (left right : List Core.Row) :
    (leftOuterRows on rightWidth left right).filter (selects (some where_)) =
      leftOuterRows on rightWidth (left.filter (selectsLeft where_)) right := by
  induction left with
  | nil => rfl
  | cons row rows induction =>
      rw [show leftOuterRows on rightWidth (row :: rows) right =
        leftOuterFor on rightWidth row right ++
          leftOuterRows on rightWidth rows right by rfl]
      rw [List.filter_append]
      rw [filterLeftOuterFor_leftOnly on rightWidth only row right]
      rw [induction]
      by_cases passes : selectsLeft where_ row = true <;>
        simp [List.filter_cons, passes, leftOuterRows]

def rowidOn (leftPrimaryKey rightPrimaryKey : Nat) : Predicate :=
  .equal (.column ⟨.left, leftPrimaryKey⟩)
    (.column ⟨.right, rightPrimaryKey⟩)

private theorem selects_rowidOn (leftSchema rightSchema : Core.Schema)
    (left right : Core.Row)
    (leftWellFormed : left.WellFormed leftSchema)
    (rightWellFormed : right.WellFormed rightSchema) :
    selects (some (rowidOn leftSchema.primaryKey rightSchema.primaryKey))
      (left, right) = decide (left.rowid = right.rowid) := by
  have leftValue : left.values[leftSchema.primaryKey]?.getD .null =
      .integer left.rowid := by
    rw [leftWellFormed.2.1]
    rfl
  have rightValue : right.values[rightSchema.primaryKey]?.getD .null =
      .integer right.rowid := by
    rw [rightWellFormed.2.1]
    rfl
  simp [selects, rowidOn, Predicate.eval, Operand.value, ColumnRef.value,
    leftValue, rightValue, PhysicalQuery.sqlEquals]

private theorem rowidMatches_eq_filter (leftSchema rightSchema : Core.Schema)
    (left : Core.Row) (right : List Core.Row)
    (leftWellFormed : left.WellFormed leftSchema)
    (rightWellFormed : ∀ row ∈ right, row.WellFormed rightSchema) :
    rowidMatches left right =
      (right.map fun row => (left, row)).filter
        (selects (some (rowidOn leftSchema.primaryKey rightSchema.primaryKey))) := by
  induction right with
  | nil => rfl
  | cons row rows induction =>
      have rowWellFormed := rightWellFormed row (by simp)
      have rowsWellFormed : ∀ candidate ∈ rows,
          candidate.WellFormed rightSchema := by
        intro candidate member
        exact rightWellFormed candidate (by simp [member])
      simp only [rowidMatches, List.filterMap_cons, List.map_cons,
        List.filter_cons]
      rw [selects_rowidOn leftSchema rightSchema left row leftWellFormed
        rowWellFormed]
      by_cases equal : left.rowid = row.rowid
      · rw [if_pos equal]
        have decision : decide (left.rowid = row.rowid) = true :=
          decide_eq_true equal
        rw [decision]
        simp only [Bool.true_eq, if_true, List.cons.injEq, true_and]
        exact induction rowsWellFormed
      · rw [if_neg equal]
        have decision : decide (left.rowid = row.rowid) = false :=
          decide_eq_false equal
        rw [decision]
        simp only [Bool.false_eq, if_false]
        exact induction rowsWellFormed

theorem rowidJoinSpec_eq_matchingRows (leftSchema rightSchema : Core.Schema)
    (left right : List Core.Row)
    (leftWellFormed : ∀ row ∈ left, row.WellFormed leftSchema)
    (rightWellFormed : ∀ row ∈ right, row.WellFormed rightSchema) :
    rowidJoinSpec left right =
      matchingRows
        (some (rowidOn leftSchema.primaryKey rightSchema.primaryKey)) none
        (crossRows left right) := by
  induction left with
  | nil => simp [rowidJoinSpec, matchingRows, crossRows]
  | cons row rows induction =>
      have rowWellFormed := leftWellFormed row (by simp)
      have rowsWellFormed : ∀ candidate ∈ rows,
          candidate.WellFormed leftSchema := by
        intro candidate member
        exact leftWellFormed candidate (by simp [member])
      simp only [rowidJoinSpec, crossRows, List.flatMap_cons, matchingRows,
        List.filter_append]
      rw [rowidMatches_eq_filter leftSchema rightSchema row right rowWellFormed
        rightWellFormed]
      have tail := induction rowsWellFormed
      unfold rowidJoinSpec matchingRows crossRows at tail
      rw [tail]
      congr 1
      apply List.filter_congr
      intro pair member
      simp [selects]

def projectRow (columns : List Operand) (row : JoinedRow) :
    List Core.Value :=
  columns.map fun column => column.value row

theorem projectRow_length (columns : List Operand) (row : JoinedRow) :
    (projectRow columns row).length = columns.length := by
  simp [projectRow]

/-- Existing column projections keep exactly their original values when
embedded in the operand projection used by literal and column atoms. -/
theorem projectRow_columns (columns : List ColumnRef) (row : JoinedRow) :
    projectRow (columns.map Operand.column) row = columns.map (fun column => column.value row) := by
  simp [projectRow, Operand.value, List.map_map]

def rowLess : List (ColumnRef × Bool) → JoinedRow → JoinedRow → Bool
  | [], _, _ => false
  | term :: terms, left, right =>
      let order := PhysicalQuery.compareValue (term.1.value left) (term.1.value right)
      if order == .eq then rowLess terms left right
      else if term.2 then order == .gt else order == .lt

def insertOrdered (terms : List (ColumnRef × Bool)) (row : JoinedRow) :
    List JoinedRow → List JoinedRow
  | [] => [row]
  | candidate :: rows =>
      if rowLess terms row candidate then row :: candidate :: rows
      else candidate :: insertOrdered terms row rows

theorem insertOrdered_perm (terms : List (ColumnRef × Bool)) (row : JoinedRow)
    (rows : List JoinedRow) :
    (insertOrdered terms row rows).Perm (row :: rows) := by
  induction rows with
  | nil => exact List.Perm.refl _
  | cons candidate rows induction =>
      unfold insertOrdered
      split
      · exact List.Perm.refl _
      · exact (induction.cons candidate).trans (List.Perm.swap row candidate rows)

theorem foldInsertOrdered_perm (terms : List (ColumnRef × Bool))
    (rows accumulator : List JoinedRow) :
    (rows.foldl (fun sorted row => insertOrdered terms row sorted) accumulator).Perm
      (rows ++ accumulator) := by
  induction rows generalizing accumulator with
  | nil => exact List.Perm.refl _
  | cons row rows induction =>
      have tail := induction (insertOrdered terms row accumulator)
      have inserted := (insertOrdered_perm terms row accumulator).append_left rows
      exact tail.trans (inserted.trans List.perm_middle)

/-- Compare projected SQL numeric keys while retaining the first original
joined row. Its unprojected values remain available to ORDER BY. -/
def distinctRows (columns : List Operand) (rows : List JoinedRow) : List JoinedRow :=
  Core.stableDistinctBy (fun row => Core.distinctRowKey (projectRow columns row)) rows

theorem distinctRows_keys (columns : List Operand) (rows : List JoinedRow)
    (key : List Core.Value) :
    key ∈ (distinctRows columns rows).map (fun row => Core.distinctRowKey (projectRow columns row)) ↔
      key ∈ rows.map (fun row => Core.distinctRowKey (projectRow columns row)) :=
  Core.mem_keys_stableDistinctBy _ _ _

theorem distinctRows_key_nodup (columns : List Operand) (rows : List JoinedRow) :
    ((distinctRows columns rows).map (fun row => Core.distinctRowKey (projectRow columns row))).Nodup :=
  Core.stableDistinctBy_key_nodup _ _

structure OrderTerm where
  reference : ColumnRef
  descending : Bool := false
  nullsFirst : Option Bool := none
  collation : SQLite.Collation.Kind := .binary

def OrderTerm.compareValues (term : OrderTerm) (left right : Core.Value) : Ordering :=
  match left, right with
  | .null, .null => .eq
  | .null, _ => if term.nullsFirst.getD (!term.descending) then .lt else .gt
  | _, .null => if term.nullsFirst.getD (!term.descending) then .gt else .lt
  | _, _ =>
      if term.descending then SQLite.Collation.compareValue term.collation right left
      else SQLite.Collation.compareValue term.collation left right

theorem OrderTerm.compareValues_null_left (term : OrderTerm) (right : Core.Value)
    (present : right ≠ .null) : term.compareValues .null right =
      if term.nullsFirst.getD (!term.descending) then .lt else .gt := by
  cases right <;> simp_all [OrderTerm.compareValues]

theorem OrderTerm.compareValues_null_right (term : OrderTerm) (left : Core.Value)
    (present : left ≠ .null) : term.compareValues left .null =
      if term.nullsFirst.getD (!term.descending) then .gt else .lt := by
  cases left <;> simp_all [OrderTerm.compareValues]

def orderedRowLess : List OrderTerm → JoinedRow → JoinedRow → Bool
  | [], _, _ => false
  | term :: terms, left, right =>
      let order := term.compareValues (term.reference.value left) (term.reference.value right)
      if order == .eq then orderedRowLess terms left right else order == .lt

def orderedRowLe (terms : List OrderTerm) (left right : JoinedRow) : Bool :=
  !orderedRowLess terms right left

structure Query where
  columns : List Operand
  on : Option Predicate
  kind : JoinKind := .inner
  rightWidth : Nat := 0
  where_ : Option Predicate := none
  orderBy : List OrderTerm := []
  limit : Option Nat := none
  offset : Nat := 0
  distinct : Bool := false
  distinctScanOrder : List (ColumnRef × Bool) := []
  lookupScanOrder : List (ColumnRef × Bool) := []

/-- Stable merge sort by the same strict order, replacing an O(n^2) insertion
sort. `a ≤ b` is `¬ (b < a)`, so equal rows keep input order. -/
def rowLe (terms : List (ColumnRef × Bool)) (left right : JoinedRow) : Bool :=
  !rowLess terms right left

def Query.orderedRows (query : Query) (rows : List JoinedRow) : List JoinedRow :=
  if query.orderBy.isEmpty then rows
  else rows.mergeSort (orderedRowLe query.orderBy)

theorem Query.orderedRows_perm (query : Query) (rows : List JoinedRow) :
    (query.orderedRows rows).Perm rows := by
  by_cases empty : query.orderBy.isEmpty
  · simp [Query.orderedRows, empty]
  · simpa [Query.orderedRows, empty] using List.mergeSort_perm rows (orderedRowLe query.orderBy)

/-- DISTINCT chooses its original representative in physical scan order.
The SQL translator supplies a rowid traversal order when ORDER BY is satisfied
by ordered table scans. A point-lookup plan already fixes its traversal;
the final output sorter remains independent. -/
def Query.distinctInputRows (query : Query) (rows : List JoinedRow) : List JoinedRow :=
  if !query.lookupScanOrder.isEmpty || query.distinctScanOrder.isEmpty then rows
  else rows.mergeSort (rowLe query.distinctScanOrder)

theorem Query.distinctInputRows_perm (query : Query) (rows : List JoinedRow) :
    (query.distinctInputRows rows).Perm rows := by
  by_cases empty : (!query.lookupScanOrder.isEmpty || query.distinctScanOrder.isEmpty) = true
  · simp [Query.distinctInputRows, empty]
  · simpa [Query.distinctInputRows, empty] using
      List.mergeSort_perm rows (rowLe query.distinctScanOrder)

/-- The SQL translator can recognize a right scan probing the left rowid.
This order applies before DISTINCT, stable output sorting and row windows. -/
def Query.lookupInputRows (query : Query) (rows : List JoinedRow) : List JoinedRow :=
  if query.lookupScanOrder.isEmpty then rows
  else rows.mergeSort (rowLe query.lookupScanOrder)

theorem Query.lookupInputRows_perm (query : Query) (rows : List JoinedRow) :
    (query.lookupInputRows rows).Perm rows := by
  by_cases empty : query.lookupScanOrder.isEmpty
  · simp [Query.lookupInputRows, empty]
  · simpa [Query.lookupInputRows, empty] using
      List.mergeSort_perm rows (rowLe query.lookupScanOrder)

def Query.finishRows (query : Query) (rows : List JoinedRow) : List JoinedRow :=
  let rows := query.lookupInputRows rows
  let rows := if query.distinct then query.distinctInputRows rows else rows
  let rows := if query.distinct then distinctRows query.columns rows else rows
  let rows := (query.orderedRows rows).drop query.offset
  match query.limit with
  | none => rows
  | some limit => rows.take limit

theorem Query.finishRows_limit_zero (query : Query) (rows : List JoinedRow)
    (zero : query.limit = some 0) : query.finishRows rows = [] := by
  simp [Query.finishRows, zero]

def Query.selectedRows (query : Query) (left right : List Core.Row) :
    List JoinedRow :=
  let selected := match query.kind with
    | .inner => matchingRows query.on query.where_ (crossRows left right)
    | .left =>
        (leftOuterRows query.on query.rightWidth left right).filter
          (selects query.where_)
  query.finishRows selected

def Query.eval (query : Query) (left right : List Core.Row) :
    List (List Core.Value) :=
  (query.selectedRows left right).map (projectRow query.columns)

theorem Query.eval_limit_zero (query : Query) (left right : List Core.Row)
    (zero : query.limit = some 0) : query.eval left right = [] := by
  simp [Query.eval, Query.selectedRows, Query.finishRows, zero]

theorem Query.finishRows_nil (query : Query) : query.finishRows [] = [] := by
  simp [Query.finishRows, Query.lookupInputRows, Query.distinctInputRows,
    Query.orderedRows, distinctRows, Core.stableDistinctBy]
  split <;> rfl

theorem Query.eval_empty_left (query : Query) (right : List Core.Row) :
    query.eval [] right = [] := by
  cases kind : query.kind <;>
    simp [Query.eval, Query.selectedRows, kind, crossRows, matchingRows,
      leftOuterRows, Query.finishRows_nil]

theorem Query.eval_empty_right_on (query : Query) (left : List Core.Row)
    (on : Option Predicate) (outer : query.kind = .left) :
    { query with on }.eval left [] = query.eval left [] := by
  simp [Query.eval, Query.selectedRows, outer, leftOuterRows, leftOuterFor,
    Query.finishRows, Query.lookupInputRows, Query.distinctInputRows, Query.orderedRows]

/-- Execute the certified primary-key join after a page reader has discarded
left rows above the greatest possible right key. -/
def Query.evalPrimaryKeyCandidates (query : Query)
    (leftCandidates right : List Core.Row) : List (List Core.Value) :=
  (query.finishRows (mergeRowids leftCandidates right)).map
    (projectRow query.columns)

def Query.evalPrimaryKeyBounded (query : Query) (left right : List Core.Row)
    (bound : Core.Integer) : List (List Core.Value) :=
  query.evalPrimaryKeyCandidates (left.filter (rowidAtMost bound)) right

/-- The bounded page-directed join is extensionally the ordinary SQL inner
join for the primary-key equality shape.  ORDER BY, LIMIT and projection stay
inside `finishRows`/`projectRow`, so this is an equality of complete query
results rather than only of intermediate pairs. -/
theorem Query.evalPrimaryKeyBounded_eq_eval (query : Query)
    (leftSchema rightSchema : Core.Schema) (left right : List Core.Row)
    (bound : Core.Integer)
    (onShape : query.on = some
      (rowidOn leftSchema.primaryKey rightSchema.primaryKey))
    (whereShape : query.where_ = none) (kindShape : query.kind = .inner)
    (leftWellFormed : Core.RowsWellFormed leftSchema left)
    (rightWellFormed : Core.RowsWellFormed rightSchema right)
    (rightBounded : ∀ row ∈ right, row.rowid.value ≤ bound.value) :
    query.evalPrimaryKeyBounded left right bound = query.eval left right := by
  unfold Query.evalPrimaryKeyBounded Query.evalPrimaryKeyCandidates Query.eval
  rw [mergeRowids_filter_left_atMost_eq_spec left right bound
    leftWellFormed.2 rightWellFormed.2 rightBounded]
  rw [rowidJoinSpec_eq_matchingRows leftSchema rightSchema left right
    leftWellFormed.1 rightWellFormed.1]
  simp [Query.selectedRows, onShape, whereShape, kindShape]

/-- Candidate form used by the IO boundary: the byte-level range theorem
supplies `candidatesEq`, while this theorem discharges all remaining SQL join
semantics. -/
theorem Query.evalPrimaryKeyCandidates_eq_eval (query : Query)
    (leftSchema rightSchema : Core.Schema) (left right candidates : List Core.Row)
    (bound : Core.Integer)
    (candidatesEq : candidates = left.filter (rowidAtMost bound))
    (onShape : query.on = some
      (rowidOn leftSchema.primaryKey rightSchema.primaryKey))
    (whereShape : query.where_ = none) (kindShape : query.kind = .inner)
    (leftWellFormed : Core.RowsWellFormed leftSchema left)
    (rightWellFormed : Core.RowsWellFormed rightSchema right)
    (rightBounded : ∀ row ∈ right, row.rowid.value ≤ bound.value) :
    query.evalPrimaryKeyCandidates candidates right = query.eval left right := by
  subst candidates
  exact query.evalPrimaryKeyBounded_eq_eval leftSchema rightSchema left right
    bound onShape whereShape kindShape leftWellFormed rightWellFormed rightBounded

/-- Empty right input is the other branch of the cold join reader; it is a
complete inner-join result without touching the left tree. -/
theorem Query.evalPrimaryKeyCandidates_empty_right_eq_eval (query : Query)
    (leftSchema rightSchema : Core.Schema) (left : List Core.Row)
    (onShape : query.on = some
      (rowidOn leftSchema.primaryKey rightSchema.primaryKey))
    (whereShape : query.where_ = none) (kindShape : query.kind = .inner) :
    query.evalPrimaryKeyCandidates [] [] = query.eval left [] := by
  have crossEmpty : crossRows left [] = [] := by
    induction left with
    | nil => rfl
    | cons _ rows induction => simp [crossRows, induction]
  simp [Query.evalPrimaryKeyCandidates, Query.eval, Query.selectedRows,
    onShape, whereShape, kindShape, mergeRowids, crossEmpty, matchingRows]

/-- Live join planner: a pure primary-key equijoin with no additional WHERE
filter uses the linear merge; every other shape retains the general 3VL nested
loop. A WHERE predicate whose operands all reference the left side is pushed
below either an inner or left outer join, avoiding construction of pairs for
discarded left rows. ORDER BY and LIMIT are applied after every access path. -/
def Query.selectedRowsPlanned (query : Query)
    (left right : Core.Table) : List JoinedRow :=
  if _merge : query.on =
        some (rowidOn left.schema.primaryKey right.schema.primaryKey) ∧
      query.where_ = none ∧ query.kind = .inner then
    query.finishRows (mergeRowids left.rows right.rows)
  else match query.where_ with
    | some where_ =>
        if _leftOnly : where_.leftOnly = true then
          let pushedLeft := left.rows.filter (selectsLeft where_)
          let selected := match query.kind with
            | .inner => matchingRows query.on none (crossRows pushedLeft right.rows)
            | .left => leftOuterRows query.on query.rightWidth pushedLeft right.rows
          query.finishRows selected
        else query.selectedRows left.rows right.rows
    | none => query.selectedRows left.rows right.rows

def Query.evalPlanned (query : Query) (left right : Core.Table) :
    List (List Core.Value) :=
  (query.selectedRowsPlanned left right).map (projectRow query.columns)

theorem Query.evalPlanned_eq_eval (query : Query)
    (left right : Core.Table) :
    query.evalPlanned left right = query.eval left.rows right.rows := by
  unfold Query.evalPlanned Query.eval
  apply congrArg (List.map (projectRow query.columns))
  unfold Query.selectedRowsPlanned
  split
  next mergeShape =>
    rcases mergeShape with ⟨onShape, whereShape, kindShape⟩
    rw [mergeRowids_eq_spec left.rows right.rows
      left.rowsWellFormed.2 right.rowsWellFormed.2]
    rw [rowidJoinSpec_eq_matchingRows left.schema right.schema
      left.rows right.rows left.rowsWellFormed.1 right.rowsWellFormed.1]
    simp [Query.selectedRows, onShape, whereShape, kindShape]
  next notMerge =>
    cases whereShape : query.where_ with
    | none => rfl
    | some where_ =>
        simp only [whereShape]
        split
        next leftOnly =>
          unfold Query.selectedRows
          simp only [whereShape]
          cases kindShape : query.kind with
          | inner =>
              simp only [kindShape]
              rw [matchingRows_pushLeft query.on leftOnly left.rows right.rows]
          | left =>
              simp only [kindShape]
              rw [leftOuterRows_pushLeft query.on query.rightWidth leftOnly
                left.rows right.rows]
        next => rfl

theorem Query.eval_width (query : Query) (left right : List Core.Row) :
    ∀ values ∈ query.eval left right, values.length = query.columns.length := by
  intro values membership
  simp only [Query.eval, List.mem_map] at membership
  obtain ⟨row, _, rfl⟩ := membership
  exact projectRow_length query.columns row

end CoreJoin
end SQLeanite
