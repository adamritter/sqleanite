import SQLeanite.QuerySemantics
import SQLeanite.KRelation
import SQLeanite.CoreEngine

namespace SQLeanite
namespace RelationalAlgebra

/-!
# Typed multiplicity-valued relational algebra

This is the general algebra layer beneath optimizer rewrites.  Every expression
denotes a `KRelation.Relation`, so duplicate behavior is explicit in `Nat`
rather than inherited accidentally from a list implementation.  Products,
selection, projection, set operations, renaming/permutation, grouping and left
outer join are constructors; an inner join is derived as selection over a
product.
-/

abbrev Relation := KRelation.Relation

/-- A finite enumeration used by projection and grouping.  `Nodup` prevents a
source value from being counted twice merely because its representative was
listed twice in the proof domain. -/
structure Domain (Row : Type) where
  values : List Row
  nodup : values.Nodup

def supportDomain [DecidableEq Row] (rows : List Row) : Domain Row :=
  ⟨Core.deduplicate rows, Core.deduplicate_nodup rows⟩

/-- Multiplicity of a value in an executable list. -/
def listMultiplicity [DecidableEq Row] (target : Row) : List Row → Nat
  | [] => 0
  | row :: rows =>
      (if row = target then 1 else 0) + listMultiplicity target rows

def ofList [DecidableEq Row] (rows : List Row) : Relation Row :=
  fun target => listMultiplicity target rows

theorem listMultiplicity_eq_count [DecidableEq Row]
    (target : Row) (rows : List Row) :
    listMultiplicity target rows = rows.count target := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      by_cases equal : row = target <;>
        simp [listMultiplicity, List.count_cons, equal, induction,
          Nat.add_comm]

private theorem multiplicity_zero_absent [DecidableEq Row]
    (target : Row) (rows : List Row) (absent : target ∉ rows) :
    listMultiplicity target rows = 0 := by
  rw [listMultiplicity_eq_count]
  exact List.count_eq_zero.mpr absent

private theorem multiplicity_nonzero_member [DecidableEq Row]
    (target : Row) (rows : List Row) (member : target ∈ rows) :
    listMultiplicity target rows ≠ 0 := by
  intro zero
  have countZero : rows.count target = 0 := by
    simpa [listMultiplicity_eq_count] using zero
  exact (List.count_eq_zero.mp countZero) member

private theorem listMultiplicity_erase_self [DecidableEq Row]
    (target : Row) (rows : List Row) :
    listMultiplicity target (rows.erase target) =
      listMultiplicity target rows - 1 := by
  simp [listMultiplicity_eq_count]

private theorem listMultiplicity_erase_of_ne [DecidableEq Row]
    (target erased : Row) (rows : List Row) (unequal : target ≠ erased) :
    listMultiplicity target (rows.erase erased) =
      listMultiplicity target rows := by
  simp [listMultiplicity_eq_count, unequal]

abbrev bagIntersect [DecidableEq Row] := @QuerySemantics.bagIntersect Row _
abbrev bagExcept [DecidableEq Row] := @QuerySemantics.bagExcept Row _

theorem listMultiplicity_bagIntersect [DecidableEq Row]
    (target : Row) (left right : List Row) :
    listMultiplicity target (bagIntersect left right) =
      min (listMultiplicity target left) (listMultiplicity target right) := by
  induction left generalizing right with
  | nil => simp [bagIntersect, QuerySemantics.bagIntersect, listMultiplicity]
  | cons row rows induction =>
      unfold bagIntersect QuerySemantics.bagIntersect
      by_cases present : row ∈ right
      · rw [if_pos present]
        simp only [listMultiplicity]
        rw [induction]
        by_cases equal : row = target
        · subst row
          rw [listMultiplicity_erase_self]
          have nonzero : listMultiplicity target right ≠ 0 :=
            multiplicity_nonzero_member target right present
          simp only [if_pos rfl]
          change 1 + min (listMultiplicity target rows)
              (listMultiplicity target right - 1) =
            min (1 + listMultiplicity target rows)
              (listMultiplicity target right)
          omega
        · have reverse : target ≠ row := Ne.symm equal
          rw [listMultiplicity_erase_of_ne target row right reverse]
          simp [listMultiplicity, equal]
      · rw [if_neg present]
        rw [induction]
        by_cases equal : row = target
        · subst row
          rw [multiplicity_zero_absent target right present]
          simp [listMultiplicity]
        · simp [listMultiplicity, equal]

theorem listMultiplicity_bagExcept [DecidableEq Row]
    (target : Row) (left right : List Row) :
    listMultiplicity target (bagExcept left right) =
      listMultiplicity target left - listMultiplicity target right := by
  induction left generalizing right with
  | nil => simp [bagExcept, QuerySemantics.bagExcept, listMultiplicity]
  | cons row rows induction =>
      unfold bagExcept QuerySemantics.bagExcept
      by_cases present : row ∈ right
      · rw [if_pos present]
        rw [induction]
        by_cases equal : row = target
        · subst row
          rw [listMultiplicity_erase_self]
          have nonzero : listMultiplicity target right ≠ 0 :=
            multiplicity_nonzero_member target right present
          simp only [listMultiplicity, if_pos rfl]
          change listMultiplicity target rows -
              (listMultiplicity target right - 1) =
            (1 + listMultiplicity target rows) -
              listMultiplicity target right
          omega
        · have reverse : target ≠ row := Ne.symm equal
          rw [listMultiplicity_erase_of_ne target row right reverse]
          simp [listMultiplicity, equal]
      · rw [if_neg present]
        simp only [listMultiplicity]
        rw [induction]
        by_cases equal : row = target
        · subst row
          rw [multiplicity_zero_absent target right present]
          simp [listMultiplicity]
        · simp [listMultiplicity, equal]

theorem ofList_bagIntersect [DecidableEq Row] (left right : List Row) :
    ofList (bagIntersect left right) =
      KRelation.intersect (ofList left) (ofList right) := by
  apply KRelation.Relation.ext
  exact fun target => listMultiplicity_bagIntersect target left right

theorem ofList_bagExcept [DecidableEq Row] (left right : List Row) :
    ofList (bagExcept left right) =
      KRelation.except (ofList left) (ofList right) := by
  apply KRelation.Relation.ext
  exact fun target => listMultiplicity_bagExcept target left right

theorem listMultiplicity_eq_zero_of_not_mem [DecidableEq Row]
    (target : Row) (rows : List Row) (absent : target ∉ rows) :
    listMultiplicity target rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.mem_cons, not_or] at absent
      have reverse : row ≠ target := Ne.symm absent.1
      simp [listMultiplicity, reverse, induction absent.2]

theorem listMultiplicity_eq_zero_iff [DecidableEq Row]
    (target : Row) (rows : List Row) :
    listMultiplicity target rows = 0 ↔ target ∉ rows := by
  constructor
  · intro zero member
    induction rows with
    | nil => contradiction
    | cons row rows induction =>
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · subst row
          simp [listMultiplicity] at zero
        · by_cases equal : row = target
          · simp [listMultiplicity, equal] at zero
          · exact induction (by simpa [listMultiplicity, equal] using zero) member
  · exact listMultiplicity_eq_zero_of_not_mem target rows

private theorem listMultiplicity_eq_one_of_nodup_mem [DecidableEq Row]
    (target : Row) (rows : List Row) (nodup : rows.Nodup)
    (member : target ∈ rows) : listMultiplicity target rows = 1 := by
  induction rows with
  | nil => contradiction
  | cons row rows induction =>
      simp only [List.nodup_cons] at nodup
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst row
        rw [show listMultiplicity target (target :: rows) =
          1 + listMultiplicity target rows by simp [listMultiplicity]]
        rw [listMultiplicity_eq_zero_of_not_mem target rows nodup.1]
      · have unequal : row ≠ target := by
          intro equal
          subst row
          exact nodup.1 member
        simpa [listMultiplicity, unequal] using induction nodup.2 member

theorem ofList_deduplicate [DecidableEq Row] (rows : List Row) :
    ofList (Core.deduplicate rows) = KRelation.distinct (ofList rows) := by
  apply KRelation.Relation.ext
  intro target
  by_cases member : target ∈ rows
  · have deduplicatedMember : target ∈ Core.deduplicate rows :=
      (Core.mem_deduplicate target rows).2 member
    have deduplicatedCount := listMultiplicity_eq_one_of_nodup_mem target
      (Core.deduplicate rows) (Core.deduplicate_nodup rows)
      deduplicatedMember
    have originalNonzero : listMultiplicity target rows ≠ 0 :=
      fun zero => (listMultiplicity_eq_zero_iff target rows).1 zero member
    simp [ofList, KRelation.distinct, deduplicatedCount, originalNonzero]
  · have deduplicatedAbsent : target ∉ Core.deduplicate rows := by
      simpa [Core.mem_deduplicate] using member
    simp [ofList, KRelation.distinct,
      listMultiplicity_eq_zero_of_not_mem target rows member,
      listMultiplicity_eq_zero_of_not_mem target (Core.deduplicate rows)
        deduplicatedAbsent]

theorem listMultiplicity_append [DecidableEq Row]
    (target : Row) (left right : List Row) :
    listMultiplicity target (left ++ right) =
      listMultiplicity target left + listMultiplicity target right := by
  induction left with
  | nil => simp [listMultiplicity]
  | cons row rows induction =>
      simp [listMultiplicity, induction, Nat.add_assoc]

theorem ofList_append [DecidableEq Row] (left right : List Row) :
    ofList (left ++ right) = KRelation.unionAll (ofList left) (ofList right) := by
  apply KRelation.Relation.ext
  intro row
  exact listMultiplicity_append row left right

theorem listMultiplicity_filter [DecidableEq Row] (predicate : Row → Bool)
    (target : Row) (rows : List Row) :
    listMultiplicity target (rows.filter predicate) =
      if predicate target then listMultiplicity target rows else 0 := by
  induction rows with
  | nil => simp [listMultiplicity]
  | cons row rows induction =>
      by_cases equal : row = target
      · subst row
        cases keep : predicate target <;>
          simp [List.filter_cons, keep, listMultiplicity, induction]
      · cases keep : predicate row <;>
          simp [List.filter_cons, keep, listMultiplicity, equal, induction]

theorem ofList_filter [DecidableEq Row] (predicate : Row → Bool)
    (rows : List Row) :
    ofList (rows.filter predicate) = fun target =>
      if predicate target then ofList rows target else 0 := by
  apply KRelation.Relation.ext
  intro target
  exact listMultiplicity_filter predicate target rows

private theorem projectSum_cons_nodup [DecidableEq Input] [DecidableEq Output]
    (projection : Input → Output) (output : Output) (row : Input)
    (rows domain : List Input) (nodup : domain.Nodup) :
    KRelation.projectSum projection (ofList (row :: rows)) output domain =
      (if row ∈ domain ∧ projection row = output then 1 else 0) +
        KRelation.projectSum projection (ofList rows) output domain := by
  induction domain with
  | nil => simp [KRelation.projectSum]
  | cons candidate domain induction =>
      simp only [List.nodup_cons] at nodup
      have tail := induction nodup.2
      by_cases equal : candidate = row
      · subst candidate
        by_cases selected : projection row = output <;>
          simp [KRelation.projectSum, ofList, listMultiplicity, nodup.1,
            tail, selected, Nat.add_assoc]
      · have reverse : row ≠ candidate := Ne.symm equal
        by_cases member : row ∈ domain <;>
          by_cases selected : projection row = output <;>
          simp [KRelation.projectSum, ofList, listMultiplicity, equal, reverse,
            tail, member, selected, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm]

private theorem projectSum_support [DecidableEq Input] [DecidableEq Output]
    (projection : Input → Output) (output : Output) (rows : List Input) :
    KRelation.projectSum projection (ofList rows) output
        (Core.deduplicate rows) =
      listMultiplicity output (rows.map projection) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      unfold Core.deduplicate
      by_cases present : row ∈ rows
      · simp only [present, ↓reduceIte]
        rw [projectSum_cons_nodup projection output row rows
          (Core.deduplicate rows) (Core.deduplicate_nodup rows)]
        rw [induction]
        simp [Core.mem_deduplicate, present, listMultiplicity]
      · simp only [present, ↓reduceIte, KRelation.projectSum]
        rw [projectSum_cons_nodup projection output row rows
          (Core.deduplicate rows) (Core.deduplicate_nodup rows)]
        rw [induction]
        by_cases selected : projection row = output <;>
          simp [Core.mem_deduplicate, present, listMultiplicity, ofList,
            selected, listMultiplicity_eq_zero_of_not_mem row rows present]

/-- Finite-support pushforward: summing each distinct source value's
multiplicity is exactly the multiplicity of the executable mapped list.  The
support is deduplicated so a source value contributes once, while its bag
multiplicity remains in `ofList`. -/
theorem project_ofList [DecidableEq Input] [DecidableEq Output]
    (projection : Input → Output) (rows : List Input) :
    KRelation.project (supportDomain rows).values projection (ofList rows) =
      ofList (rows.map projection) := by
  apply KRelation.Relation.ext
  intro output
  exact projectSum_support projection output rows

theorem ofList_groupCountRows (key : QuerySemantics.Row → QuerySemantics.Row)
    (rows : List QuerySemantics.Row) :
    ofList (QuerySemantics.groupCountRows key rows) =
      KRelation.groupCount (supportDomain rows).values key (ofList rows) := by
  simpa [QuerySemantics.groupCountRows, KRelation.groupCount] using
    (project_ofList key rows).symm

private theorem groupSumRows_cons_nodup [DecidableEq Input]
    [DecidableEq Group] (key : Input → Group) (measure : Input → Nat)
    (output : Group) (row : Input) (rows domain : List Input)
    (nodup : domain.Nodup) :
    KRelation.groupSumRows key measure (ofList (row :: rows)) output domain =
      (if row ∈ domain ∧ key row = output then measure row else 0) +
        KRelation.groupSumRows key measure (ofList rows) output domain := by
  induction domain with
  | nil => simp [KRelation.groupSumRows]
  | cons candidate domain induction =>
      simp only [List.nodup_cons] at nodup
      have tail := induction nodup.2
      by_cases equal : candidate = row
      · subst candidate
        by_cases selected : key row = output <;>
          simp [KRelation.groupSumRows, ofList, listMultiplicity, nodup.1,
            tail, selected, Nat.add_mul, Nat.add_assoc]
      · have reverse : row ≠ candidate := Ne.symm equal
        by_cases member : row ∈ domain <;>
          by_cases selected : key row = output <;>
          simp [KRelation.groupSumRows, ofList, listMultiplicity, equal,
            reverse, tail, member, selected, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm]

private theorem groupSumRows_support [DecidableEq Input]
    [DecidableEq Group] (key : Input → Group) (measure : Input → Nat)
    (output : Group) (rows : List Input) :
    KRelation.groupSumRows key measure (ofList rows) output
        (Core.deduplicate rows) =
      listMultiplicity output
        (rows.flatMap fun row => List.replicate (measure row) (key row)) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      unfold Core.deduplicate
      by_cases present : row ∈ rows
      · simp only [present, ↓reduceIte]
        rw [groupSumRows_cons_nodup key measure output row rows
          (Core.deduplicate rows) (Core.deduplicate_nodup rows)]
        rw [induction]
        rw [show ((row :: rows).flatMap fun candidate =>
              List.replicate (measure candidate) (key candidate)) =
            List.replicate (measure row) (key row) ++
              (rows.flatMap fun candidate =>
                List.replicate (measure candidate) (key candidate)) by rfl]
        rw [listMultiplicity_append]
        by_cases selected : key row = output <;>
          simp [Core.mem_deduplicate, present, listMultiplicity_eq_count,
            List.count_replicate, beq_iff_eq, selected]
      · simp only [present, ↓reduceIte, KRelation.groupSumRows]
        have countZero : rows.count row = 0 := List.count_eq_zero.mpr present
        rw [groupSumRows_cons_nodup key measure output row rows
          (Core.deduplicate rows) (Core.deduplicate_nodup rows)]
        rw [induction]
        rw [show ((row :: rows).flatMap fun candidate =>
              List.replicate (measure candidate) (key candidate)) =
            List.replicate (measure row) (key row) ++
              (rows.flatMap fun candidate =>
                List.replicate (measure candidate) (key candidate)) by rfl]
        rw [listMultiplicity_append]
        by_cases selected : key row = output <;>
          simp [Core.mem_deduplicate, present, ofList, listMultiplicity,
            listMultiplicity_eq_count, List.count_replicate, beq_iff_eq,
            selected, countZero,
            listMultiplicity_eq_zero_of_not_mem row rows present]

theorem ofList_groupSumRows (key : QuerySemantics.Row → QuerySemantics.Row)
    (measure : QuerySemantics.Row → Nat)
    (rows : List QuerySemantics.Row) :
    ofList (QuerySemantics.groupSumRows key measure rows) =
      KRelation.groupSum (supportDomain rows).values key measure
        (ofList rows) := by
  apply KRelation.Relation.ext
  intro output
  exact (groupSumRows_support key measure output rows).symm

/-- Executable materialization of a true grouped COUNT result.  Unlike the
annotation-level `groupCountRows`, each group occurs exactly once and the
aggregate is data in the output pair. -/
def materializedCountRows [DecidableEq Group] (key : Input → Group)
    (rows : List Input) : List (Group × Nat) :=
  let keys := Core.deduplicate (rows.map key)
  keys.map fun group => (group, listMultiplicity group (rows.map key))

/-- Executable materialization of a true grouped natural SUM result. -/
def materializedSumRows [DecidableEq Group] (key : Input → Group)
    (measure : Input → Nat) (rows : List Input) : List (Group × Nat) :=
  let keys := Core.deduplicate (rows.map key)
  let weighted := rows.flatMap fun row =>
    List.replicate (measure row) (key row)
  keys.map fun group => (group, listMultiplicity group weighted)

private theorem listMultiplicity_groupValueMap [DecidableEq Group]
    (value : Group → Nat) (targetGroup : Group) (targetValue : Nat)
    (groups : List Group) (nodup : groups.Nodup) :
    listMultiplicity (targetGroup, targetValue)
        (groups.map fun group => (group, value group)) =
      if targetGroup ∈ groups ∧ targetValue = value targetGroup then 1 else 0 := by
  induction groups with
  | nil => simp [listMultiplicity]
  | cons group groups induction =>
      simp only [List.nodup_cons] at nodup
      by_cases groupEqual : group = targetGroup
      · subst group
        simp only [List.map_cons, listMultiplicity]
        rw [induction nodup.2]
        by_cases valueEqual : targetValue = value targetGroup
        · simp [nodup.1, valueEqual]
        · have reverse : value targetGroup ≠ targetValue :=
            Ne.symm valueEqual
          simp [nodup.1, valueEqual, reverse]
      · have pairUnequal : (group, value group) ≠
            (targetGroup, targetValue) := by
          intro equal
          exact groupEqual (Prod.mk.inj equal).1
        have reverseGroup : targetGroup ≠ group := Ne.symm groupEqual
        simp only [List.map_cons, listMultiplicity, if_neg pairUnequal]
        rw [induction nodup.2]
        simp [groupEqual, reverseGroup]

theorem ofList_whereRows (predicate : QuerySemantics.Predicate)
    (rows : List QuerySemantics.Row) :
    ofList (QuerySemantics.whereRows predicate rows) =
      KRelation.select predicate.eval (ofList rows) := by
  apply KRelation.Relation.ext
  intro target
  rw [show QuerySemantics.whereRows predicate rows =
    rows.filter (fun row => predicate.eval row == .true) by rfl]
  change listMultiplicity target
      (rows.filter (fun row => predicate.eval row == .true)) = _
  rw [listMultiplicity_filter]
  cases result : predicate.eval target <;>
    simp [KRelation.select, ofList, result]

private theorem listMultiplicity_values_map_joined
    (cells : List Core.Value) (left : QuerySemantics.Row)
    (right : List QuerySemantics.Row) :
    listMultiplicity (QuerySemantics.Row.values cells)
      (right.map fun row => QuerySemantics.Row.joined left row) = 0 := by
  induction right with
  | nil => rfl
  | cons row rows induction =>
      simp [listMultiplicity, induction]

private theorem listMultiplicity_joined_map_joined
    (leftTarget rightTarget left : QuerySemantics.Row)
    (right : List QuerySemantics.Row) :
    listMultiplicity (QuerySemantics.Row.joined leftTarget rightTarget)
      (right.map fun row => QuerySemantics.Row.joined left row) =
      if left = leftTarget then listMultiplicity rightTarget right else 0 := by
  induction right with
  | nil => simp [listMultiplicity]
  | cons row rows induction =>
      by_cases leftEqual : left = leftTarget
      · subst leftTarget
        simp [listMultiplicity, induction]
      · simp [listMultiplicity, induction, leftEqual]

theorem listMultiplicity_joinRows (left right : List QuerySemantics.Row)
    (target : QuerySemantics.Row) :
    listMultiplicity target (QuerySemantics.joinRows left right) =
      match target with
      | .values _ => 0
      | .joined leftTarget rightTarget =>
          listMultiplicity leftTarget left *
            listMultiplicity rightTarget right := by
  induction left with
  | nil => cases target <;> simp [QuerySemantics.joinRows, listMultiplicity]
  | cons row rows induction =>
      cases target with
      | values cells =>
          rw [show QuerySemantics.joinRows (row :: rows) right =
            (right.map fun candidate =>
              QuerySemantics.Row.joined row candidate) ++
              QuerySemantics.joinRows rows right by rfl]
          rw [listMultiplicity_append,
            listMultiplicity_values_map_joined]
          simpa using induction
      | joined leftTarget rightTarget =>
          rw [show QuerySemantics.joinRows (row :: rows) right =
            (right.map fun candidate =>
              QuerySemantics.Row.joined row candidate) ++
              QuerySemantics.joinRows rows right by rfl]
          rw [listMultiplicity_append,
            listMultiplicity_joined_map_joined]
          rw [induction]
          by_cases equal : row = leftTarget
          · simp [listMultiplicity, equal, Nat.add_mul]
          · simp [listMultiplicity, equal]

def joinedProduct (left right : Relation QuerySemantics.Row) :
    Relation QuerySemantics.Row
  | .values _ => 0
  | .joined leftRow rightRow => left leftRow * right rightRow

/-- One output tuple per nonempty group, with COUNT stored as data rather than
misread as output multiplicity. -/
def materializedCountRelation [DecidableEq Group] (domain : Domain Input)
    (key : Input → Group) (relation : Relation Input) :
    Relation (Group × Nat) :=
  fun output =>
    let count := KRelation.groupCount domain.values key relation output.1
    if count = 0 then 0 else if output.2 = count then 1 else 0

/-- One output tuple per nonempty group, with natural SUM stored as data.  The
COUNT test retains groups whose measures sum to zero. -/
def materializedSumRelation [DecidableEq Group] (domain : Domain Input)
    (key : Input → Group) (measure : Input → Nat)
    (relation : Relation Input) : Relation (Group × Nat) :=
  fun output =>
    let count := KRelation.groupCount domain.values key relation output.1
    let sum := KRelation.groupSum domain.values key measure relation output.1
    if count = 0 then 0 else if output.2 = sum then 1 else 0

/-- Bridge from the existing Core-backed list denotation to the general bag
algebra: nested-loop join is exactly multiplicity product embedded in the
existing joined-row type, including duplicates. -/
theorem ofList_joinRows (left right : List QuerySemantics.Row) :
    ofList (QuerySemantics.joinRows left right) =
      joinedProduct (ofList left) (ofList right) := by
  apply KRelation.Relation.ext
  intro target
  cases target with
  | values cells =>
      simp [ofList, listMultiplicity_joinRows, joinedProduct]
  | joined leftTarget rightTarget =>
      simp [ofList, listMultiplicity_joinRows, joinedProduct]

/-- Typed algebra syntax.  `rename` is the pullback along an inverse mapping;
it covers column permutations and the product reassociations used by join
rewrites without requiring a finite summation. -/
inductive Expr : Type → Type 1 where
  | relation {Row : Type} (value : Relation Row) : Expr Row
  | unionAll {Row : Type} (left right : Expr Row) : Expr Row
  | intersect {Row : Type} (left right : Expr Row) : Expr Row
  | except {Row : Type} (left right : Expr Row) : Expr Row
  | distinct {Row : Type} (input : Expr Row) : Expr Row
  | select {Row : Type} (predicate : Row → Truth) (input : Expr Row) : Expr Row
  | product {Left Right : Type} (left : Expr Left) (right : Expr Right) :
      Expr (Left × Right)
  | project {Input Output : Type} (decEq : DecidableEq Output)
      (domain : Domain Input) (projection : Input → Output)
      (input : Expr Input) : Expr Output
  | rename {Input Output : Type} (backward : Output → Input)
      (input : Expr Input) : Expr Output
  | embed {Input Output : Type} (backward : Output → Option Input)
      (input : Expr Input) : Expr Output
  | groupCount {Input Group : Type} (decEq : DecidableEq Group)
      (domain : Domain Input) (key : Input → Group) (input : Expr Input) :
      Expr Group
  | groupSum {Input Group : Type} (decEq : DecidableEq Group)
      (domain : Domain Input) (key : Input → Group) (measure : Input → Nat)
      (input : Expr Input) : Expr Group
  | materializeCount {Input Group : Type} (decEq : DecidableEq Group)
      (domain : Domain Input) (key : Input → Group) (input : Expr Input) :
      Expr (Group × Nat)
  | materializeSum {Input Group : Type} (decEq : DecidableEq Group)
      (domain : Domain Input) (key : Input → Group) (measure : Input → Nat)
      (input : Expr Input) : Expr (Group × Nat)
  | leftOuter {Left Right : Type} (decEq : DecidableEq Right)
      (rightDomain : Domain Right) (nullRight : Right)
      (predicate : Left → Right → Truth)
      (left : Expr Left) (right : Expr Right) : Expr (Left × Right)

def hasMatch (domain : Domain Right) (predicate : Left → Right → Truth)
    (right : Relation Right) (left : Left) : Bool :=
  domain.values.any fun candidate =>
    predicate left candidate == .true && right candidate != 0

def leftOuterRelation [DecidableEq Right] (domain : Domain Right)
    (nullRight : Right) (predicate : Left → Right → Truth)
    (left : Relation Left) (right : Relation Right) : Relation (Left × Right) :=
  fun row =>
    if hasMatch domain predicate right row.1 then
      if predicate row.1 row.2 = .true then left row.1 * right row.2 else 0
    else if row.2 = nullRight then left row.1 else 0

def eval : {Row : Type} → Expr Row → Relation Row
  | _, .relation value => value
  | _, .unionAll left right => KRelation.unionAll (eval left) (eval right)
  | _, .intersect left right => KRelation.intersect (eval left) (eval right)
  | _, .except left right => KRelation.except (eval left) (eval right)
  | _, .distinct input => KRelation.distinct (eval input)
  | _, .select predicate input => KRelation.select predicate (eval input)
  | _, .product left right => KRelation.join (eval left) (eval right)
  | _, .project decEq domain projection input =>
      @KRelation.project _ _ decEq domain.values projection (eval input)
  | _, .rename backward input => fun output => eval input (backward output)
  | _, .embed backward input => fun output =>
      match backward output with
      | none => 0
      | some source => eval input source
  | _, .groupCount decEq domain key input =>
      @KRelation.groupCount _ _ decEq domain.values key (eval input)
  | _, .groupSum decEq domain key measure input =>
      @KRelation.groupSum _ _ decEq domain.values key measure (eval input)
  | _, .materializeCount decEq domain key input =>
      @materializedCountRelation _ _ decEq domain key (eval input)
  | _, .materializeSum decEq domain key measure input =>
      @materializedSumRelation _ _ decEq domain key measure (eval input)
  | _, .leftOuter decEq domain nullRight predicate left right =>
      @leftOuterRelation _ _ decEq domain nullRight predicate
        (eval left) (eval right)

/-- Materialized COUNT produces one result tuple per nonempty group and stores
the count in that tuple.  This is the SQL-result-level theorem, distinct from
the annotation-level `groupCount` law. -/
theorem materializeCount_eval [DecidableEq Input] [DecidableEq Group]
    (key : Input → Group) (rows : List Input) (input : Expr Input)
    (inputExact : eval input = ofList rows) :
    eval (.materializeCount inferInstance (supportDomain rows) key input) =
      ofList (materializedCountRows key rows) := by
  apply KRelation.Relation.ext
  intro output
  rcases output with ⟨targetGroup, targetValue⟩
  have countExact :
      KRelation.groupCount (supportDomain rows).values key (ofList rows)
          targetGroup =
        listMultiplicity targetGroup (rows.map key) := by
    simpa [KRelation.groupCount, ofList] using
      congrFun (project_ofList key rows) targetGroup
  rw [show eval (.materializeCount inferInstance (supportDomain rows) key input)
        (targetGroup, targetValue) =
      materializedCountRelation (supportDomain rows) key (eval input)
        (targetGroup, targetValue) by rfl]
  rw [inputExact]
  simp only [materializedCountRows, ofList]
  rw [listMultiplicity_groupValueMap
    (fun group => listMultiplicity group (rows.map key))
    targetGroup targetValue (Core.deduplicate (rows.map key))
    (Core.deduplicate_nodup (rows.map key))]
  rw [show materializedCountRelation (supportDomain rows) key (ofList rows)
        (targetGroup, targetValue) =
      if listMultiplicity targetGroup (rows.map key) = 0 then 0
      else if targetValue = listMultiplicity targetGroup (rows.map key)
        then 1 else 0 by
      simp [materializedCountRelation, countExact]]
  by_cases zero : listMultiplicity targetGroup (rows.map key) = 0
  · have absent : targetGroup ∉ rows.map key :=
      (listMultiplicity_eq_zero_iff targetGroup (rows.map key)).1 zero
    simp [zero, Core.mem_deduplicate, absent]
  · by_cases member : targetGroup ∈ rows.map key
    · have deduplicatedMember : targetGroup ∈
          Core.deduplicate (rows.map key) :=
        (Core.mem_deduplicate targetGroup (rows.map key)).2 member
      simp [zero, deduplicatedMember]
    · exact (zero (listMultiplicity_eq_zero_of_not_mem targetGroup
        (rows.map key) member)).elim

/-- Materialized natural SUM likewise emits one row per nonempty group.  A
group whose measures sum to zero is retained with value zero. -/
theorem materializeSum_eval [DecidableEq Input] [DecidableEq Group]
    (key : Input → Group) (measure : Input → Nat) (rows : List Input)
    (input : Expr Input) (inputExact : eval input = ofList rows) :
    eval (.materializeSum inferInstance (supportDomain rows)
        key measure input) =
      ofList (materializedSumRows key measure rows) := by
  apply KRelation.Relation.ext
  intro output
  rcases output with ⟨targetGroup, targetValue⟩
  let weighted := rows.flatMap fun row =>
    List.replicate (measure row) (key row)
  have countExact :
      KRelation.groupCount (supportDomain rows).values key (ofList rows)
          targetGroup =
        listMultiplicity targetGroup (rows.map key) := by
    simpa [KRelation.groupCount, ofList] using
      congrFun (project_ofList key rows) targetGroup
  have sumExact :
      KRelation.groupSum (supportDomain rows).values key measure (ofList rows)
          targetGroup =
        listMultiplicity targetGroup weighted := by
    exact groupSumRows_support key measure targetGroup rows
  rw [show eval (.materializeSum inferInstance (supportDomain rows)
          key measure input) (targetGroup, targetValue) =
      materializedSumRelation (supportDomain rows) key measure (eval input)
        (targetGroup, targetValue) by rfl]
  rw [inputExact]
  simp only [materializedSumRows, ofList]
  rw [listMultiplicity_groupValueMap
    (fun group => listMultiplicity group weighted)
    targetGroup targetValue (Core.deduplicate (rows.map key))
    (Core.deduplicate_nodup (rows.map key))]
  rw [show materializedSumRelation (supportDomain rows) key measure
        (ofList rows) (targetGroup, targetValue) =
      if listMultiplicity targetGroup (rows.map key) = 0 then 0
      else if targetValue = listMultiplicity targetGroup weighted
        then 1 else 0 by
      simp [materializedSumRelation, countExact, sumExact]]
  by_cases zero : listMultiplicity targetGroup (rows.map key) = 0
  · have absent : targetGroup ∉ rows.map key :=
      (listMultiplicity_eq_zero_iff targetGroup (rows.map key)).1 zero
    simp [zero, Core.mem_deduplicate, absent]
  · by_cases member : targetGroup ∈ rows.map key
    · have deduplicatedMember : targetGroup ∈
          Core.deduplicate (rows.map key) :=
        (Core.mem_deduplicate targetGroup (rows.map key)).2 member
      simp [zero, deduplicatedMember]
    · exact (zero (listMultiplicity_eq_zero_of_not_mem targetGroup
        (rows.map key) member)).elim

/-- The live Core grouped-count accumulator is exactly the multiplicity used
by `materializedCountRows`, after WHERE filtering. -/
theorem coreGroup_keyCount_eq_multiplicity (query : Core.GroupQuery)
    (rows : List Core.Row) (group : List Core.Value) :
    query.keyCount rows group =
      listMultiplicity group
        ((query.selectedRows rows).map query.rowKey) := by
  rw [listMultiplicity_eq_count]
  simp only [Core.GroupQuery.keyCount, List.count, List.countP_map,
    Function.comp_apply]
  apply List.countP_congr
  intro row _member
  simp only [Function.comp_def, beq_iff_eq]

/-- Therefore the executable materialized COUNT rows use the same groups and
counts as the live Core group evaluator, before its checked INTEGER encoding. -/
theorem materializedCountRows_eq_coreGroup (query : Core.GroupQuery)
    (rows : List Core.Row) :
    materializedCountRows query.rowKey (query.selectedRows rows) =
      (query.groupKeys rows).map fun group =>
        (group, query.keyCount rows group) := by
  unfold materializedCountRows Core.GroupQuery.groupKeys
  apply List.map_congr_left
  intro group _member
  simp [coreGroup_keyCount_eq_multiplicity]

theorem coreGroup_keyRows_length_eq_keyCount (query : Core.GroupQuery)
    (rows : List Core.Row) (group : List Core.Value) :
    (query.keyRows rows group).length = query.keyCount rows group := by
  unfold Core.GroupQuery.keyRows Core.GroupQuery.keyCount
  exact List.countP_eq_length_filter.symm

/-- Successful live COUNT(*) materialization refines the unbounded natural
aggregate.  The success premise is the explicit signed-64-bit overflow guard;
no wrapping assumption is hidden in the bridge. -/
theorem coreGroup_countStar_refines_materialized (query : Core.GroupQuery)
    (rows : List Core.Row) (group : List Core.Value)
    (integer : Core.Integer)
    (success : Core.countInteger (query.keyRows rows group).length =
      .ok integer) :
    integer.value = Int.ofNat
      (listMultiplicity group
        ((query.selectedRows rows).map query.rowKey)) := by
  rw [Core.countInteger_exact success]
  rw [coreGroup_keyRows_length_eq_keyCount]
  rw [coreGroup_keyCount_eq_multiplicity]

/-- A successful live grouped SUM output contains the mathematical integer
sum of the extracted non-NULL inputs.  `columnIntegers` rejects other storage
classes and `sumIntegers`/`checkedInteger` reject intermediate overflow, so the
premises expose both failure boundaries. -/
theorem coreGroup_sumColumn_refines_integerSum (query : Core.GroupQuery)
    (rows : List Core.Row) (group : List Core.Value) (column : Nat)
    (integers : List Core.Integer) (total : Core.Integer)
    (extracted : Core.columnIntegers column (query.keyRows rows group) =
      .ok integers)
    (success : query.outputValue rows group (.sumColumn column) =
      .ok (.integer total)) :
    total.value = (integers.map (·.value)).sum := by
  simp only [Core.GroupQuery.outputValue, Core.sumColumn] at success
  rw [extracted] at success
  simp only [Except.instMonad, Except.bind, Except.pure] at success
  cases summed : Core.sumIntegers integers with
  | error message =>
      simp [summed] at success
  | ok result =>
      cases result with
      | none =>
          simp [summed] at success
      | some integer =>
          simp [summed] at success
          subst total
          exact Core.sumIntegers_exact summed

theorem core_sumIntegers_none_iff (integers : List Core.Integer) :
    Core.sumIntegers integers = .ok none ↔ integers = [] := by
  cases integers with
  | nil => simp [Core.sumIntegers]
  | cons integer integers =>
      simp only [Core.sumIntegers]
      cases Core.sumIntegerFrom integer integers <;> simp

/-- SQL NULL for grouped SUM is likewise exact: it occurs precisely when the
group has no non-NULL integer inputs. -/
theorem coreGroup_sumColumn_null_iff (query : Core.GroupQuery)
    (rows : List Core.Row) (group : List Core.Value) (column : Nat)
    (integers : List Core.Integer)
    (extracted : Core.columnIntegers column (query.keyRows rows group) =
      .ok integers) :
    query.outputValue rows group (.sumColumn column) = .ok .null ↔
      integers = [] := by
  simp only [Core.GroupQuery.outputValue, Core.sumColumn]
  rw [extracted]
  simp only [Except.instMonad, Except.bind, Except.pure]
  cases summed : Core.sumIntegers integers with
  | error message =>
      have notEmpty : integers ≠ [] := by
        intro empty
        subst integers
        simp [Core.sumIntegers] at summed
      simp [summed, notEmpty]
  | ok result =>
      cases result with
      | none =>
          have empty := (core_sumIntegers_none_iff integers).1 summed
          simp [summed, empty]
      | some integer =>
          have notEmpty : integers ≠ [] := by
            intro empty
            subst integers
            simp [Core.sumIntegers] at summed
          simp [summed, notEmpty]

/-- Per-column semantic contract for a live grouped output tuple. -/
def coreGroupOutputRefines (query : Core.GroupQuery) (rows : List Core.Row)
    (group : List Core.Value) : Core.GroupOutput → Core.Value → Prop
  | .key position, value => value = group[position]?.getD .null
  | .countStar, .integer integer =>
      integer.value = Int.ofNat (query.keyCount rows group)
  | .countStar, _ => False
  | .countColumn column, .integer integer =>
      integer.value = Int.ofNat ((query.keyRows rows group).countP
        fun row => row.value column != .null)
  | .countColumn _, _ => False
  | .sumColumn column, value =>
      ∃ integers,
        Core.columnIntegers column (query.keyRows rows group) = .ok integers ∧
        match value with
        | .null => integers = []
        | .integer integer =>
            integer.value = (integers.map (·.value)).sum
        | .realBits _ | .text _ | .blob _ => False
  | .minColumn column, value =>
      value = Core.extremeColumn true column (query.keyRows rows group)
  | .maxColumn column, value =>
      value = Core.extremeColumn false column (query.keyRows rows group)

theorem coreGroup_outputValue_refines (query : Core.GroupQuery)
    (rows : List Core.Row) (group : List Core.Value)
    (output : Core.GroupOutput) (value : Core.Value)
    (success : query.outputValue rows group output = .ok value) :
    coreGroupOutputRefines query rows group output value := by
  cases output with
  | key position =>
      simp [Core.GroupQuery.outputValue] at success
      subst value
      rfl
  | countStar =>
      simp only [Core.GroupQuery.outputValue] at success
      cases counted : Core.countInteger (query.keyRows rows group).length with
      | error message =>
          simp [counted, Except.instMonad, Except.map] at success
      | ok integer =>
          simp [counted, Except.instMonad, Except.map] at success
          subst value
          simp [coreGroupOutputRefines, Core.countInteger_exact counted,
            coreGroup_keyRows_length_eq_keyCount]
  | countColumn column =>
      simp only [Core.GroupQuery.outputValue] at success
      cases counted : Core.countInteger ((query.keyRows rows group).countP
          fun row => row.value column != .null) with
      | error message =>
          simp [counted, Except.instMonad, Except.map] at success
      | ok integer =>
          simp [counted, Except.instMonad, Except.map] at success
          subst value
          simp [coreGroupOutputRefines, Core.countInteger_exact counted]
  | sumColumn column =>
      simp only [Core.GroupQuery.outputValue] at success
      cases extracted : Core.columnIntegers column
          (query.keyRows rows group) with
      | error message =>
          simp [Core.sumColumn, extracted, Except.instMonad, Except.bind,
            Except.pure] at success
      | ok integers =>
          cases summed : Core.sumIntegers integers with
          | error message =>
              simp [Core.sumColumn, extracted, summed, Except.instMonad,
                Except.bind, Except.pure] at success
          | ok result =>
              cases result with
              | none =>
                  simp [Core.sumColumn, extracted, summed, Except.instMonad,
                    Except.bind, Except.pure] at success
                  subst value
                  refine ⟨integers, extracted, ?_⟩
                  exact (core_sumIntegers_none_iff integers).1 summed
              | some integer =>
                  simp [Core.sumColumn, extracted, summed, Except.instMonad,
                    Except.bind, Except.pure] at success
                  subst value
                  exact ⟨integers, extracted, Core.sumIntegers_exact summed⟩
  | minColumn column =>
      simp [Core.GroupQuery.outputValue] at success
      subst value
      rfl
  | maxColumn column =>
      simp [Core.GroupQuery.outputValue] at success
      subst value
      rfl

inductive Aligned (relation : Left → Right → Prop) :
    List Left → List Right → Prop where
  | nil : Aligned relation [] []
  | cons {left right lefts rights} : relation left right →
      Aligned relation lefts rights →
      Aligned relation (left :: lefts) (right :: rights)

/-- Arbitrary multi-output grouped tuples compose the per-output contracts in
the same order. -/
theorem coreGroup_evalOutputs_refines (query : Core.GroupQuery)
    (rows : List Core.Row) (group : List Core.Value)
    (outputs : List Core.GroupOutput) (result : List Core.Value)
    (success : query.evalOutputs rows group outputs = .ok result) :
    Aligned (coreGroupOutputRefines query rows group) outputs result := by
  induction outputs generalizing result with
  | nil =>
      simp [Core.GroupQuery.evalOutputs] at success
      subst result
      exact .nil
  | cons output outputs induction =>
      simp only [Core.GroupQuery.evalOutputs] at success
      cases head : query.outputValue rows group output with
      | error message => simp [head] at success
      | ok value =>
          simp only [head] at success
          cases tail : query.evalOutputs rows group outputs with
          | error message => simp [tail] at success
          | ok values =>
              simp [tail] at success
              subst result
              exact .cons (coreGroup_outputValue_refines query rows group
                output value head) (induction values tail)

theorem coreGroup_evalKeys_refines (query : Core.GroupQuery)
    (rows : List Core.Row) (groups : List (List Core.Value))
    (results : List (List Core.Value))
    (success : query.evalKeys rows groups = .ok results) :
    Aligned (fun group result =>
      Aligned (coreGroupOutputRefines query rows group)
        query.outputs result) groups results := by
  induction groups generalizing results with
  | nil =>
      simp [Core.GroupQuery.evalKeys] at success
      subst results
      exact .nil
  | cons group groups induction =>
      simp only [Core.GroupQuery.evalKeys] at success
      cases head : query.evalOutputs rows group query.outputs with
      | error message => simp [head] at success
      | ok result =>
          simp only [head] at success
          cases tail : query.evalKeys rows groups with
          | error message => simp [tail] at success
          | ok resultsTail =>
              simp [tail] at success
              subst results
              exact .cons
                (coreGroup_evalOutputs_refines query rows group query.outputs
                  result head)
                (induction resultsTail tail)

/-- End-to-end semantic certificate for every row and column returned by the
live grouped evaluator. -/
theorem coreGroup_eval_refines (query : Core.GroupQuery)
    (rows : List Core.Row) (results : List (List Core.Value))
    (success : query.eval rows = .ok results) :
    Aligned (fun group result =>
      Aligned (coreGroupOutputRefines query rows group)
        query.outputs result) (query.groupKeys rows) results := by
  exact coreGroup_evalKeys_refines query rows (query.groupKeys rows)
    results success

/-- The algebra base relation for a live verified Core table. -/
def coreTable (database : Core.Database) (name : String) :
    Expr QuerySemantics.Row :=
  .relation (ofList (QuerySemantics.tableRows database name))

/-- INNER JOIN is not primitive: it is SQL-TRUE selection over a product. -/
def innerJoin (predicate : Left → Right → Truth)
    (left : Expr Left) (right : Expr Right) : Expr (Left × Right) :=
  .select (fun row => predicate row.1 row.2) (.product left right)

theorem eval_innerJoin (predicate : Left → Right → Truth)
    (left : Expr Left) (right : Expr Right) :
    eval (innerJoin predicate left right) =
      KRelation.select (fun row => predicate row.1 row.2)
        (KRelation.join (eval left) (eval right)) := rfl

def joinedRows (left right : Expr QuerySemantics.Row) :
    Expr QuerySemantics.Row :=
  .embed (fun
    | .values _ => none
    | .joined leftRow rightRow => some (leftRow, rightRow))
    (.product left right)

theorem joinedRows_eval (left right : Expr QuerySemantics.Row) :
    eval (joinedRows left right) = joinedProduct (eval left) (eval right) := by
  apply KRelation.Relation.ext
  intro row
  cases row <;> rfl

def joinedLeftOuterRows (rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row) : Expr QuerySemantics.Row :=
  .embed (fun
    | .values _ => none
    | .joined leftRow rightRow => some (leftRow, rightRow))
    (.leftOuter inferInstance (supportDomain rightRows) (.values [])
      (fun _ _ => .true) left right)

/-- Predicate-bearing left outer join embedded back into the executable row
shape.  The predicate is evaluated on the joined row, so SQL `unknown` is a
non-match exactly as it is for `ON` in the executable semantics. -/
def joinedLeftOuterOnWith (predicate : QuerySemantics.Predicate)
    (rightRows : List QuerySemantics.Row) (nullRight : QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row) : Expr QuerySemantics.Row :=
  .embed (fun
    | .values _ => none
    | .joined leftRow rightRow => some (leftRow, rightRow))
    (.leftOuter inferInstance (supportDomain rightRows) nullRight
      (fun leftRow rightRow =>
        predicate.eval (.joined leftRow rightRow)) left right)

def joinedLeftOuterOn (predicate : QuerySemantics.Predicate)
    (rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row) : Expr QuerySemantics.Row :=
  joinedLeftOuterOnWith predicate rightRows (.values []) left right

private theorem hasMatch_support (predicate : QuerySemantics.Predicate)
    (rows : List QuerySemantics.Row) (left : QuerySemantics.Row) :
    hasMatch (supportDomain rows)
        (fun leftRow rightRow =>
          predicate.eval (.joined leftRow rightRow))
        (ofList rows) left =
      rows.any (fun rightRow =>
        predicate.eval (.joined left rightRow) == .true) := by
  apply Bool.eq_iff_iff.mpr
  simp [hasMatch, supportDomain, Core.mem_deduplicate, ofList,
    listMultiplicity_eq_zero_iff]
  constructor
  · rintro ⟨row, member, passes, _⟩
    exact ⟨row, member, passes⟩
  · rintro ⟨row, member, passes⟩
    exact ⟨row, member, passes, member⟩

private theorem leftOuterMatches_isEmpty
    (predicate : QuerySemantics.Predicate)
    (left : QuerySemantics.Row) (rows : List QuerySemantics.Row) :
    ((rows.map fun rightRow =>
        QuerySemantics.Row.joined left rightRow).filter
      (fun row => predicate.eval row == .true)).isEmpty =
      !(rows.any fun rightRow =>
        predicate.eval (.joined left rightRow) == .true) := by
  apply Bool.eq_iff_iff.mpr
  simp [List.isEmpty_iff]

private theorem listMultiplicity_leftOuterForRowsWith
    (predicate : QuerySemantics.Predicate)
    (nullRight left : QuerySemantics.Row) (rows : List QuerySemantics.Row)
    (target : QuerySemantics.Row) :
    listMultiplicity target
        (QuerySemantics.leftOuterForRowsWith predicate nullRight left rows) =
      match target with
      | .values _ => 0
      | .joined leftTarget rightTarget =>
          if left = leftTarget then
            if rows.any (fun rightRow =>
                predicate.eval (.joined left rightRow) == .true) then
              if predicate.eval (.joined leftTarget rightTarget) = .true then
                listMultiplicity rightTarget rows
              else 0
            else if rightTarget = nullRight then 1 else 0
          else 0 := by
  cases target with
  | values cells =>
      simp only [QuerySemantics.leftOuterForRowsWith]
      rw [leftOuterMatches_isEmpty]
      cases anyResult : rows.any (fun rightRow =>
          predicate.eval (.joined left rightRow) == .true) <;>
        simp [anyResult, listMultiplicity_filter,
          listMultiplicity_values_map_joined, listMultiplicity]
  | joined leftTarget rightTarget =>
      by_cases leftEqual : left = leftTarget
      · subst leftTarget
        simp only [QuerySemantics.leftOuterForRowsWith]
        rw [leftOuterMatches_isEmpty]
        cases anyResult : rows.any (fun rightRow =>
            predicate.eval (.joined left rightRow) == .true) with
        | false =>
            by_cases rightEqual : rightTarget = nullRight
            · subst rightTarget
              simp [anyResult, listMultiplicity]
            · have reverse : nullRight ≠ rightTarget :=
                Ne.symm rightEqual
              simp [anyResult, listMultiplicity, rightEqual, reverse]
        | true =>
          simp [anyResult, listMultiplicity_filter,
              listMultiplicity_joined_map_joined, listMultiplicity]
      · simp only [QuerySemantics.leftOuterForRowsWith]
        rw [leftOuterMatches_isEmpty]
        cases anyResult : rows.any (fun rightRow =>
            predicate.eval (.joined left rightRow) == .true) <;>
          simp [anyResult, listMultiplicity_filter,
            listMultiplicity_joined_map_joined, listMultiplicity, leftEqual]

theorem listMultiplicity_leftOuterOnRowsWith
    (predicate : QuerySemantics.Predicate)
    (nullRight : QuerySemantics.Row)
    (leftRows rightRows : List QuerySemantics.Row)
    (target : QuerySemantics.Row) :
    listMultiplicity target
        (QuerySemantics.leftOuterOnRowsWith predicate nullRight leftRows rightRows) =
      match target with
      | .values _ => 0
      | .joined leftTarget rightTarget =>
          if rightRows.any (fun rightRow =>
              predicate.eval (.joined leftTarget rightRow) == .true) then
            if predicate.eval (.joined leftTarget rightTarget) = .true then
              listMultiplicity leftTarget leftRows *
                listMultiplicity rightTarget rightRows
            else 0
          else if rightTarget = nullRight then
            listMultiplicity leftTarget leftRows
          else 0 := by
  induction leftRows with
  | nil =>
      cases target <;>
        simp [QuerySemantics.leftOuterOnRowsWith, listMultiplicity]
  | cons row rows induction =>
      rw [show QuerySemantics.leftOuterOnRowsWith predicate nullRight
          (row :: rows) rightRows =
        QuerySemantics.leftOuterForRowsWith predicate nullRight row rightRows ++
          QuerySemantics.leftOuterOnRowsWith predicate nullRight rows rightRows by rfl]
      rw [listMultiplicity_append,
        listMultiplicity_leftOuterForRowsWith, induction]
      cases target with
      | values cells => rfl
      | joined leftTarget rightTarget =>
          by_cases leftEqual : row = leftTarget
          · subst leftTarget
            cases anyResult : rightRows.any (fun rightRow =>
                predicate.eval (.joined row rightRow) == .true) with
            | false =>
                by_cases rightEqual : rightTarget = nullRight
                · subst rightTarget
                  simp [anyResult, listMultiplicity]
                · have reverse : nullRight ≠ rightTarget :=
                    Ne.symm rightEqual
                  simp [anyResult, rightEqual, reverse, listMultiplicity]
            | true =>
                by_cases passes :
                    predicate.eval (.joined row rightTarget) = .true <;>
                  simp [anyResult, passes, listMultiplicity, Nat.add_mul]
          · simp [leftEqual, listMultiplicity]

theorem listMultiplicity_leftOuterOnRows
    (predicate : QuerySemantics.Predicate)
    (leftRows rightRows : List QuerySemantics.Row)
    (target : QuerySemantics.Row) :
    listMultiplicity target
        (QuerySemantics.leftOuterOnRows predicate leftRows rightRows) =
      match target with
      | .values _ => 0
      | .joined leftTarget rightTarget =>
          if rightRows.any (fun rightRow =>
              predicate.eval (.joined leftTarget rightRow) == .true) then
            if predicate.eval (.joined leftTarget rightTarget) = .true then
              listMultiplicity leftTarget leftRows *
                listMultiplicity rightTarget rightRows
            else 0
          else if rightTarget = .values [] then
            listMultiplicity leftTarget leftRows
          else 0 := by
  simpa [QuerySemantics.leftOuterOnRows] using
    listMultiplicity_leftOuterOnRowsWith predicate (.values [])
      leftRows rightRows target

private theorem hasMatch_support_true (first : QuerySemantics.Row)
    (rows : List QuerySemantics.Row) (left : QuerySemantics.Row) :
    hasMatch (supportDomain (first :: rows)) (fun _ _ => .true)
      (ofList (first :: rows)) left = true := by
  apply List.any_eq_true.mpr
  refine ⟨first, ?_, ?_⟩
  · exact (Core.mem_deduplicate first (first :: rows)).2 (by simp)
  · simp [ofList, multiplicity_nonzero_member first (first :: rows) (by simp)]

private theorem listMultiplicity_leftNullRows
    (target : QuerySemantics.Row) (left : List QuerySemantics.Row) :
    listMultiplicity target
        (left.map fun row => QuerySemantics.Row.joined row (.values [])) =
      match target with
      | .values _ => 0
      | .joined leftTarget rightTarget =>
          if rightTarget = .values [] then listMultiplicity leftTarget left
          else 0 := by
  induction left with
  | nil => cases target <;> simp [listMultiplicity]
  | cons row rows induction =>
      cases target with
      | values cells => simp [listMultiplicity, induction]
      | joined leftTarget rightTarget =>
          by_cases rightEqual : rightTarget = .values []
          · subst rightTarget
            simp [listMultiplicity, induction]
          · have reverse : QuerySemantics.Row.values [] ≠ rightTarget :=
              Ne.symm rightEqual
            simp [listMultiplicity, induction, rightEqual, reverse]

/-- The executable cross left-outer join is exactly the typed outer relation:
an empty right bag contributes one NULL-shaped row per left occurrence, while
a nonempty right bag contributes the ordinary multiplicity product. -/
theorem joinedLeftOuterRows_eval (leftRows rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row)
    (leftExact : eval left = ofList leftRows)
    (rightExact : eval right = ofList rightRows) :
    eval (joinedLeftOuterRows rightRows left right) =
      ofList (QuerySemantics.leftJoinRows leftRows rightRows) := by
  cases rightRows with
  | nil =>
      apply KRelation.Relation.ext
      intro target
      cases target with
      | values cells =>
          simp [joinedLeftOuterRows, eval, leftOuterRelation, hasMatch,
            rightExact, QuerySemantics.leftJoinRows, ofList,
            listMultiplicity_leftNullRows]
      | joined leftTarget rightTarget =>
          have noMatch : hasMatch (supportDomain []) (fun _ _ => .true)
              (eval right) leftTarget = false := by
            rw [rightExact]
            rfl
          rw [show eval (joinedLeftOuterRows [] left right)
              (.joined leftTarget rightTarget) =
            if rightTarget = .values [] then eval left leftTarget else 0 by
              simp [joinedLeftOuterRows, eval, leftOuterRelation,
                noMatch]]
          rw [leftExact]
          simp [QuerySemantics.leftJoinRows, ofList,
            listMultiplicity_leftNullRows]
  | cons first rows =>
      apply KRelation.Relation.ext
      intro target
      cases target with
      | values cells =>
          simp [joinedLeftOuterRows, eval, QuerySemantics.leftJoinRows,
            ofList, listMultiplicity_joinRows]
      | joined leftTarget rightTarget =>
          have someMatch : hasMatch (supportDomain (first :: rows))
              (fun _ _ => .true) (eval right) leftTarget = true := by
            rw [rightExact]
            exact hasMatch_support_true first rows leftTarget
          rw [show eval (joinedLeftOuterRows (first :: rows) left right)
              (.joined leftTarget rightTarget) =
            eval left leftTarget * eval right rightTarget by
              simp [joinedLeftOuterRows, eval, leftOuterRelation,
                someMatch]]
          rw [leftExact, rightExact]
          simp [QuerySemantics.leftJoinRows, ofList,
            listMultiplicity_joinRows]

/-- The predicate-bearing executable left outer join agrees with the typed
bag semantics for every SQL truth value.  In particular, both `false` and
`unknown` produce the NULL-extended row when no right candidate is `true`,
and matching duplicates multiply their bag multiplicities. -/
theorem joinedLeftOuterOnWith_eval (predicate : QuerySemantics.Predicate)
    (nullRight : QuerySemantics.Row) (leftRows rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row)
    (leftExact : eval left = ofList leftRows)
    (rightExact : eval right = ofList rightRows) :
    eval (joinedLeftOuterOnWith predicate rightRows nullRight left right) =
      ofList (QuerySemantics.leftOuterOnRowsWith predicate nullRight
        leftRows rightRows) := by
  apply KRelation.Relation.ext
  intro target
  cases target with
  | values cells =>
      simp [joinedLeftOuterOnWith, eval, leftOuterRelation, ofList,
        listMultiplicity_leftOuterOnRowsWith]
  | joined leftTarget rightTarget =>
      rw [show eval (joinedLeftOuterOnWith predicate rightRows nullRight left right)
          (.joined leftTarget rightTarget) =
        if hasMatch (supportDomain rightRows)
            (fun leftRow rightRow =>
              predicate.eval (.joined leftRow rightRow))
            (eval right) leftTarget then
          if predicate.eval (.joined leftTarget rightTarget) = .true then
            eval left leftTarget * eval right rightTarget
          else 0
        else if rightTarget = nullRight then eval left leftTarget else 0 by
          rfl]
      rw [leftExact, rightExact, hasMatch_support]
      simp [ofList, listMultiplicity_leftOuterOnRowsWith]

theorem joinedLeftOuterOn_eval (predicate : QuerySemantics.Predicate)
    (leftRows rightRows : List QuerySemantics.Row)
    (left right : Expr QuerySemantics.Row)
    (leftExact : eval left = ofList leftRows)
    (rightExact : eval right = ofList rightRows) :
    eval (joinedLeftOuterOn predicate rightRows left right) =
      ofList (QuerySemantics.leftOuterOnRows predicate leftRows rightRows) := by
  exact joinedLeftOuterOnWith_eval predicate (.values []) leftRows rightRows
    left right leftExact rightExact

/-- Translation of the existing optimizer plan into typed bag algebra. -/
def ofPlan? (database : Core.Database) : QuerySemantics.Plan → Option
    (Expr QuerySemantics.Row)
  | .table name => some (coreTable database name)
  | .rows rows => some (.relation (ofList rows))
  | .unionAll left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (.unionAll translatedLeft translatedRight)
  | .intersectAll left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (.intersect translatedLeft translatedRight)
  | .exceptAll left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (.except translatedLeft translatedRight)
  | .distinct input => do
      let translated ← ofPlan? database input
      some (.distinct translated)
  | .filter predicate input => do
      let translated ← ofPlan? database input
      some (.select predicate.eval translated)
  | .project projection input => do
      let translated ← ofPlan? database input
      some (.project inferInstance
        (supportDomain (QuerySemantics.evalPlan database input))
        projection.apply translated)
  | .innerJoin left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (joinedRows translatedLeft translatedRight)
  | .leftOuterJoin left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (joinedLeftOuterRows (QuerySemantics.evalPlan database right)
        translatedLeft translatedRight)
  | .leftOuterOn predicate left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (joinedLeftOuterOn predicate
        (QuerySemantics.evalPlan database right)
        translatedLeft translatedRight)
  | .leftOuterOnWith predicate nullRight left right => do
      let translatedLeft ← ofPlan? database left
      let translatedRight ← ofPlan? database right
      some (joinedLeftOuterOnWith predicate
        (QuerySemantics.evalPlan database right) nullRight
        translatedLeft translatedRight)
  | .groupCount key input => do
      let translated ← ofPlan? database input
      some (.groupCount inferInstance
        (supportDomain (QuerySemantics.evalPlan database input))
        key translated)
  | .groupSum key measure input => do
      let translated ← ofPlan? database input
      some (.groupSum inferInstance
        (supportDomain (QuerySemantics.evalPlan database input))
        key measure translated)

theorem ofPlan?_eval (database : Core.Database) :
    ∀ (plan : QuerySemantics.Plan) (translated : Expr QuerySemantics.Row),
      ofPlan? database plan = some translated →
      eval translated = ofList (QuerySemantics.evalPlan database plan)
  | .table name, translated, success => by
      simp only [ofPlan?, Option.some.injEq] at success
      subst translated
      rfl
  | .rows rows, translated, success => by
      simp only [ofPlan?, Option.some.injEq] at success
      subst translated
      rfl
  | .unionAll left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              rw [show eval (.unionAll translatedLeft translatedRight) =
                KRelation.unionAll (eval translatedLeft)
                  (eval translatedRight) by rfl]
              rw [ofPlan?_eval database left translatedLeft leftResult]
              rw [ofPlan?_eval database right translatedRight rightResult]
              rw [← ofList_append]
              rfl
  | .intersectAll left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              rw [show eval (.intersect translatedLeft translatedRight) =
                KRelation.intersect (eval translatedLeft)
                  (eval translatedRight) by rfl]
              rw [ofPlan?_eval database left translatedLeft leftResult]
              rw [ofPlan?_eval database right translatedRight rightResult]
              rw [← ofList_bagIntersect]
              rfl
  | .exceptAll left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              rw [show eval (.except translatedLeft translatedRight) =
                KRelation.except (eval translatedLeft)
                  (eval translatedRight) by rfl]
              rw [ofPlan?_eval database left translatedLeft leftResult]
              rw [ofPlan?_eval database right translatedRight rightResult]
              rw [← ofList_bagExcept]
              rfl
  | .distinct input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.distinct translatedInput) =
            KRelation.distinct (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [← ofList_deduplicate]
          rfl
  | .filter predicate input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.select predicate.eval translatedInput) =
            KRelation.select predicate.eval (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [← ofList_whereRows]
          rfl
  | .project projection input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.project inferInstance
              (supportDomain (QuerySemantics.evalPlan database input))
              projection.apply translatedInput) =
            KRelation.project
              (supportDomain (QuerySemantics.evalPlan database input)).values
              projection.apply (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [project_ofList]
          rfl
  | .innerJoin left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              rw [joinedRows_eval]
              rw [ofPlan?_eval database left translatedLeft leftResult]
              rw [ofPlan?_eval database right translatedRight rightResult]
              rw [← ofList_joinRows]
              rfl
  | .leftOuterJoin left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              exact joinedLeftOuterRows_eval
                (QuerySemantics.evalPlan database left)
                (QuerySemantics.evalPlan database right)
                translatedLeft translatedRight
                (ofPlan?_eval database left translatedLeft leftResult)
                (ofPlan?_eval database right translatedRight rightResult)
  | .leftOuterOn predicate left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              exact joinedLeftOuterOn_eval predicate
                (QuerySemantics.evalPlan database left)
                (QuerySemantics.evalPlan database right)
                translatedLeft translatedRight
                (ofPlan?_eval database left translatedLeft leftResult)
                (ofPlan?_eval database right translatedRight rightResult)
  | .leftOuterOnWith predicate nullRight left right, translated, success => by
      simp only [ofPlan?] at success
      cases leftResult : ofPlan? database left with
      | none => simp [leftResult] at success
      | some translatedLeft =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at success
          cases rightResult : ofPlan? database right with
          | none => simp [rightResult] at success
          | some translatedRight =>
              simp only [rightResult, Option.some.injEq] at success
              subst translated
              exact joinedLeftOuterOnWith_eval predicate nullRight
                (QuerySemantics.evalPlan database left)
                (QuerySemantics.evalPlan database right)
                translatedLeft translatedRight
                (ofPlan?_eval database left translatedLeft leftResult)
                (ofPlan?_eval database right translatedRight rightResult)
  | .groupCount key input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.groupCount inferInstance
              (supportDomain (QuerySemantics.evalPlan database input))
              key translatedInput) =
            KRelation.groupCount
              (supportDomain
                (QuerySemantics.evalPlan database input)).values
              key (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [← ofList_groupCountRows]
          rfl
  | .groupSum key measure input, translated, success => by
      simp only [ofPlan?] at success
      cases inputResult : ofPlan? database input with
      | none => simp [inputResult] at success
      | some translatedInput =>
          simp only [inputResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at success
          subst translated
          rw [show eval (.groupSum inferInstance
              (supportDomain (QuerySemantics.evalPlan database input))
              key measure translatedInput) =
            KRelation.groupSum
              (supportDomain
                (QuerySemantics.evalPlan database input)).values
              key measure (eval translatedInput) by rfl]
          rw [ofPlan?_eval database input translatedInput inputResult]
          rw [← ofList_groupSumRows]
          rfl

theorem select_product_left (predicate : Left → Truth)
    (left : Relation Left) (right : Relation Right) :
    KRelation.select (fun row : Left × Right => predicate row.1)
        (KRelation.join left right) =
      KRelation.join (KRelation.select predicate left) right := by
  apply KRelation.Relation.ext
  intro row
  by_cases passes : predicate row.1 = .true <;>
    simp [KRelation.select, KRelation.join, passes]

/-- Predicate pushdown through product, stated over the general algebra. -/
theorem selectProductLeft_eval (predicate : Left → Truth)
    (left : Expr Left) (right : Expr Right) :
    eval (.select (fun row : Left × Right => predicate row.1)
        (.product left right)) =
      eval (.product (.select predicate left) right) :=
  select_product_left predicate (eval left) (eval right)

theorem selectUnionAll_eval (predicate : Row → Truth)
    (left right : Expr Row) :
    eval (.select predicate (.unionAll left right)) =
      eval (.unionAll (.select predicate left) (.select predicate right)) :=
  KRelation.select_unionAll predicate (eval left) (eval right)

theorem productUnionAllLeft_eval (first second : Expr Left)
    (right : Expr Right) :
    eval (.product (.unionAll first second) right) =
      eval (.unionAll (.product first right) (.product second right)) :=
  KRelation.join_unionAll_left (eval first) (eval second) (eval right)

theorem productUnionAllRight_eval (left : Expr Left)
    (first second : Expr Right) :
    eval (.product left (.unionAll first second)) =
      eval (.unionAll (.product left first) (.product left second)) :=
  KRelation.join_unionAll_right (eval left) (eval first) (eval second)

theorem selectFusion_eval (first second : Row → Truth) (input : Expr Row) :
    eval (.select first (.select second input)) =
      eval (.select (fun row => Truth.and (first row) (second row)) input) := by
  apply KRelation.Relation.ext
  intro row
  cases firstResult : first row <;> cases secondResult : second row <;>
    simp [eval, KRelation.select, Truth.and, firstResult, secondResult]

theorem distinctIdempotent_eval (input : Expr Row) :
    eval (.distinct (.distinct input)) = eval (.distinct input) :=
  KRelation.distinct_idempotent (eval input)

def swapProduct (input : Expr (Left × Right)) : Expr (Right × Left) :=
  .rename (fun row => (row.2, row.1)) input

theorem swapProduct_eval (left : Expr Left) (right : Expr Right) :
    eval (swapProduct (.product left right)) = eval (.product right left) := by
  exact KRelation.swap_join (eval left) (eval right)

def reassociateProduct (input : Expr ((First × Second) × Third)) :
    Expr (First × (Second × Third)) :=
  .rename (fun row => ((row.1, row.2.1), row.2.2)) input

theorem reassociateProduct_eval (first : Expr First) (second : Expr Second)
    (third : Expr Third) :
    eval (reassociateProduct (.product (.product first second) third)) =
      eval (.product first (.product second third)) := by
  apply KRelation.Relation.ext
  intro row
  simp [reassociateProduct, eval, KRelation.join, Nat.mul_assoc]

theorem project_unionAll (decEq : DecidableEq Output) (domain : Domain Input)
    (projection : Input → Output) (left right : Expr Input) :
    eval (.project decEq domain projection (.unionAll left right)) =
      eval (.unionAll (.project decEq domain projection left)
        (.project decEq domain projection right)) := by
  let _ : DecidableEq Output := decEq
  exact KRelation.project_unionAll domain.values projection
    (eval left) (eval right)

theorem groupCountUnionAll_eval (decEq : DecidableEq Group)
    (domain : Domain Input) (key : Input → Group) (left right : Expr Input) :
    eval (.groupCount decEq domain key (.unionAll left right)) =
      eval (.unionAll (.groupCount decEq domain key left)
        (.groupCount decEq domain key right)) := by
  let _ : DecidableEq Group := decEq
  exact KRelation.groupCount_unionAll domain.values key (eval left) (eval right)

theorem groupSumUnionAll_eval (decEq : DecidableEq Group)
    (domain : Domain Input) (key : Input → Group) (measure : Input → Nat)
    (left right : Expr Input) :
    eval (.groupSum decEq domain key measure (.unionAll left right)) =
      eval (.unionAll (.groupSum decEq domain key measure left)
        (.groupSum decEq domain key measure right)) := by
  let _ : DecidableEq Group := decEq
  exact KRelation.groupSum_unionAll domain.values key measure
    (eval left) (eval right)

/-- A predicate depending only on the preserved side of a left outer join may
be pushed below the join.  No corresponding theorem is stated for the nullable
right side: that rewrite is unsound in general under SQL three-valued logic. -/
theorem selectLeftOuterLeft_eval (decEq : DecidableEq Right)
    (domain : Domain Right) (nullRight : Right)
    (joinPredicate : Left → Right → Truth) (predicate : Left → Truth)
    (left : Expr Left) (right : Expr Right) :
    eval (.select (fun row : Left × Right => predicate row.1)
        (.leftOuter decEq domain nullRight joinPredicate left right)) =
      eval (.leftOuter decEq domain nullRight joinPredicate
        (.select predicate left) right) := by
  apply KRelation.Relation.ext
  intro row
  cases predicateResult : predicate row.1 <;>
    simp [eval, KRelation.select, leftOuterRelation, hasMatch,
      predicateResult]

theorem leftOuter_unmatched [DecidableEq Right] (domain : Domain Right)
    (nullRight : Right) (predicate : Left → Right → Truth)
    (left : Relation Left) (right : Relation Right) (row : Left)
    (none : hasMatch domain predicate right row = false) :
    leftOuterRelation domain nullRight predicate left right (row, nullRight) =
      left row := by
  simp [leftOuterRelation, none]

theorem leftOuter_matched [DecidableEq Right] (domain : Domain Right)
    (nullRight : Right) (predicate : Left → Right → Truth)
    (left : Relation Left) (right : Relation Right) (leftRow : Left)
    (rightRow : Right) (some : hasMatch domain predicate right leftRow = true)
    (predicateTrue : predicate leftRow rightRow = .true) :
    leftOuterRelation domain nullRight predicate left right
        (leftRow, rightRow) = left leftRow * right rightRow := by
  simp [leftOuterRelation, some, predicateTrue]

end RelationalAlgebra
end SQLeanite
