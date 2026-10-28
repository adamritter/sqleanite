import SQLeanite.KRelation
import SQLeanite.QuerySemantics

namespace SQLeanite
namespace RelationalAlgebra

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

/-- A list's bag is the singleton of its head unioned with the bag of its tail.
The write side needs this to turn `row :: rows` into `single row ∪ ofList rows`
without unfolding multiplicity arithmetic at every use. -/
theorem ofList_cons [DecidableEq Row] (row : Row) (rows : List Row) :
    ofList (row :: rows) =
      KRelation.unionAll (KRelation.single row) (ofList rows) := by
  apply KRelation.Relation.ext
  intro target
  show listMultiplicity target (row :: rows) =
    KRelation.single row target + listMultiplicity target rows
  simp only [listMultiplicity, KRelation.single]
  by_cases hit : row = target
  · rw [if_pos hit, if_pos hit.symm]
  · rw [if_neg hit, if_neg (fun equal => hit equal.symm)]

theorem listMultiplicity_eq_count [DecidableEq Row]
    (target : Row) (rows : List Row) :
    listMultiplicity target rows = rows.count target := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      by_cases equal : row = target <;>
        simp [listMultiplicity, List.count_cons, equal, induction,
          Nat.add_comm]

/-- Reordering a list does not change its bag.  Every write-side statement that
routes through a permutation lemma needs exactly this to cross from lists to
multiplicities. -/
theorem ofList_perm [DecidableEq Row] {left right : List Row}
    (permuted : left.Perm right) : ofList left = ofList right := by
  apply KRelation.Relation.ext
  intro target
  show listMultiplicity target left = listMultiplicity target right
  rw [listMultiplicity_eq_count, listMultiplicity_eq_count, permuted.count_eq]

private theorem multiplicity_zero_absent [DecidableEq Row]
    (target : Row) (rows : List Row) (absent : target ∉ rows) :
    listMultiplicity target rows = 0 := by
  rw [listMultiplicity_eq_count]
  exact List.count_eq_zero.mpr absent

theorem multiplicity_nonzero_member [DecidableEq Row]
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

theorem groupSumRows_support [DecidableEq Input]
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

theorem listMultiplicity_groupValueMap [DecidableEq Group]
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

end RelationalAlgebra

end SQLeanite
