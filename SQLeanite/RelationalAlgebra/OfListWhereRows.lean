import SQLeanite.CoreEngine.ChooseExtremeEqLeftOrRight
import SQLeanite.RelationalAlgebra.Relation

namespace SQLeanite
namespace RelationalAlgebra

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

theorem listMultiplicity_values_map_joined
    (cells : List Core.Value) (left : QuerySemantics.Row)
    (right : List QuerySemantics.Row) :
    listMultiplicity (QuerySemantics.Row.values cells)
      (right.map fun row => QuerySemantics.Row.joined left row) = 0 := by
  induction right with
  | nil => rfl
  | cons row rows induction =>
      simp [listMultiplicity, induction]

theorem listMultiplicity_joined_map_joined
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

/-- Materialized COUNT and the live sorted GROUP BY presentation have the
same bag of normalized group keys and multiplicities. -/
theorem materializedCountRows_eq_coreGroup (query : Core.GroupQuery)
    (rows : List Core.Row) :
    ofList (materializedCountRows query.rowKey (query.selectedRows rows)) =
      ofList ((query.groupKeys rows).map fun group => (group, query.keyCount rows group)) := by
  have mapped : materializedCountRows query.rowKey (query.selectedRows rows) =
      (Core.deduplicate ((query.selectedRows rows).map query.rowKey)).map
        (fun group => (group, query.keyCount rows group)) := by
    unfold materializedCountRows
    apply List.map_congr_left
    intro group _member
    simp [coreGroup_keyCount_eq_multiplicity]
  rw [mapped]
  exact ofList_perm ((List.mergeSort_perm _ _).symm.map _)

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
  simp only [bind, Functor.map, Except.bind, pure, Except.pure] at success
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
  simp only [bind, Functor.map, Except.bind, pure, Except.pure]
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
  | .key position, value => value = (query.outputKey rows group)[position]?.getD .null
  | .countStar, .integer integer =>
      integer.value = Int.ofNat (query.keyCount rows group)
  | .countStar, _ => False
  | .countColumn column, .integer integer =>
      integer.value = Int.ofNat ((query.keyRows rows group).countP
        fun row => row.value column != .null)
  | .countColumn _, _ => False
  | .sumColumn column, value =>
      match Core.columnIntegers column (query.keyRows rows group) with
      | .ok integers =>
          match value with
          | .null => integers = []
          | .integer integer => integer.value = (integers.map (·.value)).sum
          | .realBits _ | .text _ | .blob _ => False
      | .error _ => SQLite.AggregateSum.sum
          ((query.keyRows rows group).map (·.value column)) = .ok value
  | .averageColumn column, value =>
      value = Core.averageColumn column (query.keyRows rows group)
  | .totalColumn column, value =>
      value = Core.totalColumn column (query.keyRows rows group)
  | .minColumn column, value =>
      value = Core.extremeColumn true column (query.keyRows rows group)
  | .maxColumn column, value =>
      value = Core.extremeColumn false column (query.keyRows rows group)

end RelationalAlgebra

end SQLeanite
