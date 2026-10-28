import SQLeanite.CoreEngine.RowValue
import SQLeanite.SQLite.AggregateSum

namespace SQLeanite
namespace Core

private theorem max_div_le_max (rows divisor : Nat) :
    max 1 (rows / divisor) ≤ max 1 rows := by
  exact Nat.max_le.2 ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.div_le_self rows divisor) (Nat.le_max_right _ _)⟩

/-- Cost-aware access-path choice. Applicable indexes have a lower selectivity
estimate than a scan; unsupported predicate shapes retain the scan. -/
def Table.chooseAccessPath (table : Table) (predicate : Option Predicate) :
    AccessPath :=
  match predicate with
  | some (.equal column value) =>
      match value with
      | .integer rowid =>
          if column = table.schema.primaryKey then .primaryKey rowid
          else match table.indexes.find? (fun index => index.column = column) with
            | some index => .equalityIndex index
            | none => .fullScan
      | _ =>
          match table.indexes.find? (fun index => index.column = column) with
          | some index => .equalityIndex index
          | none => .fullScan
  | some (.compare _ column _) =>
      match table.indexes.find? (fun index => index.column = column) with
      | some index => .rangeIndex index
      | none => .fullScan
  | _ => .fullScan

private theorem chooseAccessPath_primaryKey {table : Table}
    {predicate : Option Predicate} {rowid : Integer}
    (chosen : table.chooseAccessPath predicate = .primaryKey rowid) :
    predicate = some
      (.equal table.schema.primaryKey (.integer rowid)) := by
  cases predicate with
  | none => simp [Table.chooseAccessPath] at chosen
  | some predicate =>
      cases predicate with
      | equal column value =>
          cases value with
          | integer target =>
              simp only [Table.chooseAccessPath] at chosen
              split at chosen
              next sameColumn =>
                have targetEqual : target = rowid :=
                  AccessPath.primaryKey.inj chosen
                subst target
                rw [sameColumn]
              next different =>
                split at chosen <;> contradiction
          | null | realBits | text | blob =>
              simp only [Table.chooseAccessPath] at chosen
              split at chosen <;> contradiction
      | compare operation column value =>
          simp only [Table.chooseAccessPath] at chosen
          split at chosen <;> contradiction
      | notEqual | isNull | not | and | or =>
          simp [Table.chooseAccessPath] at chosen

theorem Table.chooseAccessPath_estimatedRows_le (table : Table)
    (predicate : Option Predicate) :
    (table.chooseAccessPath predicate).estimatedRows table.rows.length ≤
      max 1 table.rows.length := by
  cases predicate with
  | none =>
      simp only [Table.chooseAccessPath, AccessPath.estimatedRows]
      exact Nat.le_max_right _ _
  | some predicate =>
    cases predicate with
    | equal column value =>
        cases value with
        | integer rowid =>
            simp only [Table.chooseAccessPath]
            split
            · simp only [AccessPath.estimatedRows]
              exact Nat.le_max_left _ _
            · split
              · exact max_div_le_max _ _
              · exact Nat.le_max_right _ _
        | null | realBits | text | blob =>
            simp only [Table.chooseAccessPath]
            split
            · exact max_div_le_max _ _
            · exact Nat.le_max_right _ _
    | compare operation column value =>
        simp only [Table.chooseAccessPath]
        split
        · exact max_div_le_max _ _
        · exact Nat.le_max_right _ _
    | notEqual | isNull | not | and | or =>
        simp only [Table.chooseAccessPath, AccessPath.estimatedRows]
        exact Nat.le_max_right _ _

/-- Rows the planner feeds to a query: index candidates when an index applies,
otherwise the whole table. -/
def Table.plannedRows (table : Table) (query : Query) : List Row :=
  match table.chooseAccessPath query.predicate with
  | .primaryKey rowid => table.primaryKeyRows rowid
  | .equalityIndex index | .rangeIndex index =>
      (indexedCandidates index query.predicate table.rows).getD table.rows
  | .fullScan => table.rows

/-- **Planning is semantics-preserving.** Using an index changes nothing a query
can observe, so the executor may substitute `plannedRows` for the full table. -/
theorem Query.eval_plannedRows (table : Table) (query : Query) :
    query.eval (table.plannedRows query) = query.eval table.rows := by
  unfold Table.plannedRows
  cases chosen : table.chooseAccessPath query.predicate with
  | fullScan => simp [chosen]
  | primaryKey rowid =>
      simp only [chosen]
      exact Query.eval_primaryKey table query rowid
        (chooseAccessPath_primaryKey chosen)
  | equalityIndex index =>
      cases narrowed : indexedCandidates index query.predicate table.rows with
      | none => simp [chosen, narrowed]
      | some candidates =>
          simp only [chosen, narrowed, Option.getD_some]
          exact Query.eval_indexed index query table.rows candidates narrowed
  | rangeIndex index =>
      cases narrowed : indexedCandidates index query.predicate table.rows with
      | none => simp [chosen, narrowed]
      | some candidates =>
          simp only [chosen, narrowed, Option.getD_some]
          exact Query.eval_indexed index query table.rows candidates narrowed

def Database.modifyTable (database : Database) (name : String)
    (operation : Table → Except String Table) : Except String Database := do
  let table ← match database.findTable? name with
    | some table => .ok table
    | none => .error s!"no such table: {name}"
  let replacement ← operation table
  database.updateTable replacement

theorem Database.modifyTable_exact {database next : Database} {name : String}
    {operation : Table → Except String Table}
    (success : database.modifyTable name operation = .ok next) :
    ∃ table replacement,
      database.findTable? name = some table ∧
      operation table = .ok replacement ∧
      database.updateTable replacement = .ok next := by
  unfold Database.modifyTable at success
  cases found : database.findTable? name with
  | none =>
      simp [found, bind, Functor.map, Except.bind, pure, Except.pure,
        Except.map] at success
  | some table =>
      cases operated : operation table with
      | error message =>
          simp [found, operated, bind, Functor.map, Except.bind, pure, Except.pure,
            Except.map] at success
      | ok replacement =>
          cases updated : database.updateTable replacement with
          | error message =>
              simp [found, operated, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
          | ok output =>
              simp [found, operated, updated, bind, Functor.map, Except.bind,
                pure, Except.pure, Except.map] at success
              subst next
              exact ⟨table, replacement, rfl, operated, updated⟩

/-- Resolve a declared TEXT primary key through its proof-carrying balanced
map.  Keeping this operation separate makes the trust argument explicit: the
map is not an opportunistic cache, but an exact abstraction of the logical row
list established by `declaredKeyMapRepresents`. -/
def Table.findDeclaredTextRowid? (table : Table) (text : PhysicalCodec.Text) :
    Option Integer :=
  if table.schema.hasHiddenRowid then
    (table.declaredKeyMap.get? (.value (.text text))).map (·.rowid)
  else none

/-- A successful declared-key route names a real logical row with precisely
that key.  Thus the point updater cannot be sent to an unrelated row by stale
or merely advisory index data. -/
theorem Table.findDeclaredTextRowid?_some_mem {table : Table}
    {text : PhysicalCodec.Text} {rowid : Integer}
    (found : table.findDeclaredTextRowid? text = some rowid) :
    ∃ row, row ∈ table.rows ∧ row.rowid = rowid ∧
      row.declaredKey table.schema = .value (.text text) := by
  unfold Table.findDeclaredTextRowid? at found
  split at found
  next hidden =>
    rcases Option.map_eq_some_iff.mp found with ⟨row, owner, rowidEqual⟩
    have represented := table.declaredKeyMapRepresents hidden (.value (.text text))
    rw [owner] at represented
    have logical : table.rows.find? (fun candidate =>
        candidate.declaredKey table.schema == .value (.text text)) = some row :=
      represented.symm
    refine ⟨row, List.mem_of_find?_eq_some logical, ?_, ?_⟩
    · exact rowidEqual
    · simpa only [beq_iff_eq] using List.find?_some logical
  next => contradiction

/-- Recognize the UPDATE shapes that can safely use one primary-tree lookup.
Besides the INTEGER PRIMARY KEY alias, a declared TEXT PRIMARY KEY first
routes through its exact key map and then uses the returned hidden rowid. -/
def Table.pointUpdateRowid? (table : Table)
    (assignments : List (Nat × Value)) : Option Predicate → Option Integer
  | some (.equal column value) =>
      if assignments.all (fun assignment => assignment.1 != column) then
        if column == table.schema.primaryKey then
          match value with
          | .integer rowid => some rowid
          | _ => none
        else if table.schema.hasHiddenRowid &&
            column == table.schema.declaredPrimaryKey then
          match value with
          | .text text => table.findDeclaredTextRowid? text
          | _ => none
        else none
      else none
  | _ => none

/-- The logical UPDATE operation named independently of the statement
executor, so execute-level correspondence can expose exactly which table
transformation succeeded. -/
def Table.updateWhere (table : Table) (assignments : List (Nat × Value))
    (predicate : Option Predicate) : Except String (Table × Nat) :=
  match table.pointUpdateRowid? assignments predicate with
  | some rowid => table.patchRowid assignments rowid
  | none => do
      let replacement ← table.patchRows assignments (selects predicate)
      return (replacement, (table.rows.filter (selects predicate)).length)

theorem Table.updateWhere_schema {table next : Table}
    {assignments : List (Nat × Value)} {predicate : Option Predicate}
    {changes : Nat}
    (success : table.updateWhere assignments predicate = .ok (next, changes)) :
    next.schema = table.schema := by
  unfold Table.updateWhere at success
  cases pointResult : table.pointUpdateRowid? assignments predicate with
  | some rowid =>
    rw [pointResult] at success
    exact Table.patchRowid_schema success
  | none =>
    rw [pointResult] at success
    cases patched : table.patchRows assignments (selects predicate) with
    | error message =>
        rw [patched] at success
        contradiction
    | ok replacement =>
        rw [patched] at success
        have pairEqual := Except.ok.inj success
        have tableEqual : replacement = next := by
          simpa using congrArg Prod.fst pairEqual
        subst next
        exact Table.patchRows_schema patched

theorem Table.updateWhere_exact {table next : Table}
    {assignments : List (Nat × Value)} {predicate : Option Predicate}
    {changes : Nat}
    (success : table.updateWhere assignments predicate = .ok (next, changes)) :
    (∃ rowid,
      table.pointUpdateRowid? assignments predicate = some rowid ∧
      table.patchRowid assignments rowid = .ok (next, changes)) ∨
    (table.pointUpdateRowid? assignments predicate = none ∧
      ∃ rows,
        Core.patchRows table.schema assignments (selects predicate)
          table.rows = .ok rows ∧
        next.rows = rows ∧
        changes = (table.rows.filter (selects predicate)).length) := by
  unfold Table.updateWhere at success
  cases pointResult : table.pointUpdateRowid? assignments predicate with
  | some rowid =>
      rw [pointResult] at success
      exact Or.inl ⟨rowid, rfl, success⟩
  | none =>
      rw [pointResult] at success
      cases patchedRows : Core.patchRows table.schema assignments
          (selects predicate) table.rows with
      | error message =>
          have patchFailed : table.patchRows assignments (selects predicate) =
              .error message := by
            unfold Table.patchRows
            rw [patchedRows]
            rfl
          rw [patchFailed] at success
          contradiction
      | ok rows =>
          cases patched : table.patchRows assignments (selects predicate) with
          | error message =>
              rw [patched] at success
              contradiction
          | ok replacement =>
              rw [patched] at success
              have pairEqual := Except.ok.inj success
              have tableEqual : replacement = next := by
                simpa using congrArg Prod.fst pairEqual
              have changesEqual :
                  (table.rows.filter (selects predicate)).length = changes := by
                simpa using congrArg Prod.snd pairEqual
              subst next
              exact Or.inr ⟨rfl, rows, rfl,
                Table.patchRows_exact patchedRows patched, changesEqual.symm⟩

structure Result where
  rows : List (List Value) := []
  changes : Nat := 0

/-- Check an arbitrary mathematical integer against SQLite's signed 64-bit
INTEGER domain. -/
def checkedInteger (value : Int) : Except String Integer :=
  if lower : -(Int.ofNat FileFormat.IntegerWidth.eight.midpoint) ≤ value then
    if upper : value < Int.ofNat FileFormat.IntegerWidth.eight.midpoint then
      .ok ⟨value, lower, upper⟩
    else .error "integer is above the signed 64-bit range"
  else .error "integer is below the signed 64-bit range"

theorem checkedInteger_exact {value : Int} {integer : Integer}
    (success : checkedInteger value = .ok integer) : integer.value = value := by
  unfold checkedInteger at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  injection success with equal
  subst integer
  rfl

/-- Embed a finite row count in SQLite's signed 64-bit INTEGER domain.  The
guard is executable and the returned bounds are kernel-checked; an impossible
in-memory table larger than `2^63-1` rows is reported rather than wrapped. -/
def countInteger (count : Nat) : Except String Integer :=
  if upper : count < FileFormat.IntegerWidth.eight.midpoint then
    .ok {
      value := Int.ofNat count
      lowerBound := by simp
      upperBound := Int.ofNat_lt.mpr upper }
  else .error "COUNT(*) exceeds the signed 64-bit INTEGER range"

theorem countInteger_exact {count : Nat} {integer : Integer}
    (success : countInteger count = .ok integer) :
    integer.value = Int.ofNat count := by
  unfold countInteger at success
  split at success
  next upper =>
    injection success with equal
    subst integer
    rfl
  next tooLarge => contradiction

inductive CountTarget where
  | star
  | column (index : Nat)
  deriving DecidableEq, Repr

def CountTarget.includes : CountTarget → Row → Bool
  | .star, _ => true
  | .column index, row => row.value index != .null

def countRows (target : CountTarget) (predicate : Option Predicate)
    (rows : List Row) : Nat :=
  (rows.filter (selects predicate)).countP target.includes

theorem countRows_star (predicate : Option Predicate) (rows : List Row) :
    countRows .star predicate rows = (rows.filter (selects predicate)).length := by
  unfold countRows
  induction rows.filter (selects predicate) with
  | nil => rfl
  | cons row rows induction => simp [CountTarget.includes, List.countP_cons, induction]

def addInteger (left right : Integer) : Except String Integer :=
  checkedInteger (left.value + right.value)

theorem addInteger_exact {left right result : Integer}
    (success : addInteger left right = .ok result) :
    result.value = left.value + right.value := by
  exact checkedInteger_exact success

def sumIntegerFrom (accumulator : Integer) :
    List Integer → Except String Integer
  | [] => .ok accumulator
  | value :: values =>
      match addInteger accumulator value with
      | .error message => .error message
      | .ok next => sumIntegerFrom next values

theorem sumIntegerFrom_exact {accumulator result : Integer}
    {values : List Integer}
    (success : sumIntegerFrom accumulator values = .ok result) :
    result.value = accumulator.value + (values.map (·.value)).sum := by
  induction values generalizing accumulator result with
  | nil =>
      simp [sumIntegerFrom] at success
      subst result
      simp
  | cons value values induction =>
      simp only [sumIntegerFrom] at success
      cases added : addInteger accumulator value with
      | error message => simp [added] at success
      | ok next =>
          simp [added] at success
          have tailExact := induction success
          have addExact := addInteger_exact added
          simp only [List.map_cons, List.sum_cons]
          omega

def sumIntegers : List Integer → Except String (Option Integer)
  | [] => .ok none
  | value :: values =>
      match sumIntegerFrom value values with
      | .error message => .error message
      | .ok total => .ok (some total)

theorem sumIntegers_exact {values : List Integer} {result : Integer}
    (success : sumIntegers values = .ok (some result)) :
    result.value = (values.map (·.value)).sum := by
  cases values with
  | nil => simp [sumIntegers] at success
  | cons value values =>
      simp only [sumIntegers] at success
      cases folded : sumIntegerFrom value values with
      | error message => simp [folded] at success
      | ok total =>
          simp [folded] at success
          subst result
          simpa using sumIntegerFrom_exact folded

def columnIntegers (column : Nat) : List Row → Except String (List Integer)
  | [] => .ok []
  | row :: rows =>
      match row.value column with
      | .null => columnIntegers column rows
      | .integer value => (value :: ·) <$> columnIntegers column rows
      | .realBits _ | .text _ | .blob _ =>
          .error "SUM requires INTEGER or NULL values in the verified Core"

/-- The all-integer fast path retains its exact-sum theorem. Mixed storage
classes use the ordered SQLite accumulator, including delayed overflow errors. -/
def sumColumn (column : Nat) (rows : List Row) : Except String Value :=
  match columnIntegers column rows with
  | .error _ => SQLite.AggregateSum.sum (rows.map (·.value column))
  | .ok integers => do
      match ← sumIntegers integers with
      | none => .ok .null
      | some total => .ok (.integer total)

def averageColumn (column : Nat) (rows : List Row) : Value :=
  SQLite.AggregateSum.average (rows.map (·.value column))

def totalColumn (column : Nat) (rows : List Row) : Value :=
  SQLite.AggregateSum.total (rows.map (·.value column))

/-- Select one non-NULL value using SQLite's total storage-class ordering.
`minimum = true` chooses MIN; false chooses MAX. -/
def chooseExtreme (minimum : Bool) (left right : Value) : Value :=
  match left, right with
  | .null, value => value
  | value, .null => value
  | left, right =>
      let order := PhysicalQuery.compareValue left right
      if (minimum && order != .gt) || (!minimum && order != .lt) then left
      else right

theorem chooseExtreme_tie (minimum : Bool) (left right : Value)
    (leftNotNull : left ≠ .null) (rightNotNull : right ≠ .null)
    (equal : PhysicalQuery.compareValue left right = .eq) :
    chooseExtreme minimum left right = left := by
  cases left <;> cases right <;> simp_all [chooseExtreme]
  all_goals cases minimum <;> simp_all

def extremeValues (minimum : Bool) : List Value → Value
  | [] => .null
  | value :: values => chooseExtreme minimum value (extremeValues minimum values)

def extremeColumn (minimum : Bool) (column : Nat) (rows : List Row) : Value :=
  extremeValues minimum (rows.map (fun row => row.value column))

end Core

end SQLeanite
