import SQLeanite.PhysicalCodec
import SQLeanite.PagedBTree

namespace SQLeanite.PhysicalCodec

/-!
# Correct-by-construction operations for the restricted table

Every operation re-enters `Database` only through a checked page-fit boundary.
Sorted rowids are constructed by proof, while an overfull one-page MVP table is
an executable error rather than an unproved assumption.
-/

def Database.rebuild (rows : List Row) (sorted : rows.Pairwise Row.keyLess) :
    Except String Database :=
  if fits : PageFit 0 (rows.map Row.encodeCell) then
    .ok { rows := rows, rowidsSorted := sorted, pageFits := fits }
  else
    .error "MVP table leaf page is full"

theorem Database.rebuild_rows {rows : List Row} {sorted : rows.Pairwise Row.keyLess}
    {database : Database} (success : Database.rebuild rows sorted = .ok database) :
    database.rows = rows := by
  simp only [Database.rebuild] at success
  split at success
  · simpa using congrArg (fun result => result.rows) (Except.ok.inj success.symm)
  · contradiction

/-- Sorted insertion with SQLite REPLACE semantics at an existing rowid. -/
def orderedUpsert (row : Row) : List Row → List Row
  | [] => [row]
  | existing :: rows =>
      if row.rowid.value < existing.rowid.value then row :: existing :: rows
      else if existing.rowid.value < row.rowid.value then
        existing :: orderedUpsert row rows
      else row :: rows

/-- Bias a signed 64-bit rowid into the natural-key space used by the verified
paged B+tree. -/
def Row.treeKey (row : Row) : Nat :=
  (row.rowid.value + Int.ofNat FileFormat.IntegerWidth.eight.midpoint).toNat

theorem Row.treeKey_int (row : Row) :
    Int.ofNat row.treeKey =
      row.rowid.value + Int.ofNat FileFormat.IntegerWidth.eight.midpoint := by
  unfold Row.treeKey
  exact Int.toNat_of_nonneg (by
    have lower := row.rowid.lowerBound
    omega)

theorem Row.treeKey_lt_iff (left right : Row) :
    left.treeKey < right.treeKey ↔ left.rowid.value < right.rowid.value := by
  constructor
  · intro less
    have coerced : Int.ofNat left.treeKey < Int.ofNat right.treeKey :=
      Int.ofNat_lt.mpr less
    rw [left.treeKey_int, right.treeKey_int] at coerced
    omega
  · intro less
    apply Int.ofNat_lt.mp
    change Int.ofNat left.treeKey < Int.ofNat right.treeKey
    rw [left.treeKey_int, right.treeKey_int]
    omega

theorem Row.treeKey_eq_iff (left right : Row) :
    left.treeKey = right.treeKey ↔ left.rowid.value = right.rowid.value := by
  constructor
  · intro equal
    have coerced := congrArg Int.ofNat equal
    rw [left.treeKey_int, right.treeKey_int] at coerced
    omega
  · intro equal
    unfold Row.treeKey
    rw [equal]

def treeEntries (rows : List Row) : List (PagedBTree.Entry Row) :=
  rows.map fun row => (row.treeKey, row)

theorem map_orderedInsert_treeEntries (row : Row) (rows : List Row) :
    (PagedBTree.orderedInsert row.treeKey row (treeEntries rows)).map (·.2) =
      orderedUpsert row rows := by
  induction rows with
  | nil => rfl
  | cons existing rows induction =>
      by_cases before : row.rowid.value < existing.rowid.value
      · have keyBefore : row.treeKey < existing.treeKey :=
          (Row.treeKey_lt_iff row existing).2 before
        simp only [treeEntries, List.map_cons, PagedBTree.orderedInsert,
          orderedUpsert, if_pos before, if_pos keyBefore, Prod.snd]
        simp [treeEntries, Function.comp_def]
      · have keyNotBefore : ¬row.treeKey < existing.treeKey := by
          simpa [Row.treeKey_lt_iff] using before
        by_cases after : existing.rowid.value < row.rowid.value
        · have keyAfter : existing.treeKey < row.treeKey :=
            (Row.treeKey_lt_iff existing row).2 after
          simp only [treeEntries, List.map_cons, PagedBTree.orderedInsert,
            orderedUpsert, if_neg before, if_pos after, if_neg keyNotBefore,
            if_pos keyAfter, Prod.snd]
          simpa only [treeEntries] using congrArg (existing :: ·) induction
        · have keyNotAfter : ¬existing.treeKey < row.treeKey := by
            simpa [Row.treeKey_lt_iff] using after
          simp only [treeEntries, List.map_cons, PagedBTree.orderedInsert,
            orderedUpsert, if_neg before, if_neg after, if_neg keyNotBefore,
            if_neg keyNotAfter, Prod.snd]
          simp [treeEntries, Function.comp_def]

def Database.tree (database : Database) : PagedBTree.Tree Row :=
  PagedBTree.Tree.ofList (treeEntries database.rows)

theorem Database.tree_toList (database : Database) :
    database.tree.toList = treeEntries database.rows := by
  exact PagedBTree.Tree.toList_ofList _

theorem Database.tree_insert_rows (database : Database) (row : Row) :
    (database.tree.insert row.treeKey row).toList.map (·.2) =
      orderedUpsert row database.rows := by
  rw [PagedBTree.Tree.toList_insert, database.tree_toList]
  exact map_orderedInsert_treeEntries row database.rows

theorem Database.tree_delete_rows (database : Database) (target : Row) :
    (database.tree.delete target.treeKey).toList.map (·.2) =
      database.rows.filter (fun row => row.rowid.value != target.rowid.value) := by
  rw [PagedBTree.Tree.toList_delete, database.tree_toList]
  induction database.rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [treeEntries, List.map_cons, List.filter_cons, Prod.fst, Prod.snd]
      by_cases equal : row.rowid.value = target.rowid.value
      · have keyEqual : row.treeKey = target.treeKey :=
          (Row.treeKey_eq_iff row target).2 equal
        have leftFalse : decide (row.treeKey ≠ target.treeKey) = false := by
          simp [keyEqual]
        have rightFalse : (row.rowid.value != target.rowid.value) = false := by
          simp [equal]
        rw [leftFalse, rightFalse]
        simpa only [treeEntries, Bool.false_eq_true, ↓reduceIte] using induction
      · have keyNotEqual : row.treeKey ≠ target.treeKey := fun keyEqual =>
          equal ((Row.treeKey_eq_iff row target).1 keyEqual)
        have leftTrue : decide (row.treeKey ≠ target.treeKey) = true := by
          simp [keyNotEqual]
        have rightTrue : (row.rowid.value != target.rowid.value) = true := by
          simp [equal]
        rw [leftTrue, rightTrue]
        exact congrArg (row :: ·) (by simpa only [treeEntries, Bool.false_eq_true, ↓reduceIte] using induction)

theorem mem_orderedUpsert {row candidate : Row} {rows : List Row}
    (membership : candidate ∈ orderedUpsert row rows) :
    candidate = row ∨ candidate ∈ rows := by
  induction rows with
  | nil => simpa [orderedUpsert] using membership
  | cons existing rows induction =>
      simp only [orderedUpsert] at membership
      split at membership
      · simp only [List.mem_cons] at membership
        rcases membership with equal | equal | member
        · exact .inl equal
        · exact .inr (by simp [equal])
        · exact .inr (.tail existing member)
      · split at membership
        · simp only [List.mem_cons] at membership
          rcases membership with equal | member
          · exact .inr (by simp [equal])
          · exact (induction member).imp id (List.Mem.tail existing)
        · simp only [List.mem_cons] at membership
          rcases membership with equal | member
          · exact .inl equal
          · exact .inr (.tail existing member)

theorem orderedUpsert_sorted (row : Row) (rows : List Row)
    (sorted : rows.Pairwise Row.keyLess) :
    (orderedUpsert row rows).Pairwise Row.keyLess := by
  induction rows with
  | nil => simp [orderedUpsert, Row.keyLess]
  | cons existing rows induction =>
      simp only [List.pairwise_cons] at sorted
      simp only [orderedUpsert]
      split
      next rowLess =>
        simp only [List.pairwise_cons]
        refine ⟨?_, sorted⟩
        intro candidate member
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · simpa [Row.keyLess, equal] using rowLess
        · exact Int.lt_trans rowLess (sorted.1 candidate member)
      next rowNotLess =>
        split
        next existingLess =>
          simp only [List.pairwise_cons]
          refine ⟨?_, induction sorted.2⟩
          intro candidate member
          rcases mem_orderedUpsert member with equal | old
          · simpa [Row.keyLess, equal] using existingLess
          · exact sorted.1 candidate old
        next existingNotLess =>
          have equal : row.rowid.value = existing.rowid.value := by omega
          simp only [List.pairwise_cons]
          refine ⟨?_, sorted.2⟩
          intro candidate member
          change row.rowid.value < candidate.rowid.value
          rw [equal]
          exact sorted.1 candidate member

/-- Insert or replace a row at any signed 64-bit rowid. -/
def Database.upsertChecked (database : Database) (row : Row) : Except String Database :=
  Database.rebuild ((database.tree.insert row.treeKey row).toList.map (·.2)) (by
    rw [Database.tree_insert_rows]
    exact orderedUpsert_sorted row database.rows database.rowidsSorted)

theorem Database.upsertChecked_rows {database next : Database} {row : Row}
    (success : database.upsertChecked row = .ok next) :
    next.rows = orderedUpsert row database.rows := by
  unfold Database.upsertChecked at success
  rw [Database.rebuild_rows success]
  exact Database.tree_insert_rows database row

def Database.findRow? (database : Database) (rowid : Int) : Option Row :=
  database.rows.find? (fun row => row.rowid.value == rowid)

/-- Ordered primary-key lookup stops as soon as the sought key is smaller than
the current row. -/
def lookupSorted (rowid : Int) : List Row → List Row
  | [] => []
  | row :: rows =>
      if row.rowid.value < rowid then lookupSorted rowid rows
      else if rowid < row.rowid.value then []
      else [row]

theorem lookupSorted_eq_filter (rowid : Int) (rows : List Row)
    (sorted : rows.Pairwise Row.keyLess) :
    lookupSorted rowid rows = rows.filter (fun row => row.rowid.value == rowid) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.pairwise_cons] at sorted
      by_cases before : row.rowid.value < rowid
      · have different : ¬row.rowid.value = rowid := by omega
        simp [lookupSorted, before, different, induction sorted.2]
      · by_cases after : rowid < row.rowid.value
        · have different : ¬row.rowid.value = rowid := by omega
          have tailEmpty : rows.filter (fun candidate =>
              candidate.rowid.value == rowid) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro candidate member
            have ordered := sorted.1 candidate member
            change row.rowid.value < candidate.rowid.value at ordered
            have different : candidate.rowid.value ≠ rowid := by omega
            simp [different]
          simp [lookupSorted, before, after, different, tailEmpty]
        · have equal : row.rowid.value = rowid := by omega
          have tailEmpty : rows.filter (fun candidate =>
              candidate.rowid.value == rowid) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro candidate member
            have ordered := sorted.1 candidate member
            change row.rowid.value < candidate.rowid.value at ordered
            have different : candidate.rowid.value ≠ rowid := by omega
            simp [different]
          simp [lookupSorted, before, after, equal, tailEmpty]

def Database.lookupRowid (database : Database) (rowid : Int) : List Row :=
  lookupSorted rowid database.rows

theorem Database.lookupRowid_eq_filter (database : Database) (rowid : Int) :
    database.lookupRowid rowid =
      database.rows.filter (fun row => row.rowid.value == rowid) :=
  lookupSorted_eq_filter rowid database.rows database.rowidsSorted

theorem Database.findRow?_some_mem {database : Database} {rowid : Int} {row : Row}
    (found : database.findRow? rowid = some row) : row ∈ database.rows := by
  unfold Database.findRow? at found
  exact List.mem_of_find?_eq_some found

/-- Ordinary INSERT rejects an existing primary key and otherwise uses the
same arbitrary-order verified insertion as REPLACE. -/
def Database.insertChecked (database : Database) (row : Row) : Except String Database :=
  match database.findRow? row.rowid.value with
  | some _ => .error "UNIQUE constraint failed: items.id"
  | none => database.upsertChecked row

theorem Database.insertChecked_rows {database next : Database} {row : Row}
    (success : database.insertChecked row = .ok next) :
    next.rows = orderedUpsert row database.rows := by
  unfold Database.insertChecked at success
  split at success
  · contradiction
  · exact Database.upsertChecked_rows success

/-- Execute all rows of one INSERT statement atomically at the pure boundary.
An error returns no intermediate database to the caller. -/
def Database.applyMany (operation : Database → Row → Except String Database) :
    Database → List Row → Except String Database
  | database, [] => .ok database
  | database, row :: rows =>
      match operation database row with
      | .error message => .error message
      | .ok next => Database.applyMany operation next rows

theorem Database.applyMany_rows
    (operation : Database → Row → Except String Database)
    (operationRows : ∀ {database next row}, operation database row = .ok next →
      next.rows = orderedUpsert row database.rows)
    {database next : Database} {rows : List Row}
    (success : Database.applyMany operation database rows = .ok next) :
    next.rows = rows.foldl (fun stored row => orderedUpsert row stored) database.rows := by
  induction rows generalizing database next with
  | nil =>
      simp [Database.applyMany] at success
      subst next
      rfl
  | cons row rows induction =>
      unfold Database.applyMany at success
      cases inserted : operation database row with
      | error message => simp [inserted] at success
      | ok middle =>
          rw [inserted] at success
          rw [induction success, operationRows inserted]
          rfl

def Database.insertMany (database : Database) (rows : List Row) :
    Except String Database :=
  Database.applyMany Database.insertChecked database rows

theorem Database.insertMany_rows {database next : Database} {rows : List Row}
    (success : database.insertMany rows = .ok next) :
    next.rows = rows.foldl (fun stored row => orderedUpsert row stored) database.rows := by
  exact Database.applyMany_rows Database.insertChecked
    Database.insertChecked_rows success

def Database.upsertMany (database : Database) (rows : List Row) :
    Except String Database :=
  Database.applyMany Database.upsertChecked database rows

theorem Database.upsertMany_rows {database next : Database} {rows : List Row}
    (success : database.upsertMany rows = .ok next) :
    next.rows = rows.foldl (fun stored row => orderedUpsert row stored) database.rows := by
  exact Database.applyMany_rows Database.upsertChecked
    Database.upsertChecked_rows success

/-- Append is the fast path used by monotonically allocated rowids.  It rejects
duplicates and out-of-order keys rather than weakening the sorted invariant. -/
def Database.appendChecked (database : Database) (row : Row) : Except String Database :=
  if ordered : ∀ existing ∈ database.rows, Row.keyLess existing row then
    Database.rebuild (database.rows ++ [row]) (by
      rw [List.pairwise_append]
      exact ⟨database.rowidsSorted, by simp, by
        intro existing membership candidate candidateMembership
        simp only [List.mem_singleton] at candidateMembership
        subst candidate
        exact ordered existing membership⟩)
  else
    .error "MVP rowid is duplicate or out of order"

theorem Database.appendChecked_rows {database next : Database} {row : Row}
    (success : database.appendChecked row = .ok next) :
    next.rows = database.rows ++ [row] := by
  simp only [Database.appendChecked] at success
  split at success
  · exact Database.rebuild_rows success
  · contradiction

/-- Delete all rows with the selected INTEGER PRIMARY KEY.  Strict ordering
means there is at most one such row. -/
def Database.deleteRowid (database : Database) (rowid : Int) : Except String Database :=
  match found : database.findRow? rowid with
  | none => .ok database
  | some target =>
      Database.rebuild ((database.tree.delete target.treeKey).toList.map (·.2)) (by
        rw [Database.tree_delete_rows]
        exact database.rowidsSorted.filter _)

theorem Database.deleteRowid_rows {database next : Database} {rowid : Int}
    (success : database.deleteRowid rowid = .ok next) :
    next.rows = database.rows.filter (fun row => row.rowid.value != rowid) := by
  unfold Database.deleteRowid at success
  split at success
  next found =>
    simp only [Except.ok.injEq] at success
    subst next
    apply (List.filter_eq_self.mpr ?_).symm
    intro row member
    have absent := (List.find?_eq_none.mp found) row member
    simp [Database.findRow?] at found
    simp_all
  next target found =>
    have targetKey : target.rowid.value = rowid := by
      have selected := (List.find?_eq_some_iff_append.mp found).1
      simpa using selected
    rw [Database.rebuild_rows success, database.tree_delete_rows, targetKey]

def Row.replacePayload (row : Row) (rowid : Int) (first second : Value) : Row :=
  if row.rowid.value = rowid then { row with first := first, second := second }
  else row

theorem Row.replacePayload_rowid (row : Row) (rowid : Int) (first second : Value) :
    (row.replacePayload rowid first second).rowid = row.rowid := by
  unfold Row.replacePayload
  split <;> rfl

/-- Update payload columns without changing the rowid ordering key. -/
def Database.updatePayload (database : Database) (rowid : Int)
    (first second : Value) : Except String Database :=
  let rows := database.rows.map (fun row => row.replacePayload rowid first second)
  Database.rebuild rows (database.rowidsSorted.map _ (by
    intro left right ordered
    simpa [Row.keyLess, Row.replacePayload_rowid] using ordered))

theorem Database.updatePayload_rows {database next : Database} {rowid : Int}
    {first second : Value}
    (success : database.updatePayload rowid first second = .ok next) :
    next.rows = database.rows.map (fun row => row.replacePayload rowid first second) := by
  unfold Database.updatePayload at success
  exact Database.rebuild_rows success

/-- Update only the selected payload columns.  `none` means that the old field
is retained; `some .null` remains distinguishable from an omitted assignment. -/
def Row.patchPayload (row : Row) (rowid : Int)
    (first second : Option Value) : Row :=
  if row.rowid.value = rowid then
    { row with first := first.getD row.first, second := second.getD row.second }
  else row

theorem Row.patchPayload_rowid (row : Row) (rowid : Int)
    (first second : Option Value) :
    (row.patchPayload rowid first second).rowid = row.rowid := by
  unfold Row.patchPayload
  split <;> rfl

def Database.patchPayload (database : Database) (rowid : Int)
    (first second : Option Value) : Except String Database :=
  let rows := database.rows.map (fun row => row.patchPayload rowid first second)
  Database.rebuild rows (database.rowidsSorted.map _ (by
    intro left right ordered
    simpa [Row.keyLess, Row.patchPayload_rowid] using ordered))

theorem Database.patchPayload_rows {database next : Database} {rowid : Int}
    {first second : Option Value}
    (success : database.patchPayload rowid first second = .ok next) :
    next.rows = database.rows.map (fun row => row.patchPayload rowid first second) := by
  unfold Database.patchPayload at success
  exact Database.rebuild_rows success

def Row.patchSelected (row : Row) (selected : Bool)
    (first second : Option Value) : Row :=
  if selected then
    { row with first := first.getD row.first, second := second.getD row.second }
  else row

theorem Row.patchSelected_rowid (row : Row) (selected : Bool)
    (first second : Option Value) :
    (row.patchSelected selected first second).rowid = row.rowid := by
  unfold Row.patchSelected
  split <;> rfl

/-- Apply a payload patch to exactly the rows selected by an executable
predicate.  The selection function cannot alter ordering keys. -/
def Database.patchSelected (database : Database) (selected : Row → Bool)
    (first second : Option Value) : Except String Database :=
  let rows := database.rows.map
    (fun row => row.patchSelected (selected row) first second)
  Database.rebuild rows (database.rowidsSorted.map _ (by
    intro left right ordered
    simpa [Row.keyLess, Row.patchSelected_rowid] using ordered))

theorem Database.patchSelected_rows {database next : Database}
    {selected : Row → Bool} {first second : Option Value}
    (success : database.patchSelected selected first second = .ok next) :
    next.rows = database.rows.map
      (fun row => row.patchSelected (selected row) first second) := by
  unfold Database.patchSelected at success
  exact Database.rebuild_rows success

/-- Delete exactly the rows for which `retained` is false. -/
def Database.retainRows (database : Database) (retained : Row → Bool) :
    Except String Database :=
  Database.rebuild (database.rows.filter retained)
    (database.rowidsSorted.filter retained)

theorem Database.retainRows_rows {database next : Database}
    {retained : Row → Bool}
    (success : database.retainRows retained = .ok next) :
    next.rows = database.rows.filter retained := by
  unfold Database.retainRows at success
  exact Database.rebuild_rows success

end SQLeanite.PhysicalCodec
