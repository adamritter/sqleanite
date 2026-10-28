import SQLeanite.Core.Table

namespace SQLeanite
namespace Core
attribute [local instance] lexOrd

def Table.prepareRow (table : Table) (values : List Value) : Except String Row :=
  if values[table.schema.primaryKey]? = some .null then
    match table.nextGeneratedRowid? with
    | some rowid => Row.create table.schema (values.set table.schema.primaryKey (.integer rowid))
    | none => .error "database or disk is full"
  else Row.create table.schema values

def Table.createRow (table : Table) (values : List Value) : Except String Row := do
  let row ← table.prepareRow values
  table.requireChecks row
  return row

theorem Table.createRow_prepared {table : Table} {values : List Value} {row : Row}
    (created : table.createRow values = .ok row) : table.prepareRow values = .ok row := by
  unfold Table.createRow at created
  cases prepared : table.prepareRow values with
  | error message => simp [prepared, bind, Except.bind] at created
  | ok candidate =>
      cases checked : table.requireChecks candidate with
      | error message => simp [prepared, checked, bind, Except.bind] at created
      | ok unit =>
          simp [prepared, checked, bind, Except.bind, pure, Except.pure] at created
          subst row
          rfl

theorem Table.createRow_checks {table : Table} {values : List Value} {row : Row}
    (created : table.createRow values = .ok row) : table.requireChecks row = .ok () := by
  unfold Table.createRow at created
  cases prepared : table.prepareRow values with
  | error message => simp [prepared, bind, Except.bind] at created
  | ok candidate =>
      cases checked : table.requireChecks candidate with
      | error message => simp [prepared, checked, bind, Except.bind] at created
      | ok unit =>
          cases unit
          simp [prepared, checked, bind, Except.bind, pure, Except.pure] at created
          subst row
          exact checked

theorem Table.createRow_generated {table : Table} {values : List Value}
    {row : Row} (automatic : values[table.schema.primaryKey]? = some .null)
    (created : table.createRow values = .ok row) :
    ∃ rowid, table.nextGeneratedRowid? = some rowid ∧ row.rowid = rowid := by
  have created := Table.createRow_prepared created
  unfold Table.prepareRow at created
  rw [if_pos automatic] at created
  cases generated : table.nextGeneratedRowid? with
  | none => simp [generated] at created
  | some rowid =>
      rw [generated] at created
      exact ⟨rowid, rfl, Row.create_set_rowid created⟩

def Table.findDeclaredPrimary? (table : Table) (row : Row) : Option Row :=
  if table.schema.hasHiddenRowid then
    table.declaredKeyMap.get? (row.declaredKey table.schema)
  else none

/-- The balanced declared-primary-key lookup is exactly the old logical row
search.  This is the completeness theorem which permits the live INSERT path
to replace an O(n) scan with O(log n) routing. -/
theorem Table.findDeclaredPrimary?_exact (table : Table) (row : Row)
    (hidden : table.schema.hasHiddenRowid = true) :
    table.findDeclaredPrimary? row = table.rows.find? (fun existing =>
      existing.declaredKey table.schema == row.declaredKey table.schema) := by
  unfold Table.findDeclaredPrimary?
  rw [if_pos hidden]
  exact table.declaredKeyMapRepresents hidden (row.declaredKey table.schema)

def Table.createReplacementRow (table : Table) (values : List Value) :
    Except String Row := do
  let candidate ← table.createRow values
  match table.findDeclaredPrimary? candidate with
  | some existing => Row.createWithRowid table.schema existing.rowid values
  | none => pure candidate

theorem Row.create_wellFormed {schema : Schema} {values : List Value} {row : Row}
    (success : Row.create schema values = .ok row) : row.WellFormed schema := by
  unfold Row.create at success
  cases present : values[schema.primaryKey]? with
  | none => simp [present] at success
  | some value =>
      cases value with
      | null => simp [present] at success
      | realBits bits => simp [present] at success
      | text text => simp [present] at success
      | blob blob => simp [present] at success
      | integer integer =>
          simp only [present] at success
          split at success
          next valid =>
            injection success with equal
            subst row
            exact valid
          next invalid => contradiction

theorem Row.create_self (schema : Schema) (row : Row)
    (valid : row.WellFormed schema) :
    Row.create schema row.values = .ok row := by
  unfold Row.create
  rw [valid.2.1]
  simp only
  rw [if_pos valid]

def orderedUpsert (row : Row) : List Row → List Row
  | [] => [row]
  | existing :: rows =>
      if row.rowid.value < existing.rowid.value then row :: existing :: rows
      else if existing.rowid.value < row.rowid.value then
        existing :: orderedUpsert row rows
      else row :: rows

theorem orderedUpsert_eq_append_of_afterAll (row : Row) :
    ∀ (rows : List Row),
      (∀ existing ∈ rows, existing.rowid.value < row.rowid.value) →
      orderedUpsert row rows = rows ++ [row]
  | [], _ => rfl
  | existing :: rows, afterAll => by
      have existingBefore : existing.rowid.value < row.rowid.value :=
        afterAll existing (by simp)
      have rowNotBefore : ¬row.rowid.value < existing.rowid.value := by omega
      simp only [orderedUpsert, if_neg rowNotBefore, if_pos existingBefore,
        List.cons_append, List.cons.injEq, true_and]
      exact orderedUpsert_eq_append_of_afterAll row rows fun candidate member =>
        afterAll candidate (by simp [member])

theorem orderedInsert_treeEntries (row : Row) (rows : List Row) :
    PagedBTree.orderedInsert row.treeKey row (treeEntries rows) =
      treeEntries (orderedUpsert row rows) := by
  induction rows with
  | nil => rfl
  | cons existing rows induction =>
      by_cases before : row.rowid.value < existing.rowid.value
      · have keyBefore : row.treeKey < existing.treeKey :=
          (Row.treeKey_lt_iff row existing).2 before
        simp [treeEntries, orderedUpsert, PagedBTree.orderedInsert,
          before, keyBefore]
      · have keyNotBefore : ¬row.treeKey < existing.treeKey := by
          simpa [Row.treeKey_lt_iff] using before
        by_cases after : existing.rowid.value < row.rowid.value
        · have keyAfter : existing.treeKey < row.treeKey :=
            (Row.treeKey_lt_iff existing row).2 after
          simp only [treeEntries, List.map_cons, orderedUpsert,
            PagedBTree.orderedInsert, if_neg before, if_pos after,
            if_neg keyNotBefore, if_pos keyAfter]
          simpa only [treeEntries] using
            congrArg ((existing.treeKey, existing) :: ·) induction
        · have keyNotAfter : ¬existing.treeKey < row.treeKey := by
            simpa [Row.treeKey_lt_iff] using after
          simp [treeEntries, orderedUpsert, PagedBTree.orderedInsert,
            before, after, keyNotBefore, keyNotAfter]

/-- Tail-recursive companion to `orderedUpsert`.

`orderedUpsert` rebuilds the prefix with `existing :: orderedUpsert row rows`,
so inserting an ascending rowid recurses to the end of the table and the stack
depth equals the row count. That exhausted the stack at roughly 60,000 rows and
dumped core instead of failing cleanly. This version carries the prefix in a
reversed accumulator and is proved equal below, so the clean definition is what
every proof still sees while the compiler runs this one. -/
def orderedUpsertGo (row : Row) : List Row → List Row → List Row
  | [], acc => acc.reverseAux [row]
  | existing :: rows, acc =>
      if row.rowid.value < existing.rowid.value then
        acc.reverseAux (row :: existing :: rows)
      else if existing.rowid.value < row.rowid.value then
        orderedUpsertGo row rows (existing :: acc)
      else acc.reverseAux (row :: rows)

def orderedUpsertTR (row : Row) (rows : List Row) : List Row :=
  orderedUpsertGo row rows []

theorem orderedUpsertGo_eq (row : Row) :
    (rows acc : List Row) →
      orderedUpsertGo row rows acc = acc.reverse ++ orderedUpsert row rows
  | [], acc => by simp [orderedUpsertGo, orderedUpsert, List.reverseAux_eq]
  | existing :: rows, acc => by
      unfold orderedUpsertGo orderedUpsert
      split
      · simp [List.reverseAux_eq]
      · split
        · rw [orderedUpsertGo_eq row rows (existing :: acc)]
          simp
        · simp [List.reverseAux_eq]

@[csimp] theorem orderedUpsert_eq_orderedUpsertTR :
    @orderedUpsert = @orderedUpsertTR := by
  funext row rows
  rw [orderedUpsertTR, orderedUpsertGo_eq]
  simp

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

/-- The inserted row is present.  `mem_orderedUpsert` is the forward direction --
nothing appears from nowhere -- and this is its converse half, which is what a
caller actually wants to know about an insert. -/
theorem mem_orderedUpsert_self (row : Row) :
    ∀ rows : List Row, row ∈ orderedUpsert row rows
  | [] => by simp [orderedUpsert]
  | existing :: rows => by
      rw [orderedUpsert]
      split
      · exact List.mem_cons_self
      · split
        · exact List.mem_cons_of_mem existing (mem_orderedUpsert_self row rows)
        · exact List.mem_cons_self

/-- Rows the insert does not collide with are retained.  Stated with the rowid
inequality rather than row disequality: an insert replaces by *key*, so a
different row carrying the same rowid is exactly what does not survive. -/
theorem mem_orderedUpsert_of_mem {row : Row} :
    ∀ {candidate : Row} {rows : List Row}, candidate ∈ rows →
      candidate.rowid.value ≠ row.rowid.value →
      candidate ∈ orderedUpsert row rows
  | candidate, existing :: rows, member, different => by
      rw [orderedUpsert]
      split
      · exact List.mem_cons_of_mem row member
      · split
        next existingLess =>
          rcases List.mem_cons.mp member with equal | tail
          · exact equal ▸ List.mem_cons_self
          · exact List.mem_cons_of_mem existing
              (mem_orderedUpsert_of_mem tail different)
        next existingNotLess =>
          have same : existing.rowid.value = row.rowid.value := by omega
          rcases List.mem_cons.mp member with equal | tail
          · exact absurd (by rw [equal]; exact same) different
          · exact List.mem_cons_of_mem row tail

/-- The ordered insert as a multiset: exactly the inserted row together with the
rows it did not displace.  Sortedness is not decoration -- with two rows sharing a
rowid, `orderedUpsert` replaces only the first and the permutation is false. -/
theorem orderedUpsert_perm (row : Row) :
    ∀ rows : List Row, rows.Pairwise Row.keyLess →
      (orderedUpsert row rows).Perm
        (row :: rows.filter (fun candidate =>
          candidate.rowid.value != row.rowid.value))
  | [], _ => by simp [orderedUpsert]
  | existing :: rows, sorted => by
      simp only [List.pairwise_cons] at sorted
      rw [orderedUpsert]
      split
      next rowLess =>
        have keepExisting : (existing.rowid.value != row.rowid.value) = true := by
          simp; omega
        have keepRest : rows.filter (fun candidate =>
            candidate.rowid.value != row.rowid.value) = rows := by
          apply List.filter_eq_self.mpr
          intro candidate member
          have larger : existing.rowid.value < candidate.rowid.value :=
            sorted.1 candidate member
          simp; omega
        simp only [List.filter_cons, keepExisting, if_pos, keepRest]
        exact List.Perm.refl _
      next rowNotLess =>
        split
        next existingLess =>
          have keepExisting : (existing.rowid.value != row.rowid.value) = true := by
            simp; omega
          simp only [List.filter_cons, keepExisting, if_pos]
          exact ((orderedUpsert_perm row rows sorted.2).cons existing).trans
            (List.Perm.swap _ _ _)
        next existingNotLess =>
          have same : existing.rowid.value = row.rowid.value := by omega
          have dropExisting :
              (existing.rowid.value != row.rowid.value) = false := by
            simp [same]
          have keepRest : rows.filter (fun candidate =>
              candidate.rowid.value != row.rowid.value) = rows := by
            apply List.filter_eq_self.mpr
            intro candidate member
            have larger : existing.rowid.value < candidate.rowid.value :=
              sorted.1 candidate member
            simp; omega
          simp only [List.filter_cons, dropExisting, if_neg, keepRest,
            Bool.false_eq_true]
          exact List.Perm.refl _

/-- Membership after an insert, characterized exactly. -/
theorem mem_orderedUpsert_iff {row candidate : Row} {rows : List Row}
    (sorted : rows.Pairwise Row.keyLess) :
    candidate ∈ orderedUpsert row rows ↔
      candidate = row ∨
        (candidate ∈ rows ∧ candidate.rowid.value ≠ row.rowid.value) := by
  constructor
  · intro membership
    rcases mem_orderedUpsert membership with isRow | inRows
    · exact .inl isRow
    · by_cases collides : candidate.rowid.value = row.rowid.value
      · -- A colliding row cannot survive: the permutation drops it, and
        -- sortedness makes it the only one with that rowid.
        left
        have permuted := orderedUpsert_perm row rows sorted
        have notInFiltered : candidate ∉ rows.filter (fun other =>
            other.rowid.value != row.rowid.value) := by
          intro filtered
          have passes := (List.mem_filter.mp filtered).2
          simp [collides] at passes
        have := permuted.mem_iff.mp membership
        simp only [List.mem_cons] at this
        rcases this with equal | filtered
        · exact equal
        · exact absurd filtered notInFiltered
      · exact .inr ⟨inRows, collides⟩
  · intro source
    rcases source with equal | ⟨member, different⟩
    · exact equal ▸ mem_orderedUpsert_self row rows
    · exact mem_orderedUpsert_of_mem member different

/-- A fresh insert adds exactly one row. -/
theorem length_orderedUpsert_of_fresh (row : Row) (rows : List Row)
    (sorted : rows.Pairwise Row.keyLess)
    (fresh : ∀ existing ∈ rows, existing.rowid.value ≠ row.rowid.value) :
    (orderedUpsert row rows).length = rows.length + 1 := by
  have permuted := orderedUpsert_perm row rows sorted
  have kept : rows.filter (fun candidate =>
      candidate.rowid.value != row.rowid.value) = rows := by
    apply List.filter_eq_self.mpr
    intro candidate member
    simp [fresh candidate member]
  rw [permuted.length_eq, kept, List.length_cons]

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

theorem storedRows_insert (tree : PersistentPageTree.Store Row)
    (wellKeyed : RowTreeWellKeyed tree) (row : Row) :
    storedRows (tree.insert row.treeKey row) =
      orderedUpsert row (storedRows tree) := by
  unfold storedRows
  rw [PersistentPageTree.Store.insert_toList, wellKeyed,
    orderedInsert_treeEntries]
  simp [treeEntries, List.map_map, Function.comp_def]

theorem rowTreeWellKeyed_insert (tree : PersistentPageTree.Store Row)
    (wellKeyed : RowTreeWellKeyed tree) (row : Row) :
    RowTreeWellKeyed (tree.insert row.treeKey row) := by
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at wellKeyed
  rw [PersistentPageTree.Store.insert_toList, wellKeyed,
    orderedInsert_treeEntries, storedRows_insert tree wellKeyed row]

theorem Table.declaredKeyMap_insert_represents_append (table : Table)
    (row : Row) (hidden : table.schema.hasHiddenRowid = true)
    (fresh : table.declaredKeyMap.get? (row.declaredKey table.schema) = none) :
    DeclaredKeyMapRepresents table.schema (table.rows ++ [row])
      (table.declaredKeyMap.insert (row.declaredKey table.schema) row) := by
  intro _ target
  change (table.declaredKeyMap.insert
    (row.declaredKey table.schema) row)[target]? = _
  rw [Std.TreeMap.getElem?_insert]
  simp only [DeclaredKey.compareOn_orderKey_eq]
  rw [List.find?_append]
  have represented := table.declaredKeyMapRepresents hidden target
  have keyAbsent := table.declaredKeyMapRepresents hidden
    (row.declaredKey table.schema)
  rw [fresh] at keyAbsent
  change table.declaredKeyMap[target]? =
    table.rows.find? (fun row => row.declaredKey table.schema == target)
    at represented
  have oldNone : table.rows.find? (fun existing =>
      existing.declaredKey table.schema == row.declaredKey table.schema) =
      none := by
    simpa only [Table.rows] using keyAbsent.symm
  by_cases same : row.declaredKey table.schema = target
  · subst target
    rw [if_pos rfl, oldNone]
    simp
  · rw [if_neg same, represented]
    simp [same]

theorem find?_orderedUpsert_of_false (inserted : Row) (rows : List Row)
    (predicate : Row → Bool) (insertedFalse : predicate inserted = false)
    (freshRowid : ∀ existing ∈ rows,
      existing.rowid.value ≠ inserted.rowid.value) :
    (orderedUpsert inserted rows).find? predicate = rows.find? predicate := by
  induction rows with
  | nil => simp [orderedUpsert, insertedFalse]
  | cons head tail induction =>
      have headFresh := freshRowid head (by simp)
      have tailFresh : ∀ existing ∈ tail,
          existing.rowid.value ≠ inserted.rowid.value := by
        intro existing member
        exact freshRowid existing (by simp [member])
      by_cases before : inserted.rowid.value < head.rowid.value
      · simp [orderedUpsert, before, insertedFalse]
      · by_cases after : head.rowid.value < inserted.rowid.value
        · rw [show orderedUpsert inserted (head :: tail) =
              head :: orderedUpsert inserted tail by
                simp [orderedUpsert, before, after]]
          cases headResult : predicate head
          · simp [headResult, induction tailFresh]
          · simp [headResult]
        · have equal : head.rowid.value = inserted.rowid.value := by omega
          exact False.elim (headFresh equal)

end Core

end SQLeanite
