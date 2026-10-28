import SQLeanite.Core.TableReplaceValues

namespace SQLeanite
namespace Core
attribute [local instance] lexOrd

theorem Table.upsertDifferences?_schema (table : Table) :
    ∀ (old rows : List Row) (next : Table),
      table.upsertDifferences? old rows = some next →
      next.schema = table.schema
  | [], [], next, success => by
      simp only [Table.upsertDifferences?, Option.some.injEq] at success
      subst next
      rfl
  | [], _ :: _, _, success => by simp [Table.upsertDifferences?] at success
  | _ :: _, [], _, success => by simp [Table.upsertDifferences?] at success
  | old :: olds, row :: rows, next, success => by
      unfold Table.upsertDifferences? at success
      split at success
      next same =>
        exact Table.upsertDifferences?_schema table olds rows next success
      next different =>
        split at success
        next sameRowid =>
          split at success
          next valid =>
            have tail := Table.upsertDifferences?_schema (table.upsert row valid)
              olds rows next success
            exact tail
          next => contradiction
        next => contradiction

theorem Table.withPatchedRows_schema {table next : Table} {rows : List Row}
    (success : table.withPatchedRows rows = .ok next) :
    next.schema = table.schema := by
  unfold Table.withPatchedRows at success
  split at success
  next localized localizedResult =>
      have localizedSchema := Table.upsertDifferences?_schema table
        table.rows rows localized localizedResult
      split at success
      next =>
        injection success with equal
        subst next
        exact localizedSchema
      next => exact (Table.rebuild_exact success).1
  next => exact (Table.rebuild_exact success).1

def Table.requirePatchedChecks (table : Table) (selected : Row → Bool)
    (rows : List Row) (assigned : List Nat) : Except String Unit := do
  for (before, after) in table.rows.zip rows do
    if selected before then table.requireChecks after (some assigned)

def Table.patchRows (table : Table) (assignments : List (Nat × Value))
    (selected : Row → Bool) : Except String Table := do
  let rows ← Core.patchRows table.schema assignments selected table.rows
  table.requirePatchedChecks selected rows (assignments.map Prod.fst)
  if uniqueIndexesAccept table.indexes rows then table.withPatchedRows rows
  else .error (uniqueRowsError table.schema table.indexes rows)

/-- The proof-carrying representation makes the primary-tree lookup exact at
the rowid boundary: a successful routed lookup cannot return a different
signed key. -/
theorem Table.findRowid?_some_eq {table : Table} {rowid : Integer} {row : Row}
    (found : table.findRowid? rowid = some row) : row.rowid = rowid := by
  have foundErased : table.rowTree.root.erase.lookup rowid.treeKey = some row := by
    rw [← PersistentPageTree.Node.lookup_eq_erase]
    exact found
  have inTree := RecursiveBPlusTree.Node.lookup_some_mem foundErased
  have represented := table.rowTreeWellKeyed
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at represented
  rw [represented] at inTree
  rcases List.mem_map.mp inTree with ⟨source, _, pairEqual⟩
  have keyEqual : source.treeKey = rowid.treeKey :=
    congrArg Prod.fst pairEqual
  have rowEqual : source = row := congrArg Prod.snd pairEqual
  rw [rowEqual] at keyEqual
  exact FileFormat.SignedInteger.ext
    ((Integer.treeKey_eq_iff row.rowid rowid).mp keyEqual)

theorem Table.findRowid?_some_mem {table : Table} {rowid : Integer} {row : Row}
    (found : table.findRowid? rowid = some row) : row ∈ table.rows := by
  have foundErased : table.rowTree.root.erase.lookup rowid.treeKey = some row := by
    rw [← PersistentPageTree.Node.lookup_eq_erase]
    exact found
  have inTree := RecursiveBPlusTree.Node.lookup_some_mem foundErased
  have represented := table.rowTreeWellKeyed
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at represented
  rw [represented] at inTree
  rcases List.mem_map.mp inTree with ⟨source, member, pairEqual⟩
  have rowEqual : source = row := congrArg Prod.snd pairEqual
  simpa [rowEqual, Table.rows] using member

/-- Every logical row represented by the table is reachable by routed primary
lookup. This is the completeness half needed to trust pruning rather than
checking it against a scan. -/
theorem Table.findRowid?_eq_some_of_mem {table : Table} {rowid : Integer}
    {row : Row} (member : row ∈ table.rows) (same : row.rowid = rowid) :
    table.findRowid? rowid = some row := by
  have inEntries : (rowid.treeKey, row) ∈ treeEntries table.rows := by
    apply List.mem_map.mpr
    refine ⟨row, member, ?_⟩
    simp only [Prod.mk.injEq, and_true]
    exact congrArg Integer.treeKey same
  have represented := table.rowTreeWellKeyed
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at represented
  unfold Table.findRowid?
  rw [PersistentPageTree.Node.lookup_eq_erase]
  apply RecursiveBPlusTree.Node.lookup_of_mem table.rowTree.rootValid
  rw [represented]
  exact inEntries

theorem Table.findRowid?_eq_some_iff {table : Table} {rowid : Integer}
    {row : Row} :
    table.findRowid? rowid = some row ↔
      row ∈ table.rows ∧ row.rowid = rowid := by
  constructor
  · intro found
    exact ⟨Table.findRowid?_some_mem found, Table.findRowid?_some_eq found⟩
  · intro valid
    exact Table.findRowid?_eq_some_of_mem valid.1 valid.2

/-- Point UPDATE through the persistent primary tree. The rowid equality
checks make the fast path defensive even before lookup correctness is used as
a proof premise, and primary-key-changing assignments stay on the general
validation path. -/
def Table.patchRowid (table : Table) (assignments : List (Nat × Value))
    (rowid : Integer) : Except String (Table × Nat) :=
  match table.findRowid? rowid with
  | none => .ok (table, 0)
  | some row =>
      match created : Row.create table.schema
          (applyAssignments row.values assignments) with
      | .error message => .error message
      | .ok patched =>
          match table.requireChecks patched (some (assignments.map Prod.fst)) with
          | .error message => .error message
          | .ok _ =>
            if table.uniqueConflict patched true then .error (table.uniqueConflictMessage patched true)
            else if _samePatched : patched.rowid = rowid then
              .ok (table.upsert patched (Row.create_wellFormed created), 1)
            else .error "point UPDATE changed its INTEGER PRIMARY KEY"

theorem Table.patchRowid_schema {table next : Table}
    {assignments : List (Nat × Value)} {rowid : Integer} {changes : Nat}
    (success : table.patchRowid assignments rowid = .ok (next, changes)) :
    next.schema = table.schema := by
  unfold Table.patchRowid at success
  cases found : table.findRowid? rowid with
  | none =>
      rw [found] at success
      simp only at success
      have pairEqual := Except.ok.inj success
      have tableEqual : table = next := by
        simpa using congrArg Prod.fst pairEqual
      subst next
      rfl
  | some row =>
      rw [found] at success
      simp only at success
      split at success
      next => contradiction
      next patched created =>
        split at success <;> try contradiction
        split at success <;> try contradiction
        split at success <;> try contradiction
        have pairEqual := Except.ok.inj success
        have tableEqual : table.upsert patched (Row.create_wellFormed created) =
            next := by
          simpa using congrArg Prod.fst pairEqual
        subst next
        rfl

theorem Table.patchRowid_exact {table next : Table}
    {assignments : List (Nat × Value)} {rowid : Integer} {changes : Nat}
    (success : table.patchRowid assignments rowid = .ok (next, changes)) :
    (table.findRowid? rowid = none ∧ next = table ∧ changes = 0) ∨
    ∃ row patched,
      table.findRowid? rowid = some row ∧
      Row.create table.schema (applyAssignments row.values assignments) =
        .ok patched ∧
      patched.rowid = rowid ∧ changes = 1 ∧
      next.rows = orderedUpsert patched table.rows := by
  unfold Table.patchRowid at success
  cases found : table.findRowid? rowid with
  | none =>
      rw [found] at success
      simp only at success
      have pairEqual := Except.ok.inj success
      have tableEqual : table = next := by
        simpa using congrArg Prod.fst pairEqual
      have changesEqual : 0 = changes := by
        simpa using congrArg Prod.snd pairEqual
      exact Or.inl ⟨rfl, tableEqual.symm, changesEqual.symm⟩
  | some row =>
      rw [found] at success
      simp only at success
      split at success
      next => contradiction
      next patched created =>
        split at success <;> try contradiction
        split at success <;> try contradiction
        split at success
        next samePatched =>
          have pairEqual := Except.ok.inj success
          have tableEqual : table.upsert patched
              (Row.create_wellFormed created) = next := by
            simpa using congrArg Prod.fst pairEqual
          have changesEqual : 1 = changes := by
            simpa using congrArg Prod.snd pairEqual
          refine Or.inr ⟨row, patched, rfl, created, samePatched,
            changesEqual.symm, ?_⟩
          rw [← tableEqual]
          exact Table.upsert_rows table patched (Row.create_wellFormed created)
        next => contradiction

theorem Table.patchRows_exact {table next : Table}
    {assignments : List (Nat × Value)} {selected : Row → Bool}
    {rows : List Row} (patched : Core.patchRows table.schema assignments selected table.rows = .ok rows)
    (success : table.patchRows assignments selected = .ok next) :
    next.rows = rows := by
  unfold Table.patchRows at success
  rw [patched] at success
  simp only [bind, Except.bind] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  change table.withPatchedRows rows = .ok next at success
  unfold Table.withPatchedRows at success
  split at success
  next localized =>
      split at success
      next exactResult =>
        injection success with equal
        subst next
        exact exactResult
      next => exact (Table.rebuild_exact success).2.2
  next =>
      exact (Table.rebuild_exact success).2.2

theorem Table.patchRows_schema {table next : Table}
    {assignments : List (Nat × Value)} {selected : Row → Bool}
    (success : table.patchRows assignments selected = .ok next) :
    next.schema = table.schema := by
  unfold Table.patchRows at success
  cases patched : Core.patchRows table.schema assignments selected table.rows with
  | error message =>
      rw [patched] at success
      contradiction
  | ok rows =>
      simp only [patched, bind, Except.bind] at success
      split at success <;> try contradiction
      split at success <;> try contradiction
      exact Table.withPatchedRows_schema success

end Core

end SQLeanite
