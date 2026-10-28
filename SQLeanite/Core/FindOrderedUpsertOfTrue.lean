import SQLeanite.Core.TablePrepareRow

namespace SQLeanite
namespace Core
attribute [local instance] lexOrd

private theorem find?_orderedUpsert_of_true (inserted : Row) (rows : List Row)
    (predicate : Row → Bool) (insertedTrue : predicate inserted = true)
    (oldNone : rows.find? predicate = none) :
    (orderedUpsert inserted rows).find? predicate = some inserted := by
  induction rows with
  | nil => simp [orderedUpsert, insertedTrue]
  | cons head tail induction =>
      have headFalse : predicate head = false := by
        cases result : predicate head <;> simp_all
      have tailNone : tail.find? predicate = none := by
        simpa [headFalse] using oldNone
      by_cases before : inserted.rowid.value < head.rowid.value
      · simp [orderedUpsert, before, insertedTrue]
      · by_cases after : head.rowid.value < inserted.rowid.value
        · simp [orderedUpsert, before, after, headFalse,
            induction tailNone]
        · simp [orderedUpsert, before, after, insertedTrue]

/-- Replacing the first row selected by a predicate makes the replacement the
first selected row when it has the same rowid and still satisfies the
predicate. This is the list-level fact behind incremental TEXT-primary-key map
maintenance. -/
private theorem find?_orderedUpsert_replacing_first_of_true
    (inserted previous : Row) (predicate : Row → Bool) :
    ∀ (rows : List Row), rows.Pairwise Row.keyLess →
      predicate inserted = true → previous.rowid = inserted.rowid →
      rows.find? predicate = some previous →
      (orderedUpsert inserted rows).find? predicate = some inserted
  | [], _, _, _, found => by simp at found
  | head :: tail, sorted, insertedTrue, sameRowid, found => by
      have sortedParts := List.pairwise_cons.mp sorted
      cases headMatch : predicate head with
      | true =>
          have previousEq : previous = head := by
            have headEq : head = previous := by simpa [headMatch] using found
            exact headEq.symm
          subst previous
          have valuesEq : head.rowid.value = inserted.rowid.value :=
            congrArg FileFormat.SignedInteger.value sameRowid
          have notBefore : ¬inserted.rowid.value < head.rowid.value := by omega
          have notAfter : ¬head.rowid.value < inserted.rowid.value := by omega
          simp [orderedUpsert, notBefore, notAfter, insertedTrue]
      | false =>
          have tailFound : tail.find? predicate = some previous := by
            simpa [headMatch] using found
          have previousMember : previous ∈ tail :=
            List.mem_of_find?_eq_some tailFound
          have headBeforePrevious := sortedParts.1 previous previousMember
          have valuesEq : previous.rowid.value = inserted.rowid.value :=
            congrArg FileFormat.SignedInteger.value sameRowid
          have headBefore : head.rowid.value < inserted.rowid.value := by
            simpa [Row.keyLess, valuesEq] using headBeforePrevious
          have notBefore : ¬inserted.rowid.value < head.rowid.value := by omega
          simp [orderedUpsert, notBefore, headBefore, headMatch,
            find?_orderedUpsert_replacing_first_of_true inserted previous
              predicate tail sortedParts.2 insertedTrue sameRowid tailFound]

/-- Replacing a row which does not satisfy a predicate leaves the first match
unchanged when the replacement also does not satisfy it. -/
private theorem find?_orderedUpsert_replacing_of_false
    (inserted previous : Row) (predicate : Row → Bool) :
    ∀ (rows : List Row), rows.Pairwise Row.keyLess → previous ∈ rows →
      previous.rowid = inserted.rowid → predicate inserted = false →
      predicate previous = false →
      (orderedUpsert inserted rows).find? predicate = rows.find? predicate
  | [], _, member, _, _, _ => by simp at member
  | head :: tail, sorted, member, sameRowid, insertedFalse, previousFalse => by
      have sortedParts := List.pairwise_cons.mp sorted
      simp only [List.mem_cons] at member
      rcases member with previousEq | previousTail
      · subst previous
        have valuesEq : head.rowid.value = inserted.rowid.value :=
          congrArg FileFormat.SignedInteger.value sameRowid
        have notBefore : ¬inserted.rowid.value < head.rowid.value := by omega
        have notAfter : ¬head.rowid.value < inserted.rowid.value := by omega
        simp [orderedUpsert, notBefore, notAfter, insertedFalse, previousFalse]
      · have headBeforePrevious := sortedParts.1 previous previousTail
        have valuesEq : previous.rowid.value = inserted.rowid.value :=
          congrArg FileFormat.SignedInteger.value sameRowid
        have headBefore : head.rowid.value < inserted.rowid.value := by
          simpa [Row.keyLess, valuesEq] using headBeforePrevious
        have notBefore : ¬inserted.rowid.value < head.rowid.value := by omega
        simp only [orderedUpsert, if_neg notBefore, if_pos headBefore,
          List.find?_cons]
        cases headResult : predicate head
        · exact find?_orderedUpsert_replacing_of_false inserted previous
            predicate tail sortedParts.2 previousTail sameRowid insertedFalse
              previousFalse
        · rfl

private theorem Table.rowTree_lookup_some_mem_eq
    {table : Table} {row previous : Row}
    (found : table.rowTree.root.lookup row.treeKey = some previous) :
    previous ∈ table.rows ∧ previous.rowid = row.rowid := by
  have foundErased : table.rowTree.root.erase.lookup row.treeKey =
      some previous := by
    rw [← PersistentPageTree.Node.lookup_eq_erase]
    exact found
  have inTree := RecursiveBPlusTree.Node.lookup_some_mem foundErased
  have represented := table.rowTreeWellKeyed
  unfold RowTreeWellKeyed PersistentPageTree.Store.Represents at represented
  rw [represented] at inTree
  rcases List.mem_map.mp inTree with ⟨source, member, pairEqual⟩
  have keyEqual : source.treeKey = row.treeKey :=
    congrArg Prod.fst pairEqual
  have rowEqual : source = previous := congrArg Prod.snd pairEqual
  subst source
  refine ⟨member, FileFormat.SignedInteger.ext ?_⟩
  exact (Row.treeKey_eq_iff previous row).mp keyEqual

/-- Updating the row which owns a declared key can update the balanced key map
with one insert. The proof handles every other lookup explicitly, so this is a
representation theorem rather than a cache-coherence assumption. -/
theorem Table.declaredKeyMap_replace_represents_orderedUpsert
    (table : Table) (row previous : Row)
    (hidden : table.schema.hasHiddenRowid = true)
    (found : table.rowTree.root.lookup row.treeKey = some previous)
    (sameKey : previous.declaredKey table.schema =
      row.declaredKey table.schema)
    (owner : table.declaredKeyMap.get? (row.declaredKey table.schema) =
      some previous) :
    DeclaredKeyMapRepresents table.schema (orderedUpsert row table.rows)
      (table.declaredKeyMap.insert (row.declaredKey table.schema) row) := by
  have previousFacts := table.rowTree_lookup_some_mem_eq found
  intro _ target
  change (table.declaredKeyMap.insert
    (row.declaredKey table.schema) row)[target]? = _
  rw [Std.TreeMap.getElem?_insert]
  simp only [DeclaredKey.compareOn_orderKey_eq]
  have represented := table.declaredKeyMapRepresents hidden target
  change table.declaredKeyMap[target]? =
    table.rows.find? (fun existing =>
      existing.declaredKey table.schema == target) at represented
  by_cases sameTarget : row.declaredKey table.schema = target
  · subst target
    rw [if_pos rfl]
    have oldFound : table.rows.find? (fun existing =>
        existing.declaredKey table.schema == row.declaredKey table.schema) =
        some previous := by
      have representedKey := table.declaredKeyMapRepresents hidden
        (row.declaredKey table.schema)
      rw [owner] at representedKey
      exact representedKey.symm
    exact (find?_orderedUpsert_replacing_first_of_true row previous _
      table.rows table.rowsWellFormed.2 (by simp) previousFacts.2
        oldFound).symm
  · rw [if_neg sameTarget, represented]
    exact (find?_orderedUpsert_replacing_of_false row previous _ table.rows
      table.rowsWellFormed.2 previousFacts.1 previousFacts.2
        (by simp [sameTarget]) (by simp [sameKey, sameTarget])).symm

theorem Table.declaredKeyMap_insert_represents_orderedUpsert (table : Table)
    (row : Row) (hidden : table.schema.hasHiddenRowid = true)
    (freshRowid : ∀ existing ∈ table.rows,
      existing.rowid.value ≠ row.rowid.value)
    (fresh : table.declaredKeyMap.get? (row.declaredKey table.schema) = none) :
    DeclaredKeyMapRepresents table.schema (orderedUpsert row table.rows)
      (table.declaredKeyMap.insert (row.declaredKey table.schema) row) := by
  intro _ target
  change (table.declaredKeyMap.insert
    (row.declaredKey table.schema) row)[target]? = _
  rw [Std.TreeMap.getElem?_insert]
  simp only [DeclaredKey.compareOn_orderKey_eq]
  have represented := table.declaredKeyMapRepresents hidden target
  have keyAbsent := table.declaredKeyMapRepresents hidden
    (row.declaredKey table.schema)
  rw [fresh] at keyAbsent
  change table.declaredKeyMap[target]? =
    table.rows.find? (fun existing => existing.declaredKey table.schema == target)
    at represented
  have oldNone : table.rows.find? (fun existing =>
      existing.declaredKey table.schema == row.declaredKey table.schema) =
      none := by
    simpa only [Table.rows] using keyAbsent.symm
  by_cases same : row.declaredKey table.schema = target
  · subst target
    rw [if_pos rfl]
    exact (find?_orderedUpsert_of_true row table.rows _ (by simp) oldNone).symm
  · rw [if_neg same, represented]
    exact (find?_orderedUpsert_of_false row table.rows _ (by simp [same])
      freshRowid).symm

/-- O(log n) append for the hidden-rowid table shape.  The two erased premises
come from `nextGeneratedRowid?` and the proof-carrying declared-key map, so the
runtime performs one primary-tree insert and one balanced-map insert without
reconstructing either logical list. -/
def Table.upsertGeneratedFresh (table : Table) (row : Row)
    (valid : row.WellFormed table.schema)
    (hidden : table.schema.hasHiddenRowid = true)
    (freshRowid : ∀ existing ∈ table.rows,
      existing.rowid.value ≠ row.rowid.value)
    (fresh : table.declaredKeyMap.get? (row.declaredKey table.schema) = none) :
    Table :=
  { table with
    rowTree := table.rowTree.insert row.treeKey row
    rowTreeWellKeyed := rowTreeWellKeyed_insert table.rowTree
      table.rowTreeWellKeyed row
    declaredKeyMap := table.declaredKeyMap.insert
      (row.declaredKey table.schema) row
    declaredKeyMapRepresents := by
      rw [storedRows_insert table.rowTree table.rowTreeWellKeyed row]
      simpa only [Table.rows] using
        table.declaredKeyMap_insert_represents_orderedUpsert row hidden
          freshRowid fresh
    rowsWellFormed := by
      rw [storedRows_insert table.rowTree table.rowTreeWellKeyed row]
      constructor
      · intro candidate member
        rcases mem_orderedUpsert member with equal | old
        · simpa [equal] using valid
        · exact table.rowsWellFormed.1 candidate old
      · exact orderedUpsert_sorted row table.rows table.rowsWellFormed.2 }

/-- Incremental declared-key maintenance for the common hidden-rowid mutation.

TEXT-primary UPDATE and REPLACE preserve the declared key and replace the row
which currently owns it. That branch performs one primary-tree lookup and one
balanced-map insert. Unusual operations which change the declared key, or a
noncanonical table with duplicate declared keys, retain the exact rebuild
fallback. Thus the fast path is logarithmic without weakening the invariant,
while the fallback preserves the full existing semantics. -/
def declaredKeyMapAfterUpsert (table : Table) (row : Row) : DeclaredKeyMap :=
  if table.schema.hasHiddenRowid then
    match table.rowTree.root.lookup row.treeKey with
    | some previous =>
        if previous.declaredKey table.schema = row.declaredKey table.schema then
          if table.declaredKeyMap.get? (row.declaredKey table.schema) =
              some previous then
            table.declaredKeyMap.insert (row.declaredKey table.schema) row
          else buildDeclaredKeyMap table.schema (orderedUpsert row table.rows)
        else buildDeclaredKeyMap table.schema (orderedUpsert row table.rows)
    | none => buildDeclaredKeyMap table.schema (orderedUpsert row table.rows)
  else ∅

theorem declaredKeyMapAfterUpsert_represents (table : Table) (row : Row) :
    DeclaredKeyMapRepresents table.schema (orderedUpsert row table.rows)
      (declaredKeyMapAfterUpsert table row) := by
  unfold declaredKeyMapAfterUpsert
  split
  next hidden =>
    cases found : table.rowTree.root.lookup row.treeKey with
    | none => exact buildDeclaredKeyMap_represents table.schema _
    | some previous =>
      simp only
      split
      next sameKey =>
        split
        next owner =>
          exact table.declaredKeyMap_replace_represents_orderedUpsert row
            previous hidden found sameKey owner
        next => exact buildDeclaredKeyMap_represents table.schema _
      next => exact buildDeclaredKeyMap_represents table.schema _
  next visible =>
    intro hidden
    contradiction

def Table.upsert (table : Table) (row : Row)
    (valid : row.WellFormed table.schema) : Table :=
  { table with
    rowTree := table.rowTree.insert row.treeKey row
    rowTreeWellKeyed := rowTreeWellKeyed_insert table.rowTree
      table.rowTreeWellKeyed row
    declaredKeyMap := declaredKeyMapAfterUpsert table row
    declaredKeyMapRepresents := by
      rw [storedRows_insert table.rowTree table.rowTreeWellKeyed row]
      exact declaredKeyMapAfterUpsert_represents table row
    rowsWellFormed := by
      rw [storedRows_insert table.rowTree table.rowTreeWellKeyed row]
      constructor
      · intro candidate member
        rcases mem_orderedUpsert member with equal | old
        · simpa [equal] using valid
        · exact table.rowsWellFormed.1 candidate old
      · exact orderedUpsert_sorted row table.rows table.rowsWellFormed.2 }

/-- Exact routed lookup in the proof-carrying primary tree. -/
def Table.findRowid? (table : Table) (rowid : Integer) : Option Row :=
  table.rowTree.root.lookup rowid.treeKey

private theorem Table.findRowid?_eq_some_of_mem_early {table : Table}
    {rowid : Integer} {row : Row} (member : row ∈ table.rows)
    (same : row.rowid = rowid) : table.findRowid? rowid = some row := by
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

private theorem Table.findRowid?_fresh_of_not_isSome {table : Table}
    {rowid : Integer} (absent : ¬(table.findRowid? rowid).isSome = true) :
    ∀ existing ∈ table.rows, existing.rowid.value ≠ rowid.value := by
  intro existing member sameValue
  have same : existing.rowid = rowid :=
    FileFormat.SignedInteger.ext sameValue
  have found := Table.findRowid?_eq_some_of_mem_early member same
  rw [found] at absent
  simp at absent

theorem Table.upsert_rows (table : Table) (row : Row)
    (valid : row.WellFormed table.schema) :
    (table.upsert row valid).rows = orderedUpsert row table.rows := by
  exact storedRows_insert table.rowTree table.rowTreeWellKeyed row

theorem Table.upsertGeneratedFresh_rows (table : Table) (row : Row)
    (valid : row.WellFormed table.schema)
    (hidden : table.schema.hasHiddenRowid = true)
    (freshRowid : ∀ existing ∈ table.rows,
      existing.rowid.value ≠ row.rowid.value)
    (fresh : table.declaredKeyMap.get? (row.declaredKey table.schema) = none) :
    (table.upsertGeneratedFresh row valid hidden freshRowid fresh).rows =
      orderedUpsert row table.rows := by
  exact storedRows_insert table.rowTree table.rowTreeWellKeyed row

/-- UNIQUE compares BINARY SQL values, treating all NULLs as distinct and
INTEGER/REAL values by exact numeric order rather than physical encoding. -/
def uniqueValueConflict : Value → Value → Bool
  | .null, _ | _, .null => false
  | left, right => PhysicalQuery.compareValue left right == .eq

def Index.rowConflict (index : Index) (left right : Row) : Bool :=
  index.unique && uniqueValueConflict
    ((left.values[index.column]?).getD .null) ((right.values[index.column]?).getD .null)

def Index.acceptsRows (index : Index) : List Row → Bool
  | [] => true
  | row :: rows => !(rows.any (index.rowConflict row)) && index.acceptsRows rows

def uniqueIndexesAccept (indexes : List Index) (rows : List Row) : Bool :=
  indexes.all (fun index => !index.unique || index.acceptsRows rows)

def Table.uniqueConflict (table : Table) (row : Row) (ignoreOwnRowid : Bool := false) : Bool :=
  table.indexes.any fun index => index.unique && table.rows.any fun other =>
    (!ignoreOwnRowid || other.rowid != row.rowid) && index.rowConflict row other

theorem uniqueValueConflict_null_left (value : Value) :
    uniqueValueConflict .null value = false := rfl

theorem uniqueValueConflict_null_right (value : Value) :
    uniqueValueConflict value .null = false := by cases value <;> rfl

/-- Constraint diagnostics identify the actual indexed column. SQLite visits
later-created ordinary UNIQUE indexes first. -/
def uniqueIndexError (schema : Schema) (index : Index) : String :=
  s!"UNIQUE constraint failed: {schema.name}.{((schema.columns[index.column]?).map (·.name)).getD "rowid"}"

def uniqueRowsError (schema : Schema) (indexes : List Index) (rows : List Row) : String :=
  match indexes.reverse.find? (fun index => index.unique && !index.acceptsRows rows) with
  | some index => uniqueIndexError schema index
  | none => "UNIQUE constraint failed"

def Table.uniqueConflictMessage (table : Table) (row : Row) (ignoreOwnRowid : Bool := false) : String :=
  uniqueRowsError table.schema table.indexes
    (row :: table.rows.filter (fun other => !ignoreOwnRowid || other.rowid != row.rowid))

def Table.insertValues (table : Table) (values : List Value) :
    Except String Table :=
  match table.createRow values with
  | .error message => .error message
  | .ok row =>
      if table.uniqueConflict row then .error (table.uniqueConflictMessage row)
      else if valid : row.WellFormed table.schema then
        if duplicate : (table.findRowid? row.rowid).isSome then
          .error s!"UNIQUE constraint failed: {table.schema.name}.{if table.schema.hasHiddenRowid then "rowid" else ((table.schema.columns[table.schema.primaryKey]?).map (·.name)).getD "rowid"}"
        else match declared : table.findDeclaredPrimary? row with
          | some _ => .error "UNIQUE constraint failed: PRIMARY KEY"
          | none =>
              if hidden : table.schema.hasHiddenRowid then
                have fresh : table.declaredKeyMap.get?
                    (row.declaredKey table.schema) = none := by
                  simpa [Table.findDeclaredPrimary?, hidden] using declared
                have freshRowid := table.findRowid?_fresh_of_not_isSome duplicate
                .ok (table.upsertGeneratedFresh row valid hidden freshRowid fresh)
              else .ok (table.upsert row valid)
      else .error "internal row validation mismatch"

theorem Table.insertValues_unique {table next : Table} {values : List Value}
    (success : table.insertValues values = .ok next) :
    ∃ row, table.createRow values = .ok row ∧ table.uniqueConflict row = false := by
  cases created : table.createRow values with
  | error message => simp [Table.insertValues, created] at success
  | ok row =>
      simp only [Table.insertValues, created] at success
      split at success
      next conflict => contradiction
      next fresh => exact ⟨row, rfl, Bool.eq_false_iff.mpr fresh⟩

/-- The exact effect of a successful `INSERT` at table level.

The rowid-freshness conjunct is not decoration. `insertValues` *checks* it -- a
duplicate `INTEGER PRIMARY KEY` is an error, never a silent replacement -- but
until it appeared in the postcondition no downstream theorem could use it, so an
insert was indistinguishable from an upsert to everything above this line. It is
what lets the bag-level statement in `CoreWriteSemantics` be union with a
singleton rather than the weaker replace-then-union. -/
theorem Table.insertValues_exact {table next : Table} {values : List Value}
    (success : table.insertValues values = .ok next) :
    ∃ row, table.createRow values = .ok row ∧
      row.WellFormed table.schema ∧
      (∀ existing ∈ table.rows, existing.rowid.value ≠ row.rowid.value) ∧
      table.findDeclaredPrimary? row = none ∧
      next.rows = orderedUpsert row table.rows := by
  cases created : table.createRow values with
  | error message =>
      simp only [Table.insertValues, created] at success
      contradiction
  | ok row =>
      simp only [Table.insertValues, created] at success
      split at success <;> try contradiction
      split at success
      next valid =>
        split at success
        next duplicate => contradiction
        next fresh =>
          have freshRowid := table.findRowid?_fresh_of_not_isSome fresh
          split at success
          next duplicate => contradiction
          next declaredFresh =>
            split at success
            next hidden =>
              injection success with equal
              subst next
              exact ⟨row, rfl, valid, freshRowid, declaredFresh,
                Table.upsertGeneratedFresh_rows table row valid _ _ _⟩
            next visible =>
              injection success with equal
              subst next
              exact ⟨row, rfl, valid, freshRowid, declaredFresh,
                Table.upsert_rows table row valid⟩
      next => contradiction

theorem Table.insertValues_schema {table next : Table} {values : List Value}
    (success : table.insertValues values = .ok next) :
    next.schema = table.schema := by
  cases created : table.createRow values with
  | error message =>
      simp only [Table.insertValues, created] at success
      contradiction
  | ok row =>
      simp only [Table.insertValues, created] at success
      split at success <;> try contradiction
      split at success <;> try contradiction
      split at success <;> try contradiction
      split at success <;> try contradiction
      split at success
      <;> injection success with equal
      <;> subst next
      <;> rfl

end Core

end SQLeanite
