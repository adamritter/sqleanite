import SQLeanite.CoreSQLReadText.ExecuteStatementEqCore
import SQLeanite.CoreSQLWriteText.ExecuteTextTraceRecoveryCrashTraceAtomic

namespace SQLeanite
namespace CoreWriteSemantics

open QuerySemantics

/-!
# Write-side bag semantics

The read side has a denotational story: `CoreReadSemantics.execute_query_denotes`
and its family land in `KRelation`, an algebra defined without reference to the
executor. The write side had no analogue. `Core.orderedUpsert` served as both
specification and implementation -- it is a list function with insertion-order
semantics -- so there was no statement of what an `INSERT` *means* that was
independent of how it is performed, and the two sides never met.

This module supplies the missing half. It deliberately reuses
`CoreReadSemantics.coreRow` as the abstraction function rather than introducing a
second one: the object an `INSERT` changes is exactly the object a `SELECT`
observes, and using two abstractions would make that impossible to state.
-/

/-- The bag a table denotes.  Chosen to be exactly what the read side's plan
evaluation produces (`CoreReadSemantics.tableFilterPlan_eval` with no predicate),
so write effects and read results are comparable without a translation step. -/
def tableDenotation (rows : List Core.Row) :
    KRelation.Relation QuerySemantics.Row :=
  RelationalAlgebra.ofList (rows.map CoreReadSemantics.coreRow)

theorem tableDenotation_nil : tableDenotation [] = KRelation.empty := rfl

/-- Table rows are strictly ordered by rowid, which is what makes "at most one
row carries this rowid" available to every statement below. -/
theorem rows_pairwise (table : Core.Table) :
    table.rows.Pairwise Core.Row.keyLess :=
  table.rowsWellFormed.2

/-- **The general ordered-insert denotation.** The post-state bag is the pre-state
bag with any same-rowid row removed, unioned with the new row. This is the
`REPLACE` shape: no freshness is assumed. -/
theorem tableDenotation_orderedUpsert (row : Core.Row) (rows : List Core.Row)
    (sorted : rows.Pairwise Core.Row.keyLess) :
    tableDenotation (Core.orderedUpsert row rows) =
      KRelation.unionAll
        (tableDenotation (rows.filter (fun candidate =>
          candidate.rowid.value != row.rowid.value)))
        (KRelation.single (CoreReadSemantics.coreRow row)) := by
  unfold tableDenotation
  rw [RelationalAlgebra.ofList_perm
    ((Core.orderedUpsert_perm row rows sorted).map CoreReadSemantics.coreRow),
    List.map_cons, RelationalAlgebra.ofList_cons, KRelation.unionAll_comm]

/-- **The insert denotation.** For a rowid the table does not already carry --
which is exactly what `Core.execute` checks before admitting an `INSERT`, and now
carries in its postcondition -- the post-state bag is the pre-state bag unioned
with a singleton.

This is the statement that was missing: `⟦after⟧ = ⟦before⟧ ⊎ {row}`, with `⊎`
and `{row}` defined in `KRelation` independently of the executor. -/
theorem tableDenotation_orderedUpsert_fresh (row : Core.Row)
    (rows : List Core.Row) (sorted : rows.Pairwise Core.Row.keyLess)
    (fresh : ∀ existing ∈ rows, existing.rowid.value ≠ row.rowid.value) :
    tableDenotation (Core.orderedUpsert row rows) =
      KRelation.unionAll (tableDenotation rows)
        (KRelation.single (CoreReadSemantics.coreRow row)) := by
  have kept : rows.filter (fun candidate =>
      candidate.rowid.value != row.rowid.value) = rows := by
    apply List.filter_eq_self.mpr
    intro candidate member
    simp [fresh candidate member]
  rw [tableDenotation_orderedUpsert row rows sorted, kept]

/-- The live executor's `INSERT`, denoted.  Everything about *how* the row is
placed -- ordering, the persistent tree, the declared-key map -- has been
discharged by this point; what remains is bag union with a singleton, plus the
frame condition for every other table. -/
theorem execute_insert_denotes {state next : Core.State} {tableName : String}
    {values : List Core.Value} {result : Core.Result}
    (success : Core.execute state (.insert tableName values) =
      .ok (next, result)) :
    ∃ table replacement row,
      state.database.findTable? tableName = some table ∧
      table.createRow values = .ok row ∧
      next.database.findTable? tableName = some replacement ∧
      tableDenotation replacement.rows =
        KRelation.unionAll (tableDenotation table.rows)
          (KRelation.single (CoreReadSemantics.coreRow row)) ∧
      result = { changes := 1 } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other := by
  rcases Core.execute_insert_exact success with
    ⟨table, replacement, row, found, created, _valid, freshRowid, _declared,
      replacementRows, updatedFound, _snapshot, changes, frame⟩
  refine ⟨table, replacement, row, found, created, updatedFound, ?_, changes, frame⟩
  rw [replacementRows]
  exact tableDenotation_orderedUpsert_fresh row table.rows (rows_pairwise table)
    freshRowid

/-- The multiplicity form, which is the one that reads as a sentence: inserting a
row raises that row's multiplicity by exactly one and changes no other tuple's. -/
theorem execute_insert_multiplicity {state next : Core.State} {tableName : String}
    {values : List Core.Value} {result : Core.Result}
    (success : Core.execute state (.insert tableName values) =
      .ok (next, result)) :
    ∃ table replacement row,
      state.database.findTable? tableName = some table ∧
      next.database.findTable? tableName = some replacement ∧
      tableDenotation replacement.rows (CoreReadSemantics.coreRow row) =
        tableDenotation table.rows (CoreReadSemantics.coreRow row) + 1 ∧
      ∀ other : QuerySemantics.Row, other ≠ CoreReadSemantics.coreRow row →
        tableDenotation replacement.rows other = tableDenotation table.rows other := by
  rcases execute_insert_denotes success with
    ⟨table, replacement, row, found, created, updatedFound, denoted, _changes,
      _frame⟩
  refine ⟨table, replacement, row, found, updatedFound, ?_, ?_⟩
  · rw [denoted]
    show tableDenotation table.rows (CoreReadSemantics.coreRow row) +
      KRelation.single (CoreReadSemantics.coreRow row)
        (CoreReadSemantics.coreRow row) = _
    rw [KRelation.single_self]
  · intro other different
    rw [denoted]
    show tableDenotation table.rows other +
      KRelation.single (CoreReadSemantics.coreRow row) other = _
    rw [KRelation.single_of_ne different, Nat.add_zero]

/-- `DELETE` denotes bag difference by predicate, stated for symmetry with the
insert case: the write side now has both directions in the same algebra. -/
theorem execute_deleteWhere_denotes {state next : Core.State} {tableName : String}
    {predicate : Option Core.Predicate} {result : Core.Result}
    (success : Core.execute state (.deleteWhere tableName predicate) =
      .ok (next, result)) :
    ∃ table replacement,
      state.database.findTable? tableName = some table ∧
      next.database.findTable? tableName = some replacement ∧
      tableDenotation replacement.rows =
        RelationalAlgebra.ofList
          ((table.rows.filter (fun row => !Core.selects predicate row)).map
            CoreReadSemantics.coreRow) := by
  rcases Core.execute_deleteWhere_exact success with
    ⟨table, replacement, found, replacementRows, updatedFound, _rest⟩
  exact ⟨table, replacement, found, updatedFound, by
    unfold tableDenotation
    rw [replacementRows]⟩

/-! ## Closing the loop: write, encode, reopen, read

Everything above stops at the logical post-state. The statement a
byte-compatibility paper actually wants is the round trip: the row an `INSERT`
adds is the row a later `SELECT` observes *through the encoded file and a
reopen*. That crosses `encodeBulk`/`decode`, so it composes the existing
whole-image inverse rather than re-proving it.
-/

private theorem find?_map_canonicalize (name : String) :
    ∀ tables : List Core.Table,
      (tables.map Core.Table.canonicalize).find?
          (fun table => table.schema.name == name) =
        (tables.find? (fun table => table.schema.name == name)).map
          Core.Table.canonicalize
  | [] => rfl
  | table :: tables => by
      have sameSchema : (Core.Table.canonicalize table).schema = table.schema := rfl
      simp only [List.map_cons, List.find?_cons, sameSchema]
      cases hit : (table.schema.name == name) with
      | true => simp [hit]
      | false =>
          simp only [hit]
          exact find?_map_canonicalize name tables

/-- Canonical rebuilding commutes with catalog lookup.  Reopening a file yields
the canonicalized database, so every statement about a reopened table has to pass
through this. -/
theorem canonicalize_findTable? (database : Core.Database) (name : String) :
    database.canonicalize.findTable? name =
      (database.findTable? name).map Core.Table.canonicalize := by
  show (database.canonicalize.tables.find?
    (fun table => table.schema.name == name)) = _
  show ((database.tables.map Core.Table.canonicalize).find?
    (fun table => table.schema.name == name)) = _
  exact find?_map_canonicalize name database.tables

/-- **The insert survives the round trip.** Execute an `INSERT`, encode the
post-state to SQLite bytes, decode those bytes back: the table the reopened
database exposes denotes the pre-state bag unioned with the inserted row.

The only assumption beyond the executor's own success is the standard-library
UTF-8 law, which is the same hypothesis the whole-file codec theorem carries. -/
theorem insert_bytes_reopen_denotes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next : Core.State} {tableName : String} {values : List Core.Value}
    {result : Core.Result} {image : CoreFile.Image} {reopened : Core.Database}
    (success : Core.execute state (.insert tableName values) = .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image)
    (reread : CoreDecode.decode image.fileBytes = some reopened) :
    ∃ table stored row,
      state.database.findTable? tableName = some table ∧
      table.createRow values = .ok row ∧
      reopened.findTable? tableName = some stored ∧
      stored.rows = Core.orderedUpsert row table.rows ∧
      tableDenotation stored.rows =
        KRelation.unionAll (tableDenotation table.rows)
          (KRelation.single (CoreReadSemantics.coreRow row)) := by
  have decoded := CoreWriteBytes.decode_encoded_database utf8 next.database image
    encoded
  have sameDatabase : reopened = next.database.canonicalize :=
    Option.some.inj (reread.symm.trans decoded)
  rcases Core.execute_insert_exact success with
    ⟨table, replacement, row, found, created, _valid, freshRowid, _declared,
      replacementRows, updatedFound, _snapshot, _changes, _frame⟩
  refine ⟨table, replacement.canonicalize, row, found, created, ?_, ?_, ?_⟩
  · rw [sameDatabase, canonicalize_findTable?, updatedFound]
    rfl
  · rw [Core.Table.canonicalize_rows]
    exact replacementRows
  · rw [Core.Table.canonicalize_rows, replacementRows]
    exact tableDenotation_orderedUpsert_fresh row table.rows
      (rows_pairwise table) freshRowid

/-- The read leg, in the bag algebra: a query run against the reopened database
denotes that query applied to the post-insert rows.  Composing this with
`insert_bytes_reopen_denotes` is the full write/bytes/reopen/read circuit, and
both ends are stated in `KRelation` rather than in list operations. -/
theorem insert_bytes_reopen_query_denotes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next readNext : Core.State} {tableName : String}
    {values : List Core.Value} {result readResult : Core.Result}
    {image : CoreFile.Image} {reopened : Core.Database} {query : Core.Query}
    (success : Core.execute state (.insert tableName values) = .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image)
    (reread : CoreDecode.decode image.fileBytes = some reopened)
    (queried : Core.execute { database := reopened } (.query tableName query) =
      .ok (readNext, readResult)) :
    ∃ table row,
      state.database.findTable? tableName = some table ∧
      table.createRow values = .ok row ∧
      RelationalAlgebra.ofList readResult.rows =
        CoreReadSemantics.queryDenotation query
          (Core.orderedUpsert row table.rows) := by
  rcases insert_bytes_reopen_denotes utf8 success encoded reread with
    ⟨table, stored, row, found, created, storedFound, storedRows, _denoted⟩
  rcases CoreReadSemantics.execute_query_denotes queried with
    ⟨readTable, readFound, _unchanged, denotes⟩
  have sameTable : readTable = stored :=
    Option.some.inj (readFound.symm.trans storedFound)
  refine ⟨table, row, found, created, ?_⟩
  rw [denotes, sameTable, storedRows]

/-- **The sentence version.** For an unfiltered, unordered, unlimited,
non-`DISTINCT` `SELECT`, the projection of the inserted row is literally one of
the rows the reopened database returns.

This is the observational statement the equational ones exist to support: the row
is not merely accounted for in a multiplicity function, it comes back out of the
file. -/
theorem insert_bytes_reopen_selects_row (utf8 : CoreDecode.UTF8Roundtrips)
    {state next readNext : Core.State} {tableName : String}
    {values : List Core.Value} {result readResult : Core.Result}
    {image : CoreFile.Image} {reopened : Core.Database} {query : Core.Query}
    (success : Core.execute state (.insert tableName values) = .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image)
    (reread : CoreDecode.decode image.fileBytes = some reopened)
    (queried : Core.execute { database := reopened } (.query tableName query) =
      .ok (readNext, readResult))
    (plain : query.predicate = none) (unordered : query.orderBy = [])
    (unlimited : query.limit = none) (duplicates : query.distinct = false) :
    ∃ table row,
      state.database.findTable? tableName = some table ∧
      table.createRow values = .ok row ∧
      query.columns.map row.value ∈ readResult.rows := by
  rcases insert_bytes_reopen_denotes utf8 success encoded reread with
    ⟨table, stored, row, found, created, storedFound, storedRows, _denoted⟩
  rcases Core.execute_query_exact queried with
    ⟨readTable, readFound, _unchanged, rowsEq⟩
  have sameTable : readTable = stored :=
    Option.some.inj (readFound.symm.trans storedFound)
  refine ⟨table, row, found, created, ?_⟩
  have selected : query.selectedRows stored.rows = stored.rows := by
    unfold Core.Query.selectedRows
    rw [plain, unordered, unlimited]
    simp [Core.selects]
  have projected : readResult.rows =
      stored.rows.map (fun candidate => query.columns.map candidate.value) := by
    rw [rowsEq, sameTable]
    unfold Core.Query.eval Core.Query.projectedRows
    rw [duplicates, selected]
    simp
  rw [projected]
  exact List.mem_map.mpr ⟨row, by
    rw [storedRows]
    exact Core.mem_orderedUpsert_self row table.rows, rfl⟩

/-! ## The same circuit, entered from SQL text at both ends

The theorems above start at a parsed `Core` command. G4's acceptance is stronger:
the loop should be reachable from a live write *text* and a live read *text*, so
that nothing in the statement presumes a parser step the executable does not
perform. The write leg is factored through `CoreEndToEnd.WriteEffect` so that the
same proof serves the command level and the text level.
-/

/-- The bytes-and-reopen legs, stated over the logical effect rather than over
`Core.execute`.  `WriteEffect (.insert ..)` is definitionally the insert
postcondition, so this is usable from `execute_write_exact` and from the SQL-text
`WriteTraceEffect` alike. -/
theorem writeEffect_insert_bytes_reopen_denotes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next : Core.State} {tableName : String} {values : List Core.Value}
    {result : Core.Result} {image : CoreFile.Image} {reopened : Core.Database}
    (effect : CoreEndToEnd.WriteEffect (.insert tableName values) state next result)
    (encoded : CorePageCodec.encodeBulk next.database = some image)
    (reread : CoreDecode.decode image.fileBytes = some reopened) :
    ∃ table stored row,
      state.database.findTable? tableName = some table ∧
      table.createRow values = .ok row ∧
      reopened.findTable? tableName = some stored ∧
      stored.rows = Core.orderedUpsert row table.rows ∧
      tableDenotation stored.rows =
        KRelation.unionAll (tableDenotation table.rows)
          (KRelation.single (CoreReadSemantics.coreRow row)) := by
  have decoded := CoreWriteBytes.decode_encoded_database utf8 next.database image
    encoded
  have sameDatabase : reopened = next.database.canonicalize :=
    Option.some.inj (reread.symm.trans decoded)
  obtain ⟨table, replacement, row, found, created, _valid, freshRowid, _declared,
    replacementRows, updatedFound, _snapshot, _changes, _frame⟩ := effect
  refine ⟨table, replacement.canonicalize, row, found, created, ?_, ?_, ?_⟩
  · rw [sameDatabase, canonicalize_findTable?, updatedFound]
    rfl
  · rw [Core.Table.canonicalize_rows]
    exact replacementRows
  · rw [Core.Table.canonicalize_rows, replacementRows]
    exact tableDenotation_orderedUpsert_fresh row table.rows
      (rows_pairwise table) freshRowid

/-- **The circuit, text to text.** A supported single-row `INSERT` text is
executed; the post-state is encoded to SQLite bytes; those bytes are decoded back
into a database; a supported `SELECT` text is executed against *that* database.
The rows it returns denote the query applied to the pre-insert table with the
inserted row added.

Every step is a live entry point: `CoreSQL.execute` on both ends,
`CorePageCodec.encodeBulk` and `CoreDecode.decode` in between. -/
theorem insertText_bytes_reopen_readText_denotes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next readNext : Core.State} {insertText readText tableName : String}
    {values : List Core.Value} {results : List Core.Result}
    {readResult : Core.Result} {image : CoreFile.Image} {reopened : Core.Database}
    {query : Core.Query}
    (supportedInsert : CoreSQLWriteText.SupportedInsertRowsText state insertText
      [.insert tableName values])
    (insertSuccess : CoreSQL.execute state insertText = .ok (next, results))
    (encoded : CorePageCodec.encodeBulk next.database = some image)
    (reread : CoreDecode.decode image.fileBytes = some reopened)
    (supportedRead : CoreSQLReadText.SupportedReadText { database := reopened }
      readText (.query tableName query))
    (readSuccess : CoreSQL.execute { database := reopened } readText =
      .ok (readNext, [readResult])) :
    ∃ table row,
      state.database.findTable? tableName = some table ∧
      table.createRow values = .ok row ∧
      RelationalAlgebra.ofList readResult.rows =
        CoreReadSemantics.queryDenotation query
          (Core.orderedUpsert row table.rows) := by
  have trace := CoreSQLWriteText.insertRows_trace_success supportedInsert
    insertSuccess
  -- A one-command trace forces the middle state to be the post-state, so the
  -- single `WriteEffect` is exactly the insert postcondition.
  cases trace with
  | cons effect tail =>
      cases tail with
      | nil _ =>
          rcases writeEffect_insert_bytes_reopen_denotes utf8 effect encoded
            reread with
            ⟨table, stored, row, found, created, storedFound, storedRows,
              _denoted⟩
          rcases CoreSQLReadText.executeText_read_refines supportedRead
            readSuccess with ⟨readTable, readFound, _unchanged, denotes⟩
          have sameTable : readTable = stored :=
            Option.some.inj (readFound.symm.trans storedFound)
          refine ⟨table, row, found, created, ?_⟩
          rw [denotes, sameTable, storedRows]

end CoreWriteSemantics
end SQLeanite
