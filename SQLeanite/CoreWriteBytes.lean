import SQLeanite.CorePageCodec
import SQLeanite.CoreChunkPageDelta

namespace SQLeanite
namespace CoreWriteBytes

/-!
# Logical write operations to SQLite bytes

These theorems compose the live Core executor's abstract postconditions with
the whole-file SQLite codec.  The left conjunct says what changed (including
the other-table frame condition); the right conjunct says that decoding the
produced bytes yields exactly that post-state.
-/

theorem decode_encoded_database (utf8 : CoreDecode.UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CorePageCodec.encodeBulk database = some image) :
    CoreDecode.decode image.fileBytes = some database.canonicalize :=
  CorePageCodec.decode_encodeBulk utf8 database image encoded

theorem execute_createTable_to_bytes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next : Core.State} {schema : Core.Schema} {result : Core.Result}
    {image : CoreFile.Image}
    (success : Core.execute state (.createTable schema) = .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image) :
    (∃ table,
      Core.emptyTable schema = .ok table ∧
      next.database.tables = table :: state.database.tables ∧
      next.database.findTable? schema.name = some table ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = {} ∧
      ∀ other, other ≠ schema.name →
        next.database.findTable? other = state.database.findTable? other) ∧
    CoreDecode.decode image.fileBytes = some next.database.canonicalize := by
  exact ⟨Core.execute_createTable_exact success,
    decode_encoded_database utf8 next.database image encoded⟩

theorem execute_createIndex_to_bytes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next : Core.State} {tableName : String} {index : Core.Index}
    {result : Core.Result} {image : CoreFile.Image}
    (success : Core.execute state (.createIndex tableName index) =
      .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image) :
    (∃ table replacement,
      state.database.findTable? tableName = some table ∧
      replacement.schema = table.schema ∧
      replacement.indexes = index :: table.indexes ∧
      replacement.rows = table.rows ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = {} ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other) ∧
    CoreDecode.decode image.fileBytes = some next.database.canonicalize := by
  exact ⟨Core.execute_createIndex_exact success,
    decode_encoded_database utf8 next.database image encoded⟩

theorem execute_insert_to_bytes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next : Core.State} {tableName : String} {values : List Core.Value}
    {result : Core.Result} {image : CoreFile.Image}
    (success : Core.execute state (.insert tableName values) =
      .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image) :
    (∃ table replacement row,
      state.database.findTable? tableName = some table ∧
      table.createRow values = .ok row ∧
      row.WellFormed table.schema ∧
      (∀ existing ∈ table.rows, existing.rowid.value ≠ row.rowid.value) ∧
      table.findDeclaredPrimary? row = none ∧
      replacement.rows = Core.orderedUpsert row table.rows ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes := 1 } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other) ∧
    CoreDecode.decode image.fileBytes = some next.database.canonicalize := by
  exact ⟨Core.execute_insert_exact success,
    decode_encoded_database utf8 next.database image encoded⟩

theorem execute_replace_to_bytes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next : Core.State} {tableName : String} {values : List Core.Value}
    {result : Core.Result} {image : CoreFile.Image}
    (success : Core.execute state (.replace tableName values) =
      .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image) :
    (∃ table replacement row,
      state.database.findTable? tableName = some table ∧
      table.createReplacementRow values = .ok row ∧
      replacement.rows = Core.orderedUpsert row table.rows ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes := 1 } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other) ∧
    CoreDecode.decode image.fileBytes = some next.database.canonicalize := by
  exact ⟨Core.execute_replace_exact success,
    decode_encoded_database utf8 next.database image encoded⟩

theorem execute_delete_to_bytes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next : Core.State} {tableName : String}
    {predicate : Option Core.Predicate} {result : Core.Result}
    {image : CoreFile.Image}
    (success : Core.execute state (.deleteWhere tableName predicate) =
      .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image) :
    (∃ table replacement,
      state.database.findTable? tableName = some table ∧
      replacement.rows = table.rows.filter
        (fun row => !Core.selects predicate row) ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes := table.rows.length - replacement.rows.length } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other) ∧
    CoreDecode.decode image.fileBytes = some next.database.canonicalize := by
  exact ⟨Core.execute_deleteWhere_exact success,
    decode_encoded_database utf8 next.database image encoded⟩

theorem execute_update_to_bytes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next : Core.State} {tableName : String}
    {assignments : List (Nat × Core.Value)} {predicate : Option Core.Predicate}
    {result : Core.Result} {image : CoreFile.Image}
    (success : Core.execute state
      (.updateWhere tableName assignments predicate) = .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image) :
    (∃ table replacement changes,
      state.database.findTable? tableName = some table ∧
      table.updateWhere assignments predicate = .ok (replacement, changes) ∧
      next.database.findTable? tableName = some replacement ∧
      next.transactionSnapshot = state.transactionSnapshot ∧
      result = { changes } ∧
      ∀ other, other ≠ tableName →
        next.database.findTable? other = state.database.findTable? other) ∧
    CoreDecode.decode image.fileBytes = some next.database.canonicalize := by
  exact ⟨Core.execute_updateWhere_exact success,
    decode_encoded_database utf8 next.database image encoded⟩

theorem execute_commit_to_bytes (utf8 : CoreDecode.UTF8Roundtrips)
    {state next : Core.State} {result : Core.Result} {image : CoreFile.Image}
    (success : Core.execute state .commit = .ok (next, result))
    (encoded : CorePageCodec.encodeBulk next.database = some image) :
    (state.transactionSnapshot.isSome = true ∧
      next.database = state.database ∧
      next.transactionSnapshot = none ∧ result = {} ∧
      ∀ tableName,
        next.database.findTable? tableName =
          state.database.findTable? tableName) ∧
    CoreDecode.decode image.fileBytes = some next.database.canonicalize := by
  exact ⟨Core.execute_commit_exact success,
    decode_encoded_database utf8 next.database image encoded⟩

/-- A successful localized construction represents its requested logical
database while retaining the exact old page-state endpoint. -/
theorem localized_state_represents_database
    {database : Core.Database} {pageState : CoreChunkPageState.State}
    {delta : CoreChunkPageDelta.StateDelta}
    (updated : CoreChunkPageDelta.updateState? pageState database =
      some delta) :
    delta.before = pageState ∧
      delta.after.database = database ∧
      delta.after.Represents database := by
  have endpoints := CoreChunkPageDelta.updateState?_endpoints updated
  exact ⟨endpoints.1, endpoints.2, by
    rw [← endpoints.2]
    exact delta.after.represents_self⟩

end CoreWriteBytes
end SQLeanite
