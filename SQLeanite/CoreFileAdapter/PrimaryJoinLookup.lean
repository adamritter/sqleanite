import SQLeanite.CoreFileAdapter.PreparePageDirectedIndexInsert
import SQLeanite.CorePageCodec.PageSourceRepresentsEncodeBulkIn

namespace SQLeanite
namespace CoreFileAdapter

/-- Physical inputs for a certified primary-key merge join.  The right table
is decoded once; the left side contains only rows at or below its greatest
key, obtained by separator-directed traversal. -/
structure PrimaryJoinLookup where
  leftSchema : Core.Schema
  rightSchema : Core.Schema
  leftCandidates : List Core.Row
  rightRows : List Core.Row
  bound : Option Core.Integer
  pagesRead : Nat

inductive IntegerIndexRouting (source : CoreDecode.PageSource)
    (fuel rootPage : Nat) (expected : List CoreDecode.IndexEntry) where
  | generated (certificate : CoreDecode.CertifiedIntegerIndex
      source fuel rootPage expected)
  | general (certificate : CoreDecode.CertifiedWideIntegerIndex
      source fuel rootPage expected)
  | text (certificate : CoreDecode.CertifiedWideTextIndex
      source fuel rootPage expected)
  | allValues (certificate : CoreDecode.CertifiedAllValueIndex
      source fuel rootPage expected)

def IntegerIndexRouting.valueEntries
    {source : CoreDecode.PageSource} {fuel rootPage : Nat}
    {expected : List CoreDecode.IndexEntry}
    (routing : IntegerIndexRouting source fuel rootPage expected)
    (target : Core.Value) : List CoreDecode.IndexEntry :=
  match routing with
  | .generated _certificate =>
      (CoreDecode.lookupIndexValueFrom source target fuel rootPage).getD []
  | .general certificate => certificate.valueEntries target
  | .text certificate => certificate.valueEntries target
  | .allValues certificate => certificate.valueEntries target

theorem IntegerIndexRouting.valueEntries_exact
    {source : CoreDecode.PageSource} {fuel rootPage : Nat}
    {expected : List CoreDecode.IndexEntry}
    (routing : IntegerIndexRouting source fuel rootPage expected)
    (target : Core.Value) :
    routing.valueEntries target =
      expected.filter (fun entry => entry.matchesValue target) := by
  cases routing with
  | generated certificate =>
      simp [IntegerIndexRouting.valueEntries,
        CoreDecode.lookupIndexValueFrom_certified_exact certificate target]
  | general certificate => exact certificate.valueEntries_exact target
  | text certificate => exact certificate.valueEntries_exact target
  | allValues certificate => exact certificate.valueEntries_exact target

def IntegerIndexRouting.rangeEntries
    {source : CoreDecode.PageSource} {fuel rootPage : Nat}
    {expected : List CoreDecode.IndexEntry}
    (routing : IntegerIndexRouting source fuel rootPage expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    List CoreDecode.IndexEntry :=
  match routing with
  | .generated _certificate =>
      (CoreDecode.lookupIndexRangeFrom source operation target fuel rootPage)
        |>.getD []
  | .general certificate => certificate.rangeEntries operation target
  | .text certificate => certificate.rangeEntries operation target
  | .allValues certificate => certificate.rangeEntries operation target

theorem IntegerIndexRouting.rangeEntries_exact
    {source : CoreDecode.PageSource} {fuel rootPage : Nat}
    {expected : List CoreDecode.IndexEntry}
    (routing : IntegerIndexRouting source fuel rootPage expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    routing.rangeEntries operation target =
      expected.filter (fun entry => entry.matchesRange operation target) := by
  cases routing with
  | generated certificate =>
      simp [IntegerIndexRouting.rangeEntries,
        CoreDecode.lookupIndexRangeFrom_certified_exact certificate operation
          target]
  | general certificate => exact certificate.rangeEntries_exact operation target
  | text certificate => exact certificate.rangeEntries_exact operation target
  | allValues certificate => exact certificate.rangeEntries_exact operation target

/-- A certificate retained by a live connection.  Its dependent proof ties a
specific physical page source to the exact logical entries of `table/index`.
The connection invalidates these values on mutation until localized
certificate maintenance is implemented. -/
structure StoredIntegerIndex (database : Core.Database) where
  table : Core.Table
  tableMember : table ∈ database.tables
  index : Core.Index
  source : CoreDecode.PageSource
  fuel : Nat
  rootPage : Nat
  expected : List CoreDecode.IndexEntry
  expected_eq : expected = CoreDecode.expectedIndexEntries table index
  certificate : IntegerIndexRouting source fuel rootPage expected

/-- Rebind a physical index certificate to a newer logical table when the
exact abstract index entries are unchanged.  The dependent certificate itself
is reused: it names only the immutable page source and `expected` list. -/
def StoredIntegerIndex.retarget {before : Core.Database}
    (stored : StoredIntegerIndex before) (database : Core.Database)
    (table : Core.Table) (tableMember : table ∈ database.tables)
    (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) : StoredIntegerIndex database := {
  table
  tableMember
  index
  source := stored.source
  fuel := stored.fuel
  rootPage := stored.rootPage
  expected := stored.expected
  expected_eq := sameExpected.symm
  certificate := stored.certificate }

@[simp] theorem StoredIntegerIndex.retarget_expected
    {before : Core.Database} (stored : StoredIntegerIndex before)
    (database : Core.Database) (table : Core.Table)
    (tableMember : table ∈ database.tables) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) :
    (stored.retarget database table tableMember index sameExpected).expected =
      stored.expected := rfl

theorem StoredIntegerIndex.retarget_value_exact
    {before : Core.Database} (stored : StoredIntegerIndex before)
    (database : Core.Database) (table : Core.Table)
    (tableMember : table ∈ database.tables) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) (target : Core.Value) :
    (stored.retarget database table tableMember index sameExpected).certificate.valueEntries target =
      (CoreDecode.expectedIndexEntries table index).filter
        (fun entry => entry.matchesValue target) := by
  change stored.certificate.valueEntries target = _
  rw [stored.certificate.valueEntries_exact, sameExpected]

theorem StoredIntegerIndex.retarget_range_exact
    {before : Core.Database} (stored : StoredIntegerIndex before)
    (database : Core.Database) (table : Core.Table)
    (tableMember : table ∈ database.tables) (index : Core.Index)
    (sameExpected : CoreDecode.expectedIndexEntries table index =
      stored.expected) (operation : PhysicalQuery.Comparison)
    (target : Core.Value) :
    (stored.retarget database table tableMember index sameExpected).certificate.rangeEntries
        operation target =
      (CoreDecode.expectedIndexEntries table index).filter
        (fun entry => entry.matchesRange operation target) := by
  change stored.certificate.rangeEntries operation target = _
  rw [stored.certificate.rangeEntries_exact, sameExpected]

/-- Checked certificate maintenance for a localized table mutation.  Schema,
index identity and the complete logical index image must all agree. -/
def StoredIntegerIndex.retarget? {before : Core.Database}
    (stored : StoredIntegerIndex before) (database : Core.Database) :
    Option (StoredIntegerIndex database) :=
  match found : database.findTable? stored.table.schema.name with
  | none => none
  | some table =>
      have tableMember : table ∈ database.tables :=
        database.findTable?_mem found
      if _sameSchema : table.schema = stored.table.schema then
        match table.indexes.find? fun candidate =>
            candidate.name == stored.index.name with
        | none => none
        | some index =>
            if _sameIndex : index = stored.index then
              if sameExpected : CoreDecode.expectedIndexEntries table index =
                  stored.expected then
                some (stored.retarget database table tableMember index
                  sameExpected)
              else none
            else none
      else none

def retargetIntegerIndexCertificates
    {before : Core.Database}
    (certificates : List (StoredIntegerIndex before))
    (database : Core.Database) : List (StoredIntegerIndex database) :=
  certificates.filterMap fun stored => stored.retarget? database

def certifyIntegerIndexes (physicalPages : List (List UInt8))
    (catalog : List CoreDecode.CatalogEntry) (database : Core.Database) :
    List (StoredIntegerIndex database) :=
  let source := CoreDecode.PageSource.ofList physicalPages
  let fuel := physicalPages.length + 1
  database.tables.attach.flatMap fun attached =>
    let table := attached.val
    table.indexes.filterMap fun index =>
      match catalog.find? (fun entry =>
        entry.kind == "index" && entry.name == index.name &&
          entry.table == table.schema.name) with
      | none => none
      | some catalogEntry =>
          let expected := CoreDecode.expectedIndexEntries table index
          match CoreDecode.certifyIntegerIndex source fuel
              catalogEntry.rootPage expected with
          | none =>
              match CoreDecode.certifyWideIntegerIndex source fuel
                  catalogEntry.rootPage expected with
              | none =>
                  match CoreDecode.certifyWideTextIndex source fuel
                      catalogEntry.rootPage expected with
                  | none =>
                      match CoreDecode.certifyAllValueIndex source fuel
                          catalogEntry.rootPage expected with
                      | none => none
                      | some certificate =>
                          some ⟨table, attached.property, index, source, fuel,
                            catalogEntry.rootPage,
                            expected, rfl, .allValues certificate⟩
                  | some certificate =>
                      some ⟨table, attached.property, index, source, fuel,
                        catalogEntry.rootPage,
                        expected, rfl, .text certificate⟩
              | some certificate =>
                  some ⟨table, attached.property, index, source, fuel,
                    catalogEntry.rootPage,
                    expected, rfl, .general certificate⟩
          | some certificate =>
              some ⟨table, attached.property, index, source, fuel,
                catalogEntry.rootPage,
                expected, rfl, .generated certificate⟩

def loadIntegerIndexCertificates (paths : Paths) (database : Core.Database) :
    IO (List (StoredIntegerIndex database)) := do
  let input ← IO.FS.readBinFile paths.main
  let bytes := input.data.toList
  let some (header, _) := FileFormat.decodeDatabaseHeader bytes | return []
  let count := header.databaseSizePages.val
  unless input.size = count * PhysicalCodec.pageSize do return []
  let physicalPages := CoreDecode.pages count bytes
  let some catalog := physicalPages.head?.bind CoreDecode.decodeCatalog |
    return []
  return certifyIntegerIndexes physicalPages catalog database

def readTableSchema (paths : Paths) (tableName : String) (binaryOnly : Bool := false) :
    IO (Option Core.Schema) := do
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let some firstPage ← readPageBytes handle | return none
    let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
      return none
    let count := header.databaseSizePages.val
    unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
        header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
        metadata.byteSize.toNat = count * PhysicalCodec.pageSize do return none
    let some catalog := CoreDecode.decodeCatalog firstPage | return none
    let some entry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == tableName | return none
    let some sql := entry.sql | return none
    if binaryOnly && !CoreSchemaSQL.binaryCollations sql then return none
    let some schema := CoreDecode.parseTableSchema sql | return none
    if schema.name = tableName then return some schema else return none

/-- Cold, page-directed primary lookup with a generated-image miss
certificate.  The nested decoder result distinguishes malformed input from a
valid leaf miss.  A miss is exposed only when the parsed header carries the
stamp established by `CorePageCodec.encodeBulk_generatedHeader`; ordinary
SQLite writes invalidate its change-counter half.  Found rows remain usable
for general compatible SQLite files after their schema and row invariants are
checked locally. -/
def lookupPrimaryRowDecision (paths : Paths) (tableName : String)
    (rowid : Core.Integer) : IO (Option PrimaryLookupDecision) := do
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let some firstPage ← readPageBytes handle | return none
    let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
      return none
    let count := header.databaseSizePages.val
    unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
        header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
        metadata.byteSize.toNat = count * PhysicalCodec.pageSize do return none
    let some catalog := CoreDecode.decodeCatalog firstPage | return none
    let some entry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == tableName | return none
    let some sql := entry.sql | return none
    let some schema := CoreDecode.parseTableSchema sql | return none
    unless schema.name = tableName do return none
    let reads ← IO.mkRef 0
    let base := preadPageSource paths.main count
    let source : CoreDecode.IOPageSource := {
      pageCount := count
      readPage := fun pageNumber => do
        reads.modify (· + 1)
        base.readPage pageNumber }
    let some result ← CoreDecode.lookupTableRowidIOFrom schema source rowid
        (count + 1) entry.rootPage | return none
    match result with
    | some row =>
        unless row.rowid = rowid && row.WellFormed schema do return none
        return some ⟨schema, .found row, ← reads.get⟩
    | none =>
        unless CoreFile.hasGeneratedImageStamp header do return none
        return some ⟨schema, .generatedMissing, ← reads.get⟩

/-- Compatibility projection for callers interested only in successful hits.
Unlike `lookupPrimaryRowDecision`, this continues to collapse a valid miss. -/
def lookupPrimaryRow (paths : Paths) (tableName : String)
    (rowid : Core.Integer) : IO (Option PrimaryLookup) := do
  let some decision ← lookupPrimaryRowDecision paths tableName rowid |
    return none
  match decision.outcome with
  | .found row => return some ⟨decision.schema, row, decision.pagesRead⟩
  | .generatedMissing => return none

/-- Cold, separator-directed primary-key range lookup for a generated image.
The generated stamp supplies the encoder provenance needed by the pure
byte-level refinement theorem; rows are additionally checked against the
decoded schema and requested predicate before they cross the IO boundary. -/
def lookupGeneratedPrimaryRange (paths : Paths) (tableName : String)
    (schema : Core.Schema) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) : IO (Option IndexLookup) := do
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let some firstPage ← readPageBytes handle | return none
    let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
      return none
    let count := header.databaseSizePages.val
    unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
        header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
        metadata.byteSize.toNat = count * PhysicalCodec.pageSize &&
        CoreFile.hasGeneratedImageStamp header do return none
    let some catalog := CoreDecode.decodeCatalog firstPage | return none
    let some tableEntry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == tableName | return none
    let some tableSql := tableEntry.sql | return none
    let some decodedSchema := CoreDecode.parseTableSchema tableSql | return none
    unless decodedSchema = schema && schema.name = tableName do return none
    let reads ← IO.mkRef 0
    let base := preadPageSource paths.main count
    let source : CoreDecode.IOPageSource := {
      pageCount := count
      readPage := fun pageNumber => do
        reads.modify (· + 1)
        base.readPage pageNumber }
    let some candidates ← CoreDecode.lookupTableRangeIOFrom schema source
        operation target (count + 1) tableEntry.rootPage | return none
    unless candidates.all fun row =>
        row.WellFormed schema &&
          CoreDecode.tableRowMatchesRange operation target row do return none
    return some ⟨candidates, ← reads.get⟩

/-- Cold primary-key join acquisition for a stamped Lean-generated image.
Only the right table is decoded in full.  Its greatest rowid bounds an exact
separator-directed range read on the left; an empty right side avoids reading
the left tree altogether.  Local well-formedness checks keep malformed bytes
from crossing the IO boundary, while the generated stamp connects this path
to the encoder/range exactness theorems. -/
def lookupGeneratedPrimaryJoin (paths : Paths) (leftName rightName : String) :
    IO (Option PrimaryJoinLookup) := do
  IO.FS.withFile paths.main .read fun handle => do
    let metadata ← paths.main.metadata
    let some firstPage ← readPageBytes handle | return none
    let some (header, _) := FileFormat.decodeDatabaseHeader firstPage |
      return none
    let count := header.databaseSizePages.val
    unless header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize &&
        header.headerPrefix.reservedSpace = 0 && header.textEncoding.val = 1 &&
        metadata.byteSize.toNat = count * PhysicalCodec.pageSize &&
        CoreFile.hasGeneratedImageStamp header do return none
    let some catalog := CoreDecode.decodeCatalog firstPage | return none
    let some leftEntry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == leftName | return none
    let some rightEntry := catalog.find? fun entry =>
      entry.kind == "table" && entry.name == rightName | return none
    let some leftSql := leftEntry.sql | return none
    let some rightSql := rightEntry.sql | return none
    let some leftSchema := CoreDecode.parseTableSchema leftSql | return none
    let some rightSchema := CoreDecode.parseTableSchema rightSql | return none
    unless leftSchema.name = leftName && rightSchema.name = rightName do
      return none
    let reads ← IO.mkRef 0
    let base := preadPageSource paths.main count
    let source : CoreDecode.IOPageSource := {
      pageCount := count
      readPage := fun pageNumber => do
        reads.modify (· + 1)
        base.readPage pageNumber }
    let some rightRows ← CoreDecode.decodeSubtreeRowsIOFrom rightSchema source
        (count + 1) rightEntry.rootPage | return none
    if _rightWellFormed : Core.RowsWellFormed rightSchema rightRows then
      match rightRows.getLast? with
      | none =>
          return some ⟨leftSchema, rightSchema, [], rightRows, none, ← reads.get⟩
      | some last =>
          unless rightRows.all fun row =>
              decide (row.rowid.value ≤ last.rowid.value) do return none
          let some leftCandidates ← CoreDecode.lookupTableRangeIOFrom leftSchema
              source .lessEqual last.rowid (count + 1) leftEntry.rootPage |
            return none
          if _leftWellFormed :
              Core.RowsWellFormed leftSchema leftCandidates then
            unless leftCandidates.all fun row =>
                CoreDecode.tableRowMatchesRange .lessEqual last.rowid row do
              return none
            return some ⟨leftSchema, rightSchema, leftCandidates, rightRows,
              some last.rowid, ← reads.get⟩
          else return none
    else return none

inductive IndexLookupTarget where
  | equality (value : Core.Value)
  | range (operation : PhysicalQuery.Comparison) (value : Core.Value)

def rowidLe (left right : Core.Row) : Bool :=
  decide (left.rowid.value ≤ right.rowid.value)

def rowForIndexEntry? (table : Core.Table)
    (entry : CoreDecode.IndexEntry) : Option Core.Row :=
  table.findRowid? entry.rowid

/-- Resolve persisted index rowids through the proof-carrying primary tree.
The former implementation filtered every table row, making even a selective
index lookup O(table size).  Sorting only the returned rows restores the
table-order semantics required when SQL has no ORDER BY. -/
def rowsForIndexEntries (table : Core.Table)
    (entries : List CoreDecode.IndexEntry) : List Core.Row :=
  (entries.filterMap (rowForIndexEntry? table)).mergeSort rowidLe

theorem filterMap_expectedIndexEntries (table : Core.Table)
    (index : Core.Index) (rows : List Core.Row)
    (members : ∀ row ∈ rows, row ∈ table.rows)
    (keepEntry : CoreDecode.IndexEntry → Bool) (keepRow : Core.Row → Bool)
    (sameKeep : ∀ row ∈ rows,
      keepEntry ⟨row.value index.column, row.rowid⟩ = keepRow row) :
    (((rows.map fun row : Core.Row =>
        (⟨row.value index.column, row.rowid⟩ : CoreDecode.IndexEntry)).filter
      keepEntry).filterMap (rowForIndexEntry? table)) = rows.filter keepRow := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      have rowMember : row ∈ table.rows := members row (by simp)
      have tailMembers : ∀ candidate ∈ rows, candidate ∈ table.rows := by
        intro candidate member
        exact members candidate (by simp [member])
      have rowLookup : rowForIndexEntry? table
          ⟨row.value index.column, row.rowid⟩ = some row := by
        unfold rowForIndexEntry?
        exact Core.Table.findRowid?_eq_some_of_mem rowMember rfl
      have keep := sameKeep row (by simp)
      have tailKeep : ∀ candidate ∈ rows,
          keepEntry ⟨candidate.value index.column, candidate.rowid⟩ =
            keepRow candidate := by
        intro candidate member
        exact sameKeep candidate (by simp [member])
      cases kept : keepRow row <;>
        simp [keep, kept, rowLookup, induction tailMembers tailKeep]

end CoreFileAdapter

end SQLeanite
