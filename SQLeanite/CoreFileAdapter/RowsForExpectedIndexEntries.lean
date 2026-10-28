import SQLeanite.CoreFileAdapter.PrimaryJoinLookup

namespace SQLeanite
namespace CoreFileAdapter

theorem rowsForExpectedIndexEntries (table : Core.Table) (index : Core.Index)
    (keepEntry : CoreDecode.IndexEntry → Bool) (keepRow : Core.Row → Bool)
    (sameKeep : ∀ row ∈ CoreFile.sortedIndexRows table index,
      keepEntry ⟨row.value index.column, row.rowid⟩ = keepRow row) :
    rowsForIndexEntries table
        ((CoreDecode.expectedIndexEntries table index).filter keepEntry) =
      table.rows.filter keepRow := by
  have sortedMembers : ∀ row ∈ CoreFile.sortedIndexRows table index,
      row ∈ table.rows := by
    intro row member
    exact (CoreFile.sortedIndexRows_perm table index).subset member
  have resolved :
      (((CoreDecode.expectedIndexEntries table index).filter keepEntry).filterMap
        (rowForIndexEntry? table)) =
        (CoreFile.sortedIndexRows table index).filter keepRow := by
    exact filterMap_expectedIndexEntries table index
      (CoreFile.sortedIndexRows table index) sortedMembers keepEntry keepRow
      sameKeep
  have resolvedPerm :
      (((CoreDecode.expectedIndexEntries table index).filter keepEntry).filterMap
          (rowForIndexEntry? table)).Perm (table.rows.filter keepRow) := by
    rw [resolved]
    exact (CoreFile.sortedIndexRows_perm table index).filter keepRow
  let candidates :=
    ((CoreDecode.expectedIndexEntries table index).filter keepEntry).filterMap
      (rowForIndexEntry? table)
  have candidatePerm : (candidates.mergeSort rowidLe).Perm
      (table.rows.filter keepRow) :=
    (List.mergeSort_perm candidates rowidLe).trans resolvedPerm
  have rowidLeTrans : ∀ (left middle right : Core.Row),
      rowidLe left middle = true → rowidLe middle right = true →
        rowidLe left right = true := by
    intro left middle right leftMiddle middleRight
    simp only [rowidLe, decide_eq_true_eq] at leftMiddle middleRight ⊢
    omega
  have rowidLeTotal : ∀ (left right : Core.Row),
      (rowidLe left right || rowidLe right left) = true := by
    intro left right
    simp only [rowidLe, Bool.or_eq_true, decide_eq_true_eq]
    omega
  have candidatesSorted : (candidates.mergeSort rowidLe).Pairwise
      (fun left right => rowidLe left right = true) :=
    List.pairwise_mergeSort rowidLeTrans rowidLeTotal candidates
  have tableSorted : (table.rows.filter keepRow).Pairwise
      (fun left right => rowidLe left right = true) := by
    have strict := table.rowsWellFormed.2.filter keepRow
    exact strict.imp fun less => by
      simp only [rowidLe, decide_eq_true_eq]
      exact Int.le_of_lt less
  unfold rowsForIndexEntries
  change candidates.mergeSort rowidLe = table.rows.filter keepRow
  apply candidatePerm.eq_of_pairwise _ candidatesSorted tableSorted
  intro left right leftMember rightMember leftRight rightLeft
  have leftFiltered : left ∈ table.rows.filter keepRow :=
    candidatePerm.subset leftMember
  have leftTable : left ∈ table.rows := (List.mem_filter.mp leftFiltered).1
  have rightTable : right ∈ table.rows := (List.mem_filter.mp rightMember).1
  simp only [rowidLe, decide_eq_true_eq] at leftRight rightLeft
  have rowidValue : left.rowid.value = right.rowid.value :=
    Int.le_antisymm leftRight rightLeft
  have rowid : left.rowid = right.rowid :=
    FileFormat.SignedInteger.ext rowidValue
  have leftLookup := Core.Table.findRowid?_eq_some_of_mem leftTable rfl
  have rightLookup := Core.Table.findRowid?_eq_some_of_mem rightTable rfl
  rw [rowid] at leftLookup
  exact Option.some.inj (leftLookup.symm.trans rightLookup)

theorem rowsForExpectedValue_exact (table : Core.Table) (index : Core.Index)
    (target : Core.Value) :
    rowsForIndexEntries table
        ((CoreDecode.expectedIndexEntries table index).filter
          (fun entry => entry.matchesValue target)) =
      table.rows.filter
        (Core.selects (some (.equal index.column target))) := by
  apply rowsForExpectedIndexEntries table index
  intro row member
  simp [CoreDecode.IndexEntry.matchesValue, Core.selects,
    Core.Predicate.eval, Core.indexColumnMatches] <;> rfl

theorem rowsForExpectedRange_exact (table : Core.Table) (index : Core.Index)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    rowsForIndexEntries table
        ((CoreDecode.expectedIndexEntries table index).filter
          (fun entry => entry.matchesRange operation target)) =
      table.rows.filter
        (Core.selects (some (.compare operation index.column target))) := by
  apply rowsForExpectedIndexEntries table index
  intro row member
  simp [CoreDecode.IndexEntry.matchesRange, Core.selects,
    Core.Predicate.eval] <;> rfl

structure CertifiedCandidates (table : Core.Table) (query : Core.Query) where
  candidates : List Core.Row
  exact : query.eval candidates = query.eval table.rows

def CertifiedCandidates.result {table : Core.Table} {query : Core.Query}
    (certified : CertifiedCandidates table query) : Core.Result :=
  { rows := query.eval certified.candidates }

theorem CertifiedCandidates.result_exact {table : Core.Table}
    {query : Core.Query} (certified : CertifiedCandidates table query) :
    certified.result.rows = query.eval table.rows := by
  exact certified.exact

def certifiedEqualityCandidates {database : Core.Database}
    (stored : StoredIntegerIndex database)
    (table : Core.Table) (query : Core.Query) (target : Core.Value)
    (sameTable : stored.table = table)
    (predicateEqual : query.predicate =
      some (.equal stored.index.column target)) :
    CertifiedCandidates table query :=
  let entries := stored.certificate.valueEntries target
  let candidates := rowsForIndexEntries table entries
  have entriesEqual : entries = stored.expected.filter
      (fun entry => entry.matchesValue target) := by
    unfold entries
    exact stored.certificate.valueEntries_exact target
  have candidatesEqual : candidates = table.rows.filter
      (Core.selects query.predicate) := by
    unfold candidates
    have rowsEqual : stored.table.rows = table.rows :=
      congrArg Core.Table.rows sameTable
    have expectedCurrent : stored.expected =
        CoreDecode.expectedIndexEntries table stored.index := by
      rw [stored.expected_eq]
      simp [CoreDecode.expectedIndexEntries, CoreFile.sortedIndexRows,
        CoreFile.indexValuesInteger, CoreFile.indexValuesText,
        rowsEqual]
    rw [entriesEqual, expectedCurrent, rowsForExpectedValue_exact]
    rw [predicateEqual, ← rowsEqual]
  have narrowed : Core.indexedCandidates stored.index query.predicate
      table.rows = some candidates := by
    rw [predicateEqual]
    simp only [Core.indexedCandidates, ↓reduceIte]
    rw [candidatesEqual, predicateEqual]
  ⟨candidates, Core.Query.eval_indexed stored.index query table.rows candidates
    narrowed⟩

def certifiedRangeCandidates {database : Core.Database}
    (stored : StoredIntegerIndex database)
    (table : Core.Table) (query : Core.Query)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (sameTable : stored.table = table)
    (predicateEqual : query.predicate =
      some (.compare operation stored.index.column target)) :
    CertifiedCandidates table query :=
  let entries := stored.certificate.rangeEntries operation target
  let candidates := rowsForIndexEntries table entries
  have entriesEqual : entries = stored.expected.filter
      (fun entry => entry.matchesRange operation target) := by
    unfold entries
    exact stored.certificate.rangeEntries_exact operation target
  have candidatesEqual : candidates = table.rows.filter
      (Core.selects query.predicate) := by
    unfold candidates
    have rowsEqual : stored.table.rows = table.rows :=
      congrArg Core.Table.rows sameTable
    have expectedCurrent : stored.expected =
        CoreDecode.expectedIndexEntries table stored.index := by
      rw [stored.expected_eq]
      simp [CoreDecode.expectedIndexEntries, CoreFile.sortedIndexRows,
        CoreFile.indexValuesInteger, CoreFile.indexValuesText,
        rowsEqual]
    rw [entriesEqual, expectedCurrent, rowsForExpectedRange_exact]
    rw [predicateEqual, ← rowsEqual]
  have narrowed : Core.indexedCandidates stored.index query.predicate
      table.rows = some candidates := by
    rw [predicateEqual]
    simp only [Core.indexedCandidates, ↓reduceIte]
    rw [candidatesEqual, predicateEqual]
  ⟨candidates, Core.Query.eval_indexed stored.index query table.rows candidates
    narrowed⟩

def lookupCertifiedIndexCandidates {database : Core.Database}
    (certificates : List (StoredIntegerIndex database))
    (table : Core.Table) (tableMember : table ∈ database.tables)
    (query : Core.Query) :
    Option (CertifiedCandidates table query) :=
  match predicateResult : query.predicate with
  | some (.equal column target) =>
      match table.chooseAccessPath query.predicate with
      | .equalityIndex index =>
          if columnEqual : column = index.column then
            match storedResult : certificates.find? fun stored =>
                stored.table.schema.name == table.schema.name &&
                  stored.index.name == index.name with
            | none => none
            | some stored =>
                if indexEqual : stored.index = index then
                  have storedName : stored.table.schema.name =
                      table.schema.name := by
                    have selected := List.find?_some storedResult
                    simp only [Bool.and_eq_true, beq_iff_eq] at selected
                    exact selected.1
                  have sameTable : stored.table = table :=
                    database.table_eq_of_mem_of_name_eq stored.tableMember
                      tableMember storedName
                  have predicateEqual : query.predicate =
                      some (.equal stored.index.column target) := by
                    calc
                      query.predicate = some (.equal column target) :=
                        predicateResult
                      _ = some (.equal stored.index.column target) := by
                        simp [indexEqual, columnEqual]
                  some (certifiedEqualityCandidates stored table query target
                    sameTable predicateEqual)
                else none
          else none
      | _ => none
  | some (.compare operation column target) =>
      match table.chooseAccessPath query.predicate with
      | .rangeIndex index =>
          if columnEqual : column = index.column then
            match storedResult : certificates.find? fun stored =>
                stored.table.schema.name == table.schema.name &&
                  stored.index.name == index.name with
            | none => none
            | some stored =>
                if indexEqual : stored.index = index then
                  have storedName : stored.table.schema.name =
                      table.schema.name := by
                    have selected := List.find?_some storedResult
                    simp only [Bool.and_eq_true, beq_iff_eq] at selected
                    exact selected.1
                  have sameTable : stored.table = table :=
                    database.table_eq_of_mem_of_name_eq stored.tableMember
                      tableMember storedName
                  have predicateEqual : query.predicate =
                      some (.compare operation stored.index.column target) := by
                    calc
                      query.predicate =
                          some (.compare operation column target) :=
                        predicateResult
                      _ = some (.compare operation stored.index.column target) := by
                        simp [indexEqual, columnEqual]
                  some (certifiedRangeCandidates stored table query operation
                    target sameTable predicateEqual)
                else none
          else none
      | _ => none
  | _ => none

/-- Page count and catalog for a validated main file.

Used by the persisted-index lookup below, which reads the catalog and only
value-compatible index branches; returned rowids are projected back into table
order so queries without ORDER BY retain Core's observable list semantics.
Unsupported query shapes return `none`.

Split out of `lookupIndexCandidates` so a connection can decode it once instead
of once per statement. Reading page zero and decoding the header and catalog is
per-query fixed cost that does not change until a write, and writes already
invalidate the connection's caches. -/
structure FileGeometry where
  pageCount : Nat
  catalog : List CoreDecode.CatalogEntry

/-- Header/catalog facts checked once for a read-only batch over a stamped
Lean-generated image.  Reusing this value does not cache mutable table pages;
it only removes repeated file opens and repeated catalog decoding while the
outer process lock keeps the batch image stable. -/
structure GeneratedFileGeometry where
  pageCount : Nat
  catalog : List CoreDecode.CatalogEntry
  schemas : List (String × Core.Schema)

def readGeneratedFileGeometry (paths : Paths) :
    IO (Option GeneratedFileGeometry) := do
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
    let schemas := catalog.filterMap fun entry =>
      if entry.kind == "table" then do
        let sql ← entry.sql
        let schema ← CoreDecode.parseTableSchema sql
        if schema.name = entry.name then some (entry.name, schema) else none
      else none
    return some ⟨count, catalog, schemas⟩

def GeneratedFileGeometry.tableSchema? (geometry : GeneratedFileGeometry)
    (tableName : String) : Option Core.Schema := do
  let entry ← geometry.schemas.find? fun entry => entry.1 == tableName
  some entry.2

/-- Primary-key counterpart of the generated secondary-index reader. The
caller retains the generated geometry and bounded byte-page cache for one
immutable, process-locked read batch. Use the same routed byte reader already
used to resolve secondary-index rowids: it decodes the selected record rather
than every record in its leaf. Foreign images continue through
`lookupPrimaryRowDecision`, including its full local decoding checks.

Neither geometry nor cache may be reused across a write. A malformed routed
page or an invalid selected row is an optimization miss, not a successful
empty result. Only a valid leaf miss returns `some none`. -/
def lookupGeneratedPrimaryRowWith (geometry : GeneratedFileGeometry)
    (paths : Paths) (tableName : String) (schema : Core.Schema)
    (cache : PageReadCache) (target : Core.Integer) :
    IO (Option (Option Core.Row)) := do
  let some tableEntry := geometry.catalog.find? fun entry =>
    entry.kind == "table" && entry.name == tableName | return none
  let some decodedSchema := geometry.tableSchema? tableName | return none
  unless decodedSchema = schema do return none
  let source := preadPageSourceCached paths.main geometry.pageCount cache
  let some result ← lookupTableRowidBytesCached paths.main schema source cache
      target (geometry.pageCount + 1) tableEntry.rootPage | return none
  match result with
  | none => return some none
  | some row =>
      unless row.rowid = target && row.WellFormed schema do return none
      return some (some row)

/-- Validate the header and decode the catalog. The header checks are exactly
those `lookupIndexCandidates` performed inline, so a cached geometry carries the
same premises a fresh read would. -/
def readFileGeometry (paths : Paths) : IO (Option FileGeometry) := do
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
    return some ⟨count, catalog⟩

/-- The index selected by a query's predicate, or `none` for shapes this path
does not serve. -/
private def selectedIndexTarget (table : Core.Table) (query : Core.Query) :
    Option (Core.Index × IndexLookupTarget) :=
  match query.predicate, table.chooseAccessPath query.predicate with
  | some (.equal column target), .equalityIndex index =>
      if column = index.column then
        some (index, IndexLookupTarget.equality target)
      else none
  | some (.compare operation column target), .rangeIndex index =>
      if column = index.column then
        some (index, IndexLookupTarget.range operation target)
      else none
  | _, _ => none

/-- Index lookup against an already-decoded geometry. -/
def lookupIndexCandidatesWith (geometry : FileGeometry) (paths : Paths)
    (table : Core.Table) (query : Core.Query) : IO (Option IndexLookup) := do
  let some (index, target) := selectedIndexTarget table query | return none
  let some entry := geometry.catalog.find? fun entry =>
    entry.kind == "index" && entry.name == index.name &&
      entry.table == table.schema.name | return none
  let count := geometry.pageCount
  let reads ← IO.mkRef 0
  let base := preadPageSource paths.main count
  let source : CoreDecode.IOPageSource := {
    pageCount := count
    readPage := fun pageNumber => do
      reads.modify (· + 1)
      base.readPage pageNumber }
  let entries ← match target with
    | .equality value =>
        CoreDecode.lookupIndexValueIOFrom source value
          (count + 1) entry.rootPage
    | .range operation value =>
        CoreDecode.lookupIndexRangeIOFrom source operation value
          (count + 1) entry.rootPage
  let some entries := entries | return none
  let candidates := rowsForIndexEntries table entries
  return some ⟨candidates, ← reads.get⟩

def lookupIndexCandidates (paths : Paths) (table : Core.Table)
    (query : Core.Query) : IO (Option IndexLookup) := do
  let some geometry ← readFileGeometry paths | return none
  lookupIndexCandidatesWith geometry paths table query

/-- Recognize exactly the two index-catalog shapes emitted by the certified
encoder. Explicit indexes carry the canonical proof marker in their SQL text;
SQLite's required automatic index for a non-aliasing primary key has NULL SQL,
so its certificate is instead the canonical name/column pair derived from the
decoded table schema. The generated-image stamp remains the outer provenance
gate for both cases. -/
def generatedIndexEntryMatches (schema : Core.Schema)
    (tableName : String) (column : Nat) (columnName : String)
    (entry : CoreDecode.CatalogEntry) : Bool :=
  entry.kind == "index" && entry.table == tableName &&
    match entry.sql with
    | some sql =>
        match CanonicalIndexSQL.parseGeneratedCertified sql with
        | some spec => spec.name == entry.name && spec.table == tableName &&
            spec.column == columnName
        | none => false
    | none =>
        Core.Index.isImplicitPrimary schema { name := entry.name, column }

/-- Cold secondary-index lookup for a stamped image emitted by the proved
encoder. The exact canonical catalog suffix records the INTEGER-only premise
of `lookupIndexValueFrom_encodeIndex_exact` and
`lookupIndexRangeFrom_encodeIndex_exact`. Only selected index branches and
the corresponding primary-tree paths are read; every returned rowid/value
link is checked locally before it reaches SQL evaluation. -/
def lookupGeneratedIndexCandidatesWith (geometry : GeneratedFileGeometry)
    (paths : Paths) (tableName : String)
    (schema : Core.Schema) (query : Core.Query)
    (cache : Option PageReadCache := none) : IO (Option IndexLookup) := do
  let selected := match query.predicate with
    | some (.equal column target) =>
        some (column, IndexLookupTarget.equality target)
    | some (.compare operation column target) =>
        some (column, IndexLookupTarget.range operation target)
    | _ => none
  let some (column, target) := selected | return none
  let some columnSpec := schema.columns[column]? | return none
  let count := geometry.pageCount
  let some tableEntry := geometry.catalog.find? fun entry =>
    entry.kind == "table" && entry.name == tableName | return none
  let some decodedSchema := geometry.tableSchema? tableName | return none
  unless decodedSchema = schema do return none
  let some indexEntry := geometry.catalog.find? (generatedIndexEntryMatches schema
    tableName column columnSpec.name) | return none
  let reads ← IO.mkRef 0
  let base := match cache with
    | some cache => preadPageSourceCached paths.main count cache
    | none => preadPageSource paths.main count
  let source : CoreDecode.IOPageSource := {
    pageCount := count
    readPage := fun pageNumber => do
      reads.modify (· + 1)
      base.readPage pageNumber }
  let entries ← match target with
    | .equality value =>
        match cache with
        | some cache =>
            CoreDecode.lookupIndexValueDecodedWith
              (decodedIndexPageCached cache source) value
              (count + 1) indexEntry.rootPage
        | none =>
            CoreDecode.lookupIndexValueIOFrom source value (count + 1)
              indexEntry.rootPage
    | .range operation value =>
        CoreDecode.lookupIndexRangeIOFrom source operation value
          (count + 1) indexEntry.rootPage
  let some entries := entries | return none
  let mut candidates := []
  for entry in entries do
    let resolve : IO (Option (Option Core.Row)) := match cache with
      | some retained =>
          lookupTableRowidBytesCached paths.main schema source retained
            entry.rowid (count + 1) tableEntry.rootPage
      | none =>
          CoreDecode.lookupTableRowidTargetIOFrom schema source entry.rowid
            (count + 1) tableEntry.rootPage
    let resolved ← resolve
    let some resolved := resolved | return none
    let some row := resolved | return none
    unless row.rowid = entry.rowid && row.WellFormed schema &&
        row.value column = entry.value do return none
    candidates := row :: candidates
  return some ⟨candidates.mergeSort rowidLe, ← reads.get⟩

end CoreFileAdapter

end SQLeanite
