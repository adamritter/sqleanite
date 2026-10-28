import SQLeanite.CoreTextEncoding
import SQLeanite.CoreAutomaticIndex
import SQLeanite.CoreDecode.LookupTableRangeIOFrom
import SQLeanite.CoreDecode.RestoreCanonicalIndexesFixed
import SQLeanite.CoreIndexPrepare
import SQLeanite.CoreDecode.AuxiliaryIndexes

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem validateCanonicalIndexGroupsFrom_encodeOverflowIndexTableGroups
    (source : PageSource) :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreOverflow.IndexEncoding)
      (suffix : List CatalogEntry),
      Core.TablesWellFormed tables →
      (∀ entry ∈ suffix, ∀ table ∈ tables,
        entry.table ≠ table.schema.name) →
      CoreOverflow.encodeIndexTableGroups nextPage tables = some encodings →
      (∀ encoding ∈ encodings,
        ReadsPagesFrom source encoding.rootPage encoding.pages) →
      (∀ encoding ∈ encodings, 0 < encoding.rootPage) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length < 2 ^ 32) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length ≤ source.pageCount + 1) →
      validateCanonicalIndexGroupsFrom source
        (tables.map Core.Table.withoutIndexes)
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some suffix
  | _, [], encodings, suffix, _, _, encoded, _, _, _, _ => by
      simp only [CoreOverflow.encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, suffix, wellFormed, boundary,
      encoded, reads, positive, pageBound, sourceBound => by
      simp only [Core.TablesWellFormed, Core.namesUnique, List.map_cons,
        List.pairwise_cons] at wellFormed
      rcases wellFormed with ⟨headDistinct, tailWellFormed⟩
      simp only [CoreOverflow.encodeIndexTableGroups,
        Option.bind_eq_bind, Option.bind] at encoded
      cases currentResult : CoreOverflow.encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : CoreOverflow.encodeIndexTableGroups
            (nextPage + (CoreOverflow.indexPagesOf current).length) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult, Option.some.injEq] at encoded
          subst encodings
          simp only [List.map_cons, List.map_append, List.append_assoc]
          unfold validateCanonicalIndexGroupsFrom
          have remainingBelongs := CoreOverflow.encodeIndexTableGroups_tables
            remainingResult
          have currentBoundary : ∀ entry ∈
              (remaining.map (fun encoding =>
                CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix),
              entry.table ≠ table.schema.name := by
            intro entry member
            simp only [List.mem_append] at member
            rcases member with encodedMember | suffixMember
            · rcases List.mem_map.mp encodedMember with
                ⟨encoding, encodingMember, equal⟩
              subst entry
              have tableMember := remainingBelongs encoding encodingMember
              have distinct := headDistinct encoding.table.schema.name
                (List.mem_map_of_mem tableMember)
              simpa [CoreOverflow.IndexEncoding.catalogEntry,
                CatalogEntry.ofEncoded] using distinct.symm
            · exact boundary entry suffixMember table (by simp)
          rw [validateCanonicalIndexesForTableFrom_encodeOverflowIndexes
            source table nextPage table.indexes current
            (remaining.map (fun encoding =>
              CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix)
            (by simp) currentBoundary currentResult
            (fun encoding member => reads encoding (by simp [member]))
            (fun encoding member => positive encoding (by simp [member]))
            (fun encoding member => pageBound encoding (by simp [member]))
            (fun encoding member => sourceBound encoding (by simp [member]))]
          have tailBoundary : ∀ entry ∈ suffix, ∀ candidate ∈ tables,
              entry.table ≠ candidate.schema.name := by
            intro entry entryMember candidate candidateMember
            exact boundary entry entryMember candidate (by simp [candidateMember])
          exact validateCanonicalIndexGroupsFrom_encodeOverflowIndexTableGroups
            source (nextPage + (CoreOverflow.indexPagesOf current).length)
            tables remaining suffix tailWellFormed tailBoundary remainingResult
            (fun encoding member => reads encoding (by simp [member]))
            (fun encoding member => positive encoding (by simp [member]))
            (fun encoding member => pageBound encoding (by simp [member]))
            (fun encoding member => sourceBound encoding (by simp [member]))

theorem validateCanonicalIndexesFrom_overflowEncoded
    (source : PageSource) (database : Core.Database) (nextPage : Nat)
    (encodings : List CoreOverflow.IndexEncoding)
    (encoded : CoreOverflow.encodeIndexTableGroups nextPage database.tables =
      some encodings)
    (reads : ∀ encoding ∈ encodings,
      ReadsPagesFrom source encoding.rootPage encoding.pages)
    (positive : ∀ encoding ∈ encodings, 0 < encoding.rootPage)
    (pageBound : ∀ encoding ∈ encodings,
      encoding.rootPage + encoding.pages.length < 2 ^ 32)
    (sourceBound : ∀ encoding ∈ encodings,
      encoding.rootPage + encoding.pages.length ≤ source.pageCount + 1) :
    validateCanonicalIndexesFrom source
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CatalogEntry.ofEncoded encoding.catalogEntry)) = some () := by
  unfold validateCanonicalIndexesFrom
  have validated :=
    validateCanonicalIndexGroupsFrom_encodeOverflowIndexTableGroups source
    nextPage database.tables encodings [] database.tablesWellFormed (by simp)
      encoded reads positive pageBound sourceBound
  simp only [List.append_nil] at validated
  rw [validated]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]

/-- Recover only index metadata. Empty SQL and NULL both denote an automatic
primary index; every other entry must describe one supported CREATE INDEX. -/
def indexMetadata (database : Core.Database) (entry : CatalogEntry) :
    Option (Core.Table × Core.Index) := do
  if entry.kind != "index" then none else do
    let table ← CoreNames.table? database entry.table
    if table.withoutRowid then none else do
     let index ← match entry.sql with
       | none => (CoreAutomaticIndex.find table entry.name).orElse fun _ =>
           decodeCanonicalIndex table.schema table.schema.name { entry with table := table.schema.name }
       | some sql =>
           if sql.isEmpty then
             (CoreAutomaticIndex.find table entry.name).orElse fun _ =>
               decodeCanonicalIndex table.schema table.schema.name
                 { entry with table := table.schema.name, sql := none }
           else do
             let spec ← (CanonicalIndexSQL.parse sql).orElse fun _ => CoreSchemaSQL.indexSpec sql
             if spec.name.toLower != entry.name.toLower ||
                 spec.table.toLower != entry.table.toLower then none else do
               let available ← (CoreIndexPrepare.prepareCreateIndex { database } entry.name false).toOption
               if !available then none else do
                 unless (← (CoreIndexPrepare.columnCollation table spec.column).toOption).toLower == "binary" do none
                 let column ← (CoreIndexPrepare.indexColumn table.schema spec.column).toOption
                 some ⟨entry.name, column, spec.unique⟩
     some (table, index)


/-- SQLite may store integral REAL values with an INTEGER serial type. Apply
only the column's read conversion; write affinity would hide corrupt types. -/
def readIndexEntry (column : Core.Column) (entry : IndexEntry) : IndexEntry :=
  { entry with value := SQLite.PhysicalAffinity.read column.affinity entry.value }

@[simp] theorem readIndexEntry_rowid (column : Core.Column) (entry : IndexEntry) :
    (readIndexEntry column entry).rowid = entry.rowid := rfl

theorem readIndexEntry_accepted (column : Core.Column) (entry : IndexEntry)
    (accepted : Core.columnAcceptsBool column entry.value = true) :
    readIndexEntry column entry = entry := by
  simp [readIndexEntry, Core.columnRead_eq_self accepted]

/-- Both pure and IO acquisition pass through this exact content check before
index metadata can be attached. It preserves record order and physical rowids. -/
def checkedIndex (table : Core.Table) (index : Core.Index)
    (physical : List IndexEntry) : Option Core.Table := do
  let column ← table.schema.columns[index.column]?
  if physical.map (readIndexEntry column) = expectedIndexEntries table index then
    (table.addIndex index).toOption
  else none

theorem checkedIndex_contents {table updated : Core.Table} {index : Core.Index}
    {physical : List IndexEntry}
    (checked : checkedIndex table index physical = some updated) :
    ∃ column, table.schema.columns[index.column]? = some column ∧
      physical.map (readIndexEntry column) = expectedIndexEntries table index := by
  unfold checkedIndex at checked
  cases found : table.schema.columns[index.column]? with
  | none => simp [found] at checked
  | some column =>
      simp only [found, Option.bind_eq_bind, Option.bind] at checked
      split at checked
      next contentsEqual => exact ⟨column, rfl, contentsEqual⟩
      next => simp at checked

def applyIndexFrom (source : PageSource) (database : Core.Database)
    (entry : CatalogEntry) : Option Core.Database := do
  if entry.kind = "index" then
    match indexMetadata database entry with
    | some (table,index) => do
        let physical ← decodeIndexSubtreeFrom source (source.pageCount + 1) entry.rootPage
        let updated ← checkedIndex table index physical
        (database.updateTable updated).toOption
    | none => do
        let prepared ← filteredIndexMetadata database entry
        if prepared.table.withoutRowid then
          let physical ← IndexRecords.valuesFrom source (source.pageCount + 1) entry.rootPage
          unless checkedWithoutRowidIndex prepared physical do none
        else
          let physical ← IndexRecords.subtreeFrom source (source.pageCount + 1) entry.rootPage
          unless checkedFilteredIndex prepared physical do none
        some database
  else some database

/-- Process catalog entries in creation order, matching Table.addIndex and
SQLite's reverse creation-order planner list across opens and live CREATEs. -/
def applyIndexesFromSeen (source : PageSource) :
    Core.Database → List CatalogEntry → List String → Option Core.Database
  | database, [], _ => some database
  | database, entry :: entries, seen => do
      let names := if entry.kind == "index" then [entry.name.toLower] else []
      unless names.all (fun name => !seen.contains name) do none
      let database ← applyIndexFrom source database entry
      applyIndexesFromSeen source database entries (names ++ seen)

def applyIndexesFrom (source : PageSource) (database : Core.Database)
    (entries : List CatalogEntry) : Option Core.Database :=
  applyIndexesFromSeen source database entries []

/-- Generated images take the proof-oriented path: validate every physical
index once, then reconstruct all metadata in one structurally recursive pass.
The general updater remains the compatibility fallback for externally-created
SQLite files and non-canonical catalog layouts. -/
def applyIndexesForOpen (source : PageSource) (database : Core.Database)
    (entries : List CatalogEntry) : Option Core.Database :=
  match validateCanonicalIndexesFrom source database.tables entries with
  | some () => rebuildCanonicalDatabase database.tables entries
  | none => applyIndexesFrom source database entries

theorem applyIndexesForOpen_overflowEncoded
    (source : PageSource) (database : Core.Database) (nextPage : Nat)
    (encodings : List CoreOverflow.IndexEncoding)
    (encoded : CoreOverflow.encodeIndexTableGroups nextPage database.tables =
      some encodings)
    (reads : ∀ encoding ∈ encodings,
      ReadsPagesFrom source encoding.rootPage encoding.pages)
    (positive : ∀ encoding ∈ encodings, 0 < encoding.rootPage)
    (pageBound : ∀ encoding ∈ encodings,
      encoding.rootPage + encoding.pages.length < 2 ^ 32)
    (sourceBound : ∀ encoding ∈ encodings,
      encoding.rootPage + encoding.pages.length ≤ source.pageCount + 1) :
    applyIndexesForOpen source database.withoutIndexes
      (encodings.map (fun encoding =>
        CatalogEntry.ofEncoded encoding.catalogEntry)) =
          some database.canonicalize := by
  unfold applyIndexesForOpen
  have validated := validateCanonicalIndexesFrom_overflowEncoded source
    database nextPage encodings encoded reads positive pageBound sourceBound
  change validateCanonicalIndexesFrom source
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CatalogEntry.ofEncoded encoding.catalogEntry)) = some () at validated
  simp only [Core.Database.withoutIndexes]
  rw [validated]
  exact rebuildCanonicalDatabase_overflowEncoded database nextPage encodings
    encoded

def applyIndexes (physicalPages : List (List UInt8))
    (database : Core.Database) (entries : List CatalogEntry) :
    Option Core.Database :=
  applyIndexesFrom (.ofList physicalPages) database entries

theorem applyIndexes_ofList (physicalPages : List (List UInt8))
    (database : Core.Database) (entries : List CatalogEntry) :
    applyIndexesFrom (.ofList physicalPages) database entries =
      applyIndexes physicalPages database entries := rfl


/-- Foreign UTF-16 physical order is checked in its actual BINARY byte
representation. The Core memory index remains its ordinary logical index. -/
def encodedIndexEntries (encoding : Nat) (table : Core.Table) (index : Core.Index) : List IndexEntry :=
  let kind := SQLite.Collation.forEncoding encoding .binary
  (expectedIndexEntries table index).mergeSort fun left right =>
    let order := SQLite.Collation.compareValue kind left.value right.value
    order == .lt || (order == .eq && decide (left.rowid.value ≤ right.rowid.value))


theorem encodedIndexEntries_perm (encoding : Nat) (table : Core.Table) (index : Core.Index) :
    (encodedIndexEntries encoding table index).Perm (expectedIndexEntries table index) := by
  exact List.mergeSort_perm _ _


def checkedEncodedIndex (encoding : Nat) (table : Core.Table) (index : Core.Index)
    (physical : List IndexEntry) : Option Core.Table := do
  if encoding ≤ 1 then return ← checkedIndex table index physical
  let column ← table.schema.columns[index.column]?
  unless physical.map (readIndexEntry column) == encodedIndexEntries encoding table index do none
  (table.addIndex index).toOption


theorem checkedEncodedIndex_utf8 (table : Core.Table) (index : Core.Index) (physical : List IndexEntry) :
    checkedEncodedIndex 1 table index physical = checkedIndex table index physical := by
  simp [checkedEncodedIndex]

def applyIndexIOFrom (source : IOPageSource) (database : Core.Database)
    (entry : CatalogEntry) : IO (Option Core.Database) := do
  if entry.kind = "index" then
    match indexMetadata database entry with
    | some (table,index) =>
        let some physical ← decodeIndexSubtreeIOFrom source
          (source.pageCount + 1) entry.rootPage | return none
        let some updated := checkedEncodedIndex source.textEncoding table index physical | return none
        return (database.updateTable updated).toOption
    | none =>
        unless source.textEncoding == 1 do return none
        let some prepared := filteredIndexMetadata database entry | return none
        if prepared.table.withoutRowid then
          let some physical ← IndexRecords.valuesIOFrom source (source.pageCount + 1) entry.rootPage | return none
          unless checkedWithoutRowidIndex prepared physical do return none
        else
          let some physical ← IndexRecords.subtreeIOFrom source (source.pageCount + 1) entry.rootPage | return none
          unless checkedFilteredIndex prepared physical do return none
        return some database
  else return some database

def applyIndexesIOFromSeen (source : IOPageSource) :
    Core.Database → List CatalogEntry → List String → IO (Option Core.Database)
  | database, [], _ => pure (some database)
  | database, entry :: entries, seen => do
      let names := if entry.kind == "index" then [entry.name.toLower] else []
      unless names.all (fun name => !seen.contains name) do return none
      let some database ← applyIndexIOFrom source database entry | return none
      applyIndexesIOFromSeen source database entries (names ++ seen)

def applyIndexesIOFrom (source : IOPageSource) (database : Core.Database)
    (entries : List CatalogEntry) : IO (Option Core.Database) :=
  applyIndexesIOFromSeen source database entries []

/-- The schema table uses the ordinary table B-tree format, including the
100-byte database header on root page one and payload overflow chains. -/
inductive CatalogPage where
  | branch (children : List Nat)
  | leaf (cells : List (List UInt8))

def catalogPage? (pageSize pageNumber : Nat) (page : List UInt8) : Option CatalogPage := do
  if page.length != pageSize then none else do
    let headerOffset := if pageNumber == 1 then 100 else 0
    let (header, afterHeader) ← decodeBTreePageHeader (page.drop headerOffset)
    match header with
    | .interiorTable common rightmost =>
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        let children ← offsets.mapM fun offset => do
          if offset < headerOffset + 12 + 2 * common.cellCount.val || offset ≥ page.length then none
          else do
            let (cell, _) ← decodeInteriorTableCell (page.drop offset)
            some cell.leftChildPage.value.val
        some (.branch (children ++ [rightmost.val]))
    | .leafTable common =>
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        if offsets.all (fun offset => headerOffset + 8 + 2 * common.cellCount.val ≤ offset && offset < page.length)
        then some (.leaf (offsets.map page.drop)) else none
    | _ => none

def catalogFields? : List RecordField → Option CatalogEntry
  | [kindField, nameField, tableField, rootField, sqlField] => do
      let kind ← fieldText? kindField
      let name ← fieldText? nameField
      let table ← fieldText? tableField
      let rootPage ← fieldNat? rootField
      let sql ← fieldOptionalText? sqlField
      some { kind, name, table, rootPage, sql }
  | _ => none

def catalogCellIOFrom (source : IOPageSource) (input : List UInt8) :
    IO (Option CatalogEntry) := do
  let some (cell, _) := decodeTableLeafCell source.usable input | return none
  let some payload ← resolvedTablePayloadIOFrom source (source.pageCount + 1) cell | return none
  let some (record, suffix) := decodePhysicalRecord payload | return none
  unless suffix = [] && record.encode.length = cell.payloadSize.val do return none
  let some fields := CoreTextEncoding.fields source.textEncoding record.fields | return none
  return catalogFields? fields

/-- A global visit budget and explicit visited-page set reject cycles, repeated
child references and out-of-range pointers before reading them. Leaf entries
retain schema rowid traversal order. Overflow resolution has its own bounded
payload reader, shared with ordinary table records. -/
def catalogWalkIOFrom (source : IOPageSource) : Nat → List Nat → List Nat →
    List CatalogEntry → IO (Option (List CatalogEntry))
  | _, [], _, entries => pure (some entries.reverse)
  | 0, _ :: _, _, _ => pure none
  | fuel + 1, pageNumber :: pending, visited, entries => do
      if pageNumber == 0 || source.pageCount < pageNumber || visited.contains pageNumber then return none
      let some page ← source.readPage pageNumber | return none
      let some decoded := catalogPage? source.usable.val pageNumber page | return none
      match decoded with
      | .branch children =>
          catalogWalkIOFrom source fuel (children ++ pending) (pageNumber :: visited) entries
      | .leaf cells =>
          let entriesOnPage ← cells.mapM (catalogCellIOFrom source)
          let some entriesOnPage := sequenceOptions entriesOnPage | return none
          catalogWalkIOFrom source fuel pending (pageNumber :: visited) (entriesOnPage.reverse ++ entries)

def catalogIOFrom (source : IOPageSource) : IO (Option (List CatalogEntry)) :=
  catalogWalkIOFrom source source.pageCount [1] [] []

theorem catalogFields_nil : catalogFields? [] = none := rfl

theorem catalogWalk_empty (source : IOPageSource) (fuel : Nat)
    (visited : List Nat) (entries : List CatalogEntry) :
    catalogWalkIOFrom source fuel [] visited entries = pure (some entries.reverse) := by
  cases fuel <;> rfl

theorem catalogWalk_exhausted (source : IOPageSource) (page : Nat)
    (pending visited : List Nat) (entries : List CatalogEntry) :
    catalogWalkIOFrom source 0 (page :: pending) visited entries = pure none := rfl

def decodeFromIOPageSource (source : IOPageSource) : IO (Option Core.Database) := do
  let some catalog ← catalogIOFrom source | return none
  let tableEntries := catalog.filter (fun entry => entry.kind == "table")
  let indexEntries := catalog.filter (fun entry => entry.kind == "index")
  let tables ← tableEntries.mapM (decodeTableIOFrom source)
  let some tables := sequenceOptions tables | return none
  let some database := (Core.Database.rebuild tables).toOption | return none
  applyIndexesIOFrom source database indexEntries

/-- Pure validating counterpart of the general IO catalog reader. -/
def catalogCellFrom (source : PageSource) (input : List UInt8) : Option CatalogEntry := do
  let (payloadSize,afterSize) ← decodeVarint input
  let (_,afterRowid) ← decodeVarint afterSize
  let (payload,_) ← decodeTablePayloadBytesFrom source (source.pageCount+1) payloadSize.val afterRowid
  let (record,suffix) ← decodePhysicalRecord payload
  if suffix != [] || record.encode.length != payloadSize.val then none else catalogFields? record.fields

def catalogWalkFrom (source : PageSource) : Nat → List Nat → List Nat → List CatalogEntry → Option (List CatalogEntry)
  | _, [], _, entries => some entries.reverse
  | 0, _ :: _, _, _ => none
  | fuel+1, pageNumber :: pending, visited, entries => do
      if pageNumber == 0 || source.pageCount < pageNumber || visited.contains pageNumber then none else do
        let page ← source.readPage pageNumber
        let decoded ← catalogPage? PhysicalCodec.usablePageSize.val pageNumber page
        match decoded with
        | .branch children => catalogWalkFrom source fuel (children++pending) (pageNumber::visited) entries
        | .leaf cells =>
            let found ← cells.mapM (catalogCellFrom source)
            catalogWalkFrom source fuel pending (pageNumber::visited) (found.reverse++entries)

def catalogFromPageSource (source : PageSource) : Option (List CatalogEntry) :=
  (source.readPage 1 >>= decodeCatalogForOpen).orElse
    (fun _ => catalogWalkFrom source source.pageCount [1] [] [])

theorem catalogFromPageSource_shallow (source : PageSource) (catalog : List CatalogEntry)
    (read : source.readPage 1 >>= decodeCatalogForOpen = some catalog) :
    catalogFromPageSource source = some catalog := by
  unfold catalogFromPageSource
  rw [read]
  rfl

def decodeFromPageSource (source : PageSource) : Option Core.Database := do
  let catalog ← catalogFromPageSource source
  let tableEntries := catalog.filter (fun entry => entry.kind == "table")
  let indexEntries := catalog.filter (fun entry => entry.kind == "index")
  let tables ← tableEntries.mapM (decodeTableFrom source)
  let database ← (Core.Database.rebuild tables).toOption
  applyIndexesForOpen source database indexEntries

/-- Validating catalog acquisition with the actual declared table storage kind. -/
def decodeForOpenFromPageSource (source : PageSource) : Option Core.Database := do
  let catalog ← catalogFromPageSource source
  let tables ← (catalog.filter (·.kind == "table")).mapM (decodeTableForOpenFrom source)
  let database ← (Core.Database.rebuild tables).toOption
  applyIndexesForOpen source database (catalog.filter (·.kind == "index"))

/-- Exact component-wise account of a validating open.  Unlike
`PageSourceRepresents`, this relation does not quotient the in-memory row-tree
topology through canonicalization: it records exactly what the executable
decoder returned. -/
inductive PageSourceDecodes (source : PageSource)
    (database : Core.Database) : Prop where
  | intro (catalog : List CatalogEntry)
      (catalogRead :
        source.readPage 1 >>= decodeCatalogForOpen = some catalog)
      (tablesRead :
        (catalog.filter (fun entry => entry.kind == "table")).mapM
          (decodeTableFrom source) =
            some (database.tables.map Core.Table.withoutIndexes))
      (indexesRead :
        applyIndexesForOpen source database.withoutIndexes
          (catalog.filter (fun entry => entry.kind == "index")) =
            some database) :
      PageSourceDecodes source database

theorem PageSourceDecodes.decode
    {source : PageSource} {database : Core.Database}
    (decodes : PageSourceDecodes source database) :
    decodeFromPageSource source = some database := by
  rcases decodes with ⟨catalog, catalogRead, tablesRead, indexesRead⟩
  unfold decodeFromPageSource
  rw [catalogFromPageSource_shallow source catalog catalogRead]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [tablesRead]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [Core.Database.rebuild_withoutIndexes]
  simp only [Except.toOption, Option.bind_eq_bind, Option.bind]
  exact indexesRead

/-- Compositional physical representation invariant.  Unlike the single
equation `decodeFromPageSource source = ...`, this records the exact catalog,
table, and index obligations separately so a page-local mutation can preserve
unchanged components and re-prove only the component it touched. -/
inductive PageSourceRepresents (source : PageSource)
    (database : Core.Database) : Prop where
  | intro (catalog : List CatalogEntry)
      (catalogRead :
        source.readPage 1 >>= decodeCatalogForOpen = some catalog)
      (tablesRead :
        (catalog.filter (fun entry => entry.kind == "table")).mapM
          (decodeTableFrom source) =
            some (database.tables.map Core.Table.withoutIndexes))
      (indexesRead :
        applyIndexesForOpen source database.withoutIndexes
          (catalog.filter (fun entry => entry.kind == "index")) =
            some database.canonicalize) :
      PageSourceRepresents source database

theorem PageSourceRepresents.decode
    {source : PageSource} {database : Core.Database}
    (represents : PageSourceRepresents source database) :
    decodeFromPageSource source = some database.canonicalize := by
  rcases represents with ⟨catalog, catalogRead, tablesRead, indexesRead⟩
  unfold decodeFromPageSource
  rw [catalogFromPageSource_shallow source catalog catalogRead]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [tablesRead]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [Core.Database.rebuild_withoutIndexes]
  simp only [Except.toOption, Option.bind_eq_bind, Option.bind]
  exact indexesRead

/-- Exact validating-open components become the topology-quotiented storage
invariant once the returned database is known to be canonical. -/
theorem PageSourceDecodes.represents
    {source : PageSource} {database : Core.Database}
    (decodes : PageSourceDecodes source database)
    (fixed : database.canonicalize = database) :
    PageSourceRepresents source database := by
  rcases decodes with ⟨catalog, catalogRead, tablesRead, indexesRead⟩
  exact .intro catalog catalogRead tablesRead (by simpa [fixed] using indexesRead)

def pages : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | count + 1, input =>
      input.take PhysicalCodec.pageSize ::
        pages count (input.drop PhysicalCodec.pageSize)

def decode (input : List UInt8) : Option Core.Database := do
  let (header, _) ← decodeDatabaseHeader input
  let count := header.databaseSizePages.val
  if _pageSizeMatches : header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize then
    if _noReservedSpace : header.headerPrefix.reservedSpace = 0 then
      if _utf8 : header.textEncoding.val = 1 then
        if _fileLength : input.length = count * PhysicalCodec.pageSize then
          let physicalPages := pages count input
          decodeFromPageSource (.ofList physicalPages)
        else none
      else none
    else none
  else none

def decodeForOpen (input : List UInt8) : Option Core.Database := do
  let (header, _) ← decodeDatabaseHeader input
  let count := header.databaseSizePages.val
  if _pageSizeMatches : header.headerPrefix.pageSizeField.val = PhysicalCodec.pageSize then
    if _noReservedSpace : header.headerPrefix.reservedSpace = 0 then
      if _utf8 : header.textEncoding.val = 1 then
        if _fileLength : input.length = count * PhysicalCodec.pageSize then
          let physicalPages := pages count input
          decodeForOpenFromPageSource (.ofList physicalPages)
        else none
      else none
    else none
  else none

/-- Strict inverse for images emitted by `CoreFile.encode`. It decodes the
catalog and every table logically, restores index metadata, and finally
requires byte-for-byte canonical re-encoding. That last check validates the
index pages and rejects unexplained or non-canonical physical pages. -/
def decodeCanonicalPageBytes (physicalPages : List (List UInt8)) :
    Option Core.Database := do
  let firstPage ← physicalPages[0]?
  let catalog ← decodeCanonicalCatalog firstPage
  let split := splitCanonicalCatalog catalog
  let (tables, _) ← decodeCanonicalTables 2 split.1 physicalPages.tail
  let database ← rebuildCanonicalDatabase tables split.2
  let image ← CoreFile.encode database
  if _canonical : image.pages.map CoreFile.Page.bytes = physicalPages then
    some database
  else none

end CoreDecode

end SQLeanite
