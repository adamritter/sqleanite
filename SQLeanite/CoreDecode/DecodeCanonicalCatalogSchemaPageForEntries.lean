import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeCanonicalTableGroupTablePages

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem decodeCanonicalCatalog_schemaPageForEntries
    (entries : List CoreFile.CatalogEntry) (count : U32Value)
    {page : CoreFile.Page}
    (safe : ∀ entry ∈ entries, CatalogTextRoundtrips entry)
    (built : CoreFile.schemaPageForEntries? entries count = some page) :
    decodeCanonicalCatalog page.bytes =
      some (entries.map CatalogEntry.ofEncoded) := by
  unfold CoreFile.schemaPageForEntries? at built
  cases cellsResult : CoreFile.catalogCellsFrom 1 entries with
  | none => simp [cellsResult] at built
  | some cells =>
      simp only [cellsResult, Option.bind_eq_bind, Option.bind] at built
      cases bodyResult : CoreFile.leafBody? 13 100 cells with
      | none => simp [bodyResult] at built
      | some body =>
          simp only [bodyResult] at built
          injection built with equal
          subst page
          rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
          change decodeCanonicalCatalog
            (encodeDatabaseHeader (CoreFile.databaseHeader count) ++ body.bytes) = _
          rw [bodyBytes]
          exact decodeCanonicalCatalog_leafPageBody
            (encodeDatabaseHeader (CoreFile.databaseHeader count)) entries cells
            (encodeDatabaseHeader_length _) fits safe cellsResult

theorem decodeCanonicalCatalog_schemaPage
    (database : Core.Database) (layouts : List CoreFile.TableLayout)
    (indexes : List CoreFile.IndexLayout) (count : U32Value)
    {page : CoreFile.Page}
    (safe : ∀ entry ∈ CoreFile.catalogEntries database layouts indexes,
      CatalogTextRoundtrips entry)
    (built : CoreFile.schemaPage? database layouts indexes count = some page) :
    decodeCanonicalCatalog page.bytes =
      some ((CoreFile.catalogEntries database layouts indexes).map
        CatalogEntry.ofEncoded) := by
  unfold CoreFile.schemaPage? CoreFile.schemaPageForEntries? at built
  cases cellsResult : CoreFile.catalogCellsFrom 1
      (CoreFile.catalogEntries database layouts indexes) with
  | none => simp [cellsResult] at built
  | some cells =>
      simp only [cellsResult, Option.bind_eq_bind, Option.bind] at built
      cases bodyResult : CoreFile.leafBody? 13 100 cells with
      | none => simp [bodyResult] at built
      | some body =>
          simp only [bodyResult] at built
          injection built with equal
          subst page
          rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
          change decodeCanonicalCatalog
            (encodeDatabaseHeader (CoreFile.databaseHeader count) ++ body.bytes) = _
          rw [bodyBytes]
          apply decodeCanonicalCatalog_leafPageBody
          · exact encodeDatabaseHeader_length _
          · exact fits
          · exact safe
          · exact cellsResult

def decodeCatalog (firstPage : List UInt8) : Option (List CatalogEntry) := do
  let cells ← cellInputs? 100 firstPage
  cells.mapM decodeCatalogCell

def decodeCatalogForPageSize (pageSize : Nat) (firstPage : List UInt8) :
    Option (List CatalogEntry) := do
  let cells ← cellInputsFor? pageSize 100 firstPage
  cells.mapM decodeCatalogCell

/-- Check the whole pointer run before treating its payload as physically
key-ordered. A foreign page may have its first pointer at contentStart while
later pointers run backwards. -/
def ascendingCellPointers : Nat → Nat → List UInt8 → Bool
  | 0, _, _ => true
  | count + 1, lower, input =>
      match decodeUnsignedFixed 2 input with
      | some (offset, rest) => decide (lower ≤ offset) && ascendingCellPointers count offset rest
      | none => false

theorem ascendingCellPointers_leafPointers (cells : List (List UInt8))
    (start lower : Nat) (suffix : List UInt8) (ordered : lower ≤ start)
    (bounded : start + (PhysicalCodec.cellBytes cells).length < 65536) :
    ascendingCellPointers cells.length lower
      (PhysicalCodec.leafPointers start cells ++ suffix) = true := by
  induction cells generalizing start lower with
  | nil => rfl
  | cons cell cells ih =>
      have layout : PhysicalCodec.leafPointers start (cell :: cells) =
          PhysicalCodec.encodeU16Nat start ++
            PhysicalCodec.leafPointers (start + cell.length) cells := rfl
      rw [layout, List.append_assoc]
      simp only [List.length_cons, ascendingCellPointers, PhysicalCodec.encodeU16Nat]
      rw [decodeUnsignedFixed_encode _ (by
        simp [PhysicalCodec.cellBytes] at bounded
        omega)]
      simp only [ordered, decide_true, Bool.true_and]
      exact ih (start + cell.length) start (by omega) (by
        simp only [PhysicalCodec.cellBytes, List.flatten_cons, List.length_append] at bounded ⊢
        omega)

theorem ascendingCellPointers_next {count lower offset : Nat}
    {input rest : List UInt8}
    (decoded : decodeUnsignedFixed 2 input = some (offset, rest))
    (accepted : ascendingCellPointers (count + 1) lower input = true) :
    lower ≤ offset := by
  simp only [ascendingCellPointers, decoded, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact accepted.1

theorem decodedU16Nat (value : Nat) (bounded : value < 65536) :
    value / 256 % 256 * 256 + value % 256 = value := by
  have high : value / 256 < 256 := by omega
  rw [Nat.mod_eq_of_lt high]
  omega

def canonicalCatalogPointersBeginAtContent (page : List UInt8) : Bool :=
  match page.drop 100 with
  | 13 :: _ :: _ :: countHigh :: countLow :: contentHigh :: contentLow :: _ ::
      afterHeader =>
      let cellCount := decodeU16 countHigh countLow
      let contentStart := decodeU16 contentHigh contentLow
      if cellCount = 0 then true
      else match afterHeader with
        | firstHigh :: firstLow :: remaining =>
            decide (decodeU16 firstHigh firstLow = contentStart) &&
              ascendingCellPointers (cellCount - 1) contentStart remaining
        | _ => false
  | _ => false

theorem canonicalCatalogPointers_leafPageBody (headerBytes : List UInt8)
    (cells : List (List UInt8)) (headerLength : headerBytes.length = 100)
    (fits : PhysicalCodec.PageFit 100 cells) :
    canonicalCatalogPointersBeginAtContent
      (headerBytes ++ PhysicalCodec.leafPageBody 100 cells) = true := by
  have droppedHeader :
      (headerBytes ++ PhysicalCodec.leafPageBody 100 cells).drop 100 =
        PhysicalCodec.leafPageBody 100 cells := by
    rw [← headerLength]
    simp
  unfold canonicalCatalogPointersBeginAtContent
  rw [droppedHeader]
  have countBound : cells.length < 65536 := fits.cellCount_lt
  have contentBound : PhysicalCodec.pageSize -
      (PhysicalCodec.cellBytes cells).length < 65536 :=
    PhysicalCodec.contentStart_lt cells
  cases cells with
  | nil =>
      simp [PhysicalCodec.leafPageBody, PhysicalCodec.leafHeader,
        PhysicalCodec.leafPointers, PhysicalCodec.cellOffsetsFrom,
        PhysicalCodec.cellBytes, PhysicalCodec.encodeU16Nat,
        FileFormat.encodeUnsignedFixed, FileFormat.decodeU16]
  | cons cell cells =>
      simp only [List.length_cons] at countBound
      have restOrdered : ∀ suffix,
          ascendingCellPointers cells.length
            (PhysicalCodec.pageSize - (PhysicalCodec.cellBytes (cell :: cells)).length)
            (PhysicalCodec.leafPointers
              (PhysicalCodec.pageSize - (PhysicalCodec.cellBytes (cell :: cells)).length + cell.length)
              cells ++ suffix) = true := by
        intro suffix
        apply ascendingCellPointers_leafPointers
        · omega
        · have sizeBound : (PhysicalCodec.cellBytes (cell :: cells)).length ≤ PhysicalCodec.pageSize := by
            simp only [PhysicalCodec.PageFit, PhysicalTableBTree.InteriorPageFit] at fits
            omega
          simp only [PhysicalCodec.cellBytes, List.flatten_cons, List.length_append] at sizeBound ⊢
          have pageSize : PhysicalCodec.pageSize = 4096 := rfl
          omega
      simp only [PhysicalCodec.leafPointers, PhysicalCodec.cellBytes, List.flatten_cons,
        List.length_append, List.length_flatten] at restOrdered
      have decodedCount : (cells.length + 1) / 256 % 256 * 256 +
          (cells.length + 1) % 256 = cells.length + 1 := by omega
      simp only [PhysicalCodec.cellBytes, List.flatten_cons, List.length_append,
        List.length_flatten] at contentBound
      have decodedContent :
          (PhysicalCodec.pageSize - (cell.length + (cells.map List.length).sum)) / 256 % 256 * 256 +
          (PhysicalCodec.pageSize - (cell.length + (cells.map List.length).sum)) % 256 =
          PhysicalCodec.pageSize - (cell.length + (cells.map List.length).sum) :=
        decodedU16Nat _ contentBound
      simp [PhysicalCodec.leafPageBody, PhysicalCodec.leafHeader,
        PhysicalCodec.leafPointers, PhysicalCodec.cellOffsetsFrom,
        PhysicalCodec.cellBytes, PhysicalCodec.encodeU16Nat,
        FileFormat.encodeUnsignedFixed, FileFormat.decodeU16,
        Nat.mod_eq_of_lt countBound, Nat.mod_eq_of_lt contentBound, restOrdered, decodedCount, decodedContent]

/-- Generated pages use a proof-oriented sequential catalog decoder. Other
SQLite pointer layouts retain the tolerant offset-based decoder. -/
def decodeCatalogForOpen (firstPage : List UInt8) : Option (List CatalogEntry) :=
  if canonicalCatalogPointersBeginAtContent firstPage then
    match decodeCanonicalCatalog firstPage with
    | some catalog => some catalog
    | none => decodeCatalog firstPage
  else
    decodeCatalog firstPage

theorem decodeCatalogForOpen_schemaPageForEntries
    (entries : List CoreFile.CatalogEntry) (count : U32Value)
    {page : CoreFile.Page}
    (safe : ∀ entry ∈ entries, CatalogTextRoundtrips entry)
    (built : CoreFile.schemaPageForEntries? entries count = some page) :
    decodeCatalogForOpen page.bytes =
      some (entries.map CatalogEntry.ofEncoded) := by
  have canonical :=
    decodeCanonicalCatalog_schemaPageForEntries entries count safe built
  unfold CoreFile.schemaPageForEntries? at built
  cases cellsResult : CoreFile.catalogCellsFrom 1 entries with
  | none => simp [cellsResult] at built
  | some cells =>
    simp only [cellsResult, Option.bind_eq_bind, Option.bind] at built
    cases bodyResult : CoreFile.leafBody? 13 100 cells with
    | none => simp [bodyResult] at built
    | some body =>
      simp only [bodyResult] at built
      injection built with pageEqual
      subst page
      rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
      have pointers := canonicalCatalogPointers_leafPageBody
        (encodeDatabaseHeader (CoreFile.databaseHeader count)) cells
        (encodeDatabaseHeader_length _) fits
      change decodeCanonicalCatalog
        (encodeDatabaseHeader (CoreFile.databaseHeader count) ++ body.bytes) = _
          at canonical
      rw [bodyBytes] at canonical
      change decodeCatalogForOpen
        (encodeDatabaseHeader (CoreFile.databaseHeader count) ++ body.bytes) = _
      rw [bodyBytes]
      unfold decodeCatalogForOpen
      simp [pointers, canonical]

/-- Replacing only the 100-byte SQLite database header preserves the generated
catalog.  Freelist-backed files use this theorem when they change the database
size and freelist fields while retaining the exact schema B-tree body. -/
theorem decodeCatalogForOpen_schemaPageForEntries_withHeader
    (entries : List CoreFile.CatalogEntry) (count : U32Value)
    {page : CoreFile.Page} (headerBytes : List UInt8)
    (headerLength : headerBytes.length = 100)
    (safe : ∀ entry ∈ entries, CatalogTextRoundtrips entry)
    (built : CoreFile.schemaPageForEntries? entries count = some page) :
    decodeCatalogForOpen (headerBytes ++ page.bytes.drop 100) =
      some (entries.map CatalogEntry.ofEncoded) := by
  unfold CoreFile.schemaPageForEntries? at built
  cases cellsResult : CoreFile.catalogCellsFrom 1 entries with
  | none => simp [cellsResult] at built
  | some cells =>
      simp only [cellsResult, Option.bind_eq_bind, Option.bind] at built
      cases bodyResult : CoreFile.leafBody? 13 100 cells with
      | none => simp [bodyResult] at built
      | some body =>
          simp only [bodyResult] at built
          injection built with pageEqual
          subst page
          rcases CoreFile.leafBody_table_exact bodyResult with
            ⟨bodyBytes, fits⟩
          change decodeCatalogForOpen
            (headerBytes ++
              (encodeDatabaseHeader (CoreFile.databaseHeader count) ++
                body.bytes).drop 100) = _
          rw [bodyBytes]
          have dropped :
              (encodeDatabaseHeader (CoreFile.databaseHeader count) ++
                  PhysicalCodec.leafPageBody 100 cells).drop 100 =
                PhysicalCodec.leafPageBody 100 cells := by
            rw [← encodeDatabaseHeader_length (CoreFile.databaseHeader count)]
            simp
          rw [dropped]
          have canonical := decodeCanonicalCatalog_leafPageBody headerBytes
            entries cells headerLength fits safe cellsResult
          have pointers := canonicalCatalogPointers_leafPageBody headerBytes
            cells headerLength fits
          unfold decodeCatalogForOpen
          simp [pointers, canonical]

/-- Recover a schema from `sqlite_schema`.

The canonical recognizer runs first: for text this engine printed it inverts
`CanonicalSchemaSQL.tableChars` by proof, so `decode (encode db)` does not
depend on the correctness of the general SQL parser. Anything else -- notably
files written by C SQLite, whose `CREATE TABLE` text we did not generate --
uses metadata-only parsing and the independent token grammar replay. -/
def parseTableSchema := CoreCatalogSQL.parse

/-- The canonical path is taken for every schema this engine prints. -/
theorem parseTableSchema_tableSQL (schema : Core.Schema)
    (printable : CanonicalSchemaSQL.Printable schema) :
    parseTableSchema (CanonicalSchemaSQL.print schema) = some schema := by
  exact CoreCatalogSQL.parse_print schema printable

theorem parseTableSchema_catalogSQL (table : Core.Table) :
    parseTableSchema table.catalogSQL = some table.schema :=
  table.parse_catalogSQL

def decodeCanonicalTableStep (nextPage : Nat) (entry : CatalogEntry)
    (physicalPages : List (List UInt8)) :
    Option (Core.Table × Nat × List (List UInt8)) := do
  if _isTable : entry.kind = "table" then
    if _rootMatches : entry.rootPage = nextPage then
      let sql ← entry.sql
      let schema ← parseTableSchema sql
      if _nameMatches : schema.name = entry.name then
        match physicalPages with
        | [] => none
        | root :: tail => do
            let (group, remaining) ←
              match canonicalInteriorLeafCount? root with
              | none => some ([root], tail)
              | some leafCount =>
                  let leaves := tail.take leafCount
                  if _enoughLeaves : leaves.length = leafCount then
                    some (root :: leaves, tail.drop leafCount)
                  else none
            let rows ← decodeCanonicalTableGroup schema group
            let table ← (Core.Table.rebuildFromCatalog schema [] rows sql).toOption
            some (table, group.length, remaining)
      else none
    else none
  else none

def decodeCanonicalTables : Nat → List CatalogEntry → List (List UInt8) →
    Option (List Core.Table × List (List UInt8))
  | _, [], physicalPages => some ([], physicalPages)
  | nextPage, entry :: entries, physicalPages => do
      let (table, consumed, remaining) ←
        decodeCanonicalTableStep nextPage entry physicalPages
      let (tables, suffix) ←
        decodeCanonicalTables (nextPage + consumed) entries remaining
      some (table :: tables, suffix)

def decodeCanonicalIndex (schema : Core.Schema) (tableName : String)
    (entry : CatalogEntry) : Option Core.Index := do
  if _isIndex : entry.kind = "index" then
    if _tableMatches : entry.table = tableName then
      match entry.sql with
      | some sql => do
          let spec ← CanonicalIndexSQL.parse sql
          if _metadataMatches : spec.name = entry.name ∧ spec.table = tableName then
            let column ← schema.columns.findIdx?
              (fun candidate => candidate.name = spec.column)
            some ⟨spec.name, column, spec.unique⟩
          else none
      | none =>
          let index : Core.Index := ⟨entry.name, schema.declaredPrimaryKey, false⟩
          if schema.declaredPrimaryKey < schema.columns.length then
            if index.isImplicitPrimary schema then some index else none
          else none
    else none
  else none

theorem decodeCanonicalIndex_missing_primary (schema : Core.Schema) (tableName : String)
    (entry : CatalogEntry) (noSQL : entry.sql = none)
    (missing : schema.columns.length ≤ schema.declaredPrimaryKey) :
    decodeCanonicalIndex schema tableName entry = none := by
  simp [decodeCanonicalIndex, noSQL, Nat.not_lt.mpr missing]

theorem decodeCanonicalIndex_encoded (table : Core.Table) (index : Core.Index)
    (member : index ∈ table.indexes) (rootPage : Nat) :
    let entry : CoreFile.CatalogEntry := {
      kind := "index"
      name := index.name
      table := table.schema.name
      rootPage
      sql := CoreFile.indexSQL table index
      sqlIsNull := index.isImplicitPrimary table.schema }
    decodeCanonicalIndex table.schema table.schema.name
      (CatalogEntry.ofEncoded entry) = some index := by
  dsimp only
  unfold decodeCanonicalIndex CatalogEntry.ofEncoded
  rw [dif_pos rfl, dif_pos rfl]
  simp only [Option.bind_eq_bind, Option.bind]
  have indexEta : (⟨index.name, index.column, index.unique⟩ : Core.Index) = index := by
    cases index
    rfl
  by_cases automatic : index.isImplicitPrimary table.schema = true
  · rw [if_pos automatic]
    simp only
    have automatic' := automatic
    unfold Core.Index.isImplicitPrimary at automatic
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true] at automatic
    have column : index.column = table.schema.declaredPrimaryKey :=
      automatic.1.2
    have ordinary : index.unique = false := by
      cases h : index.unique <;> simp_all
    have indexEq :
        (⟨index.name, table.schema.declaredPrimaryKey, false⟩ : Core.Index) = index := by
      calc
        _ = (⟨index.name, index.column, index.unique⟩ : Core.Index) := by rw [column, ordinary]
        _ = index := indexEta
    have bound : table.schema.declaredPrimaryKey < table.schema.columns.length := by
      rw [← column]
      exact table.indexesWellFormed.1 index member
    rw [if_pos bound, indexEq, if_pos automatic']
  · rw [if_neg automatic]
    let columnName :=
      (table.schema.columns[index.column]?).map (·.name) |>.getD ""
    let spec : CanonicalIndexSQL.Spec :=
      ⟨index.name, table.schema.name, columnName, index.unique⟩
    change (CanonicalIndexSQL.parse (CoreFile.indexSQL table index)).bind _ =
      some index
    rw [CoreFile.parse_indexSQL table index]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [dif_pos (by simp)]
    have indexValid := table.indexesWellFormed.1 index member
    have columnNameEq : columnName =
        (table.schema.columns[index.column]'indexValid).name := by
      simp [columnName, List.getElem?_eq_getElem indexValid]
    have found := table.schema.findIdx?_column_name table.schemaWellFormed
      index.column indexValid
    change (table.schema.columns.findIdx?
      (fun candidate => candidate.name = columnName)).bind
        (fun column => some (⟨index.name, column, index.unique⟩ : Core.Index)) = some index
    rw [columnNameEq, found]
    rfl

def decodeCanonicalIndexesForTable (schema : Core.Schema) (tableName : String) :
    List CatalogEntry → Option (List Core.Index × List CatalogEntry)
  | [] => some ([], [])
  | entry :: entries =>
      if _sameTable : entry.table = tableName then do
        let index ← decodeCanonicalIndex schema tableName entry
        let (indexes, remaining) ←
          decodeCanonicalIndexesForTable schema tableName entries
        some (index :: indexes, remaining)
      else some ([], entry :: entries)

def restoreCanonicalIndexes : List Core.Table → List CatalogEntry →
    Option (List Core.Table × List CatalogEntry)
  | [], entries => some ([], entries)
  | table :: tables, entries => do
      let (indexes, remaining) ←
        decodeCanonicalIndexesForTable table.schema table.schema.name entries
      let rebuilt ← (Core.Table.rebuild table.schema indexes table.rows table.catalogSource).toOption
      let (restored, suffix) ← restoreCanonicalIndexes tables remaining
      some (rebuilt :: restored, suffix)

def rebuildCanonicalDatabase (tables : List Core.Table)
    (indexEntries : List CatalogEntry) : Option Core.Database := do
  let (restored, suffix) ← restoreCanonicalIndexes tables indexEntries
  if _consumed : suffix = [] then
    (Core.Database.rebuild restored).toOption
  else none

end CoreDecode

end SQLeanite
