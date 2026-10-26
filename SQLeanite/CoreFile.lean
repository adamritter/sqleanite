import SQLeanite.CoreRecord
import SQLeanite.CoreEngine
import SQLeanite.PhysicalQuery
import SQLeanite.CellPagination
import SQLeanite.CanonicalSchemaSQL
import SQLeanite.CanonicalIndexSQL
import SQLeanite.PhysicalTableBTree

attribute [local instance] lexOrd

namespace SQLeanite
namespace CoreFile

open FileFormat

structure Page where
  bytes : List UInt8
  length_eq : bytes.length = PhysicalCodec.pageSize

structure PageBody (headerOffset : Nat) where
  bytes : List UInt8
  length_eq : bytes.length = PhysicalCodec.pageSize - headerOffset

def Page.storage (page : Page) : Storage.Page PhysicalCodec.pageSize := {
  bytes := page.bytes.toArray
  sizeInvariant := by simp [page.length_eq] }

def text? (value : String) : Option PhysicalCodec.Text :=
  let bytes := value.toUTF8.data.toList
  if bound : bytes.length < PhysicalCodec.textByteLimit then some ⟨bytes, bound⟩
  else none

def quoteIdentifier (name : String) : String :=
  "\"" ++ name.replace "\"" "\"\"" ++ "\""

/-- Retain schema-checked catalog text. New abstract schemas use the
canonical printer, whose inverse is proved for structurally valid schemas. -/
def tableSQL (table : Core.Table) : String :=
  table.catalogSQL

def valueIsInteger : Core.Value → Bool
  | .integer _ => true
  | _ => false

def valueIsText : Core.Value → Bool
  | .text _ => true
  | _ => false

def indexValuesInteger (table : Core.Table) (index : Core.Index) : Bool :=
  table.rows.all fun row => valueIsInteger (row.value index.column)

@[simp] theorem indexValuesInteger_canonicalize
    (table : Core.Table) (index : Core.Index) :
    indexValuesInteger table.canonicalize index =
      indexValuesInteger table index := by
  unfold indexValuesInteger
  rw [Core.Table.canonicalize_rows]

theorem indexValuesInteger_iff (table : Core.Table) (index : Core.Index) :
    indexValuesInteger table index = true ↔
      ∀ row ∈ table.rows,
        ∃ integer : Core.Integer, row.value index.column = .integer integer := by
  unfold indexValuesInteger
  rw [List.all_eq_true]
  apply forall_congr'
  intro row
  apply imp_congr_right
  intro member
  cases valueResult : row.value index.column <;>
    simp [valueIsInteger, valueResult]

def indexValuesText (table : Core.Table) (index : Core.Index) : Bool :=
  table.rows.all fun row => valueIsText (row.value index.column)

@[simp] theorem indexValuesText_canonicalize
    (table : Core.Table) (index : Core.Index) :
    indexValuesText table.canonicalize index =
      indexValuesText table index := by
  unfold indexValuesText
  rw [Core.Table.canonicalize_rows]

theorem indexValuesText_iff (table : Core.Table) (index : Core.Index) :
    indexValuesText table index = true ↔
      ∀ row ∈ table.rows,
        ∃ text : PhysicalCodec.Text, row.value index.column = .text text := by
  unfold indexValuesText
  rw [List.all_eq_true]
  apply forall_congr'
  intro row
  apply imp_congr_right
  intro member
  cases valueResult : row.value index.column <;>
    simp [valueIsText, valueResult]

def indexSQL (table : Core.Table) (index : Core.Index) : String :=
  let columnName := (table.schema.columns[index.column]?).map (·.name) |>.getD ""
  let spec : CanonicalIndexSQL.Spec :=
    ⟨index.name, table.schema.name, columnName, index.unique⟩
  if indexValuesInteger table index then
    CanonicalIndexSQL.printIntegerCertified spec
  else if indexValuesText table index then
    CanonicalIndexSQL.printTextCertified spec
  else CanonicalIndexSQL.print spec

theorem parse_indexSQL (table : Core.Table) (index : Core.Index) :
    let columnName :=
      (table.schema.columns[index.column]?).map (·.name) |>.getD ""
    CanonicalIndexSQL.parse (indexSQL table index) =
      some ⟨index.name, table.schema.name, columnName, index.unique⟩ := by
  dsimp only
  unfold indexSQL
  split
  · exact CanonicalIndexSQL.parse_printIntegerCertified _
  · split
    · exact CanonicalIndexSQL.parse_printTextCertified _
    · exact CanonicalIndexSQL.parse_print _

theorem parseIntegerCertified_indexSQL (table : Core.Table)
    (index : Core.Index) :
    (CanonicalIndexSQL.parseIntegerCertified (indexSQL table index)).isSome =
      indexValuesInteger table index := by
  unfold indexSQL
  by_cases integers : indexValuesInteger table index = true
  · rw [if_pos integers]
    rw [CanonicalIndexSQL.parseIntegerCertified_print]
    simp [integers]
  · rw [if_neg integers]
    let spec : CanonicalIndexSQL.Spec :=
      ⟨index.name, table.schema.name,
        (table.schema.columns[index.column]?).map (·.name) |>.getD "", index.unique⟩
    by_cases texts : indexValuesText table index = true
    · rw [if_pos texts]
      simp only [CanonicalIndexSQL.parseIntegerCertified,
        CanonicalIndexSQL.parse_printTextCertified,
        Option.bind_eq_bind, Option.bind]
      have unequal : CanonicalIndexSQL.printTextCertified spec ≠
          CanonicalIndexSQL.printIntegerCertified spec := by
        intro equal
        have lengths := congrArg String.length equal
        simp [CanonicalIndexSQL.printTextCertified,
          CanonicalIndexSQL.printIntegerCertified,
          CanonicalIndexSQL.textCertificateMarker,
          CanonicalIndexSQL.integerCertificateMarker] at lengths
        exact (by decide : " /*LSQL:TEXT*/".length ≠
          " /*LSQL:INTEGER*/".length) lengths
      rw [if_neg unequal]
      simp [integers]
    · rw [if_neg texts]
      simp only [CanonicalIndexSQL.parseIntegerCertified,
        CanonicalIndexSQL.parse_print, Option.bind_eq_bind, Option.bind]
      have unequal : CanonicalIndexSQL.print spec ≠
          CanonicalIndexSQL.printIntegerCertified spec := by
        intro equal
        have lengths := congrArg String.length equal
        have markerPositive :
            0 < CanonicalIndexSQL.integerCertificateMarker.length := by decide
        simp only [CanonicalIndexSQL.printIntegerCertified, String.length_append] at lengths
        omega
      rw [if_neg unequal]
      simp [integers]

structure CatalogEntry where
  kind : String
  name : String
  table : String
  rootPage : Nat
  sql : String
  /-- SQLite represents automatically generated PRIMARY KEY indexes with a
  NULL `sqlite_schema.sql` field. -/
  sqlIsNull : Bool := false

def indexedIndexes (database : Core.Database) :
    List (Core.Table × Core.Index) :=
  database.tables.flatMap fun table => table.indexes.map fun index => (table, index)

def tableCells (table : Core.Table) : Option (List (List UInt8)) :=
  table.rows.mapM (CoreRecord.encodeCell? table.schema)

/-- Encoded row cells of a table, split into leaf-sized runs.

A table with more than one run needs an interior root page above its leaves, so
its page footprint is no longer fixed at one. Layout therefore has to be
computed before the catalog, because `rootPage` depends on it. -/
def tableLeaves (table : Core.Table) : Option (List (List (List UInt8))) := do
  let cells ← tableCells table
  some (CellPagination.paginateCells cells)

theorem tableCells_canonicalize (table : Core.Table) :
    tableCells table.canonicalize = tableCells table := by
  unfold tableCells
  rw [Core.Table.canonicalize_schema, Core.Table.canonicalize_rows]

theorem tableLeaves_canonicalize (table : Core.Table) :
    tableLeaves table.canonicalize = tableLeaves table := by
  unfold tableLeaves
  rw [tableCells_canonicalize]

/-- Pages occupied by one table: `n` leaves, plus an interior root when `n > 1`.
A single-leaf table keeps the old shape, its root *is* the leaf. -/
def tableFootprint (leaves : List (List (List UInt8))) : Nat :=
  if leaves.length ≤ 1 then 1 else leaves.length + 1

/-- Where each table's pages live, in page-number order starting at 2. -/
structure TableLayout where
  rootPage : Nat
  leaves : List (List (List UInt8))

def layoutTables (next : Nat) :
    List (List (List (List UInt8))) → List TableLayout
  | [] => []
  | leaves :: rest =>
      { rootPage := next, leaves } ::
        layoutTables (next + tableFootprint leaves) rest

/-- First page number after every table's pages; index roots start here. -/
def indexRootBase (layouts : List TableLayout) : Nat :=
  layouts.foldl (fun total layout => total + tableFootprint layout.leaves) 2

def tableEntriesFor : List Core.Table → List TableLayout → List CatalogEntry
  | table :: tables, layout :: layouts => {
    kind := "table"
    name := table.schema.name
    table := table.schema.name
    rootPage := layout.rootPage
    sql := tableSQL table } :: tableEntriesFor tables layouts
  | _, _ => []

def tableEntries (database : Core.Database) (layouts : List TableLayout) :
    List CatalogEntry := tableEntriesFor database.tables layouts

theorem tableEntriesFor_kind : ∀ (tables : List Core.Table)
    (layouts : List TableLayout) (entry : CatalogEntry),
    entry ∈ tableEntriesFor tables layouts → entry.kind = "table"
  | [], _, _, member => by simp [tableEntriesFor] at member
  | _, [], _, member => by simp [tableEntriesFor] at member
  | table :: tables, layout :: layouts, entry, member => by
      simp only [tableEntriesFor, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact tableEntriesFor_kind tables layouts entry member

/-- Where each index's pages live. Like tables, an index spanning several
leaves needs an interior root, so its footprint is not fixed at one. -/
structure IndexLayout where
  rootPage : Nat
  leaves : List (List (List UInt8))

def layoutIndexes (next : Nat) :
    List (List (List (List UInt8))) → List IndexLayout
  | [] => []
  | leaves :: rest =>
      { rootPage := next, leaves } ::
        layoutIndexes (next + tableFootprint leaves) rest

def indexEntriesFor : List (Core.Table × Core.Index) →
    List IndexLayout → List CatalogEntry
  | indexed :: indexedIndexes, layout :: layouts => {
    kind := "index"
    name := indexed.2.name
    table := indexed.1.schema.name
    rootPage := layout.rootPage
    sql := indexSQL indexed.1 indexed.2
    sqlIsNull := indexed.2.isImplicitPrimary indexed.1.schema } ::
      indexEntriesFor indexedIndexes layouts
  | _, _ => []

def indexEntries (database : Core.Database) (indexes : List IndexLayout) :
    List CatalogEntry := indexEntriesFor (indexedIndexes database) indexes

def catalogEntries (database : Core.Database) (layouts : List TableLayout)
    (indexes : List IndexLayout) : List CatalogEntry :=
  tableEntries database layouts ++ indexEntries database indexes

def physicalRecord? (fields : List RecordField) : Option PhysicalRecord :=
  if bound : recordHeaderSize (encodeRecordSerialTypes fields).length < 2 ^ 64 then
    some ⟨fields, by simpa using bound⟩
  else none

def signedNat? (value : Nat) : Option (SignedInteger .eight) :=
  if upper : value < FileFormat.IntegerWidth.eight.midpoint then
    some ⟨Int.ofNat value, by simp, by simpa using upper⟩
  else none

def recordCell? (rowid : SignedInteger .eight) (fields : List RecordField) :
    Option (List UInt8) := do
  let record ← physicalRecord? fields
  if bound : record.encode.length < 2 ^ 64 then
    let payloadSize : U64Value := ⟨record.encode.length, by simpa using bound⟩
    some (encodeVarint payloadSize ++ encodeVarint (signedInteger64Bits rowid) ++
      record.encode)
  else none

def catalogCell? (rowid : Nat) (entry : CatalogEntry) : Option (List UInt8) := do
  let rowid ← signedNat? rowid
  let kind ← text? entry.kind
  let name ← text? entry.name
  let table ← text? entry.table
  let rootPage ← signedNat? entry.rootPage
  let sqlField ← if entry.sqlIsNull then some RecordField.null
    else (text? entry.sql).map (·.recordField)
  recordCell? rowid [kind.recordField, name.recordField, table.recordField,
    .integer .eight rootPage, sqlField]

def catalogCellsFrom : Nat → List CatalogEntry → Option (List (List UInt8))
  | _, [] => some []
  | rowid, entry :: entries => do
      let cell ← catalogCell? rowid entry
      let cells ← catalogCellsFrom (rowid + 1) entries
      some (cell :: cells)

theorem catalogCellsFrom_length {rowid : Nat} {entries : List CatalogEntry}
    {cells : List (List UInt8)}
    (built : catalogCellsFrom rowid entries = some cells) :
    cells.length = entries.length := by
  induction entries generalizing rowid cells with
  | nil =>
      simp only [catalogCellsFrom] at built
      injection built with equal
      subst cells
      rfl
  | cons entry entries induction =>
      simp only [catalogCellsFrom, Option.bind_eq_bind, Option.bind] at built
      cases headResult : catalogCell? rowid entry with
      | none => simp [headResult] at built
      | some cell =>
          simp only [headResult] at built
          cases tailResult : catalogCellsFrom (rowid + 1) entries with
          | none => simp [tailResult] at built
          | some remaining =>
              simp only [tailResult] at built
              injection built with equal
              subst cells
              simp [induction tailResult]

def replaceFirst (value : UInt8) : List UInt8 → List UInt8
  | [] => []
  | _ :: remaining => value :: remaining

theorem replaceFirst_length (value : UInt8) (bytes : List UInt8) :
    (replaceFirst value bytes).length = bytes.length := by
  cases bytes <;> rfl

def leafBody? (pageType headerOffset : Nat) (cells : List (List UInt8)) :
    Option (PageBody headerOffset) :=
  if typeByte : pageType < 256 then
    if fits : PhysicalCodec.PageFit headerOffset cells then
      let body := PhysicalCodec.leafPageBody headerOffset cells
      let bytes := replaceFirst (UInt8.ofNat pageType) body
      some {
        bytes
        length_eq := by
          rw [replaceFirst_length]
          exact PhysicalCodec.leafPageBody_length headerOffset cells fits }
    else none
  else none

theorem leafBody_table_exact {headerOffset : Nat}
    {cells : List (List UInt8)} {body : PageBody headerOffset}
    (built : leafBody? 13 headerOffset cells = some body) :
    body.bytes = PhysicalCodec.leafPageBody headerOffset cells ∧
      PhysicalCodec.PageFit headerOffset cells := by
  unfold leafBody? at built
  split at built
  next typeByte =>
    split at built
    next fits =>
      injection built with equal
      subst body
      exact ⟨rfl, fits⟩
    next doesNotFit => contradiction
  next invalidType => contradiction

/-- The default SQLite application identifier is zero. Generated-image
recognition must not overwrite application-owned metadata with a private tag. -/
def generatedApplicationId : U32Value := ⟨0, by omega⟩

/-- The current generated-image provenance tag is stored in both SQLite
change-counter fields. Application-owned nonzero metadata disables its fast
path. A normal SQLite writer advances
the counter and therefore invalidates the stamp; Lean's localized page writes
preserve it.  This is a provenance tag, not a cryptographic authenticator. -/
def generatedChangeCounter : U32Value := ⟨1279607118, by omega⟩

def hasGeneratedImageStamp (header : DatabaseHeader) : Bool :=
  header.applicationId.val == generatedApplicationId.val && header.userVersion.val == 0 &&
    header.headerPrefix.changeCounter.val == generatedChangeCounter.val &&
    header.versionValidFor.val == generatedChangeCounter.val

def GeneratedImageHeader (header : DatabaseHeader) : Prop :=
  hasGeneratedImageStamp header = true

def databaseHeader (pageCount : U32Value) : DatabaseHeader :=
  { PhysicalCodec.databaseHeader with
    headerPrefix := {
      PhysicalCodec.databaseHeader.headerPrefix with
      changeCounter := generatedChangeCounter }
    databaseSizePages := pageCount
    applicationId := generatedApplicationId
    versionValidFor := generatedChangeCounter }

theorem databaseHeader_generatedImage (pageCount : U32Value) :
    GeneratedImageHeader (databaseHeader pageCount) := by
  simp [GeneratedImageHeader, hasGeneratedImageStamp, databaseHeader,
    generatedApplicationId, generatedChangeCounter, PhysicalCodec.databaseHeader]

theorem databaseHeader_hasGeneratedImageStamp (pageCount : U32Value) :
    hasGeneratedImageStamp (databaseHeader pageCount) = true := by
  exact databaseHeader_generatedImage pageCount

def schemaPageForEntries? (entries : List CatalogEntry) (pageCount : U32Value) :
    Option Page := do
  let cells ← catalogCellsFrom 1 entries
  let body ← leafBody? 13 100 cells
  let header := encodeDatabaseHeader (databaseHeader pageCount)
  some {
    bytes := header ++ body.bytes
    length_eq := by
      rw [List.length_append, encodeDatabaseHeader_length, body.length_eq]
      simp [PhysicalCodec.pageSize] }

theorem schemaPageForEntries_header {entries : List CatalogEntry}
    {pageCount : U32Value} {page : Page}
    (built : schemaPageForEntries? entries pageCount = some page) :
    ∃ body, page.bytes = encodeDatabaseHeader (databaseHeader pageCount) ++ body := by
  unfold schemaPageForEntries? at built
  cases cellsResult : catalogCellsFrom 1 entries with
  | none => simp [cellsResult] at built
  | some cells =>
    simp only [cellsResult, Option.bind_eq_bind, Option.bind] at built
    cases bodyResult : leafBody? 13 100 cells with
    | none => simp [bodyResult] at built
    | some body =>
      simp only [bodyResult] at built
      injection built with equal
      subst page
      exact ⟨body.bytes, rfl⟩

def schemaPage? (database : Core.Database) (layouts : List TableLayout)
    (indexes : List IndexLayout) (pageCount : U32Value) :
    Option Page :=
  schemaPageForEntries? (catalogEntries database layouts indexes) pageCount

/-- One leaf page of a multi-leaf table. -/
def tableLeafPage? (cells : List (List UInt8)) : Option Page := do
  let body ← leafBody? 13 0 cells
  some { bytes := body.bytes, length_eq := by simpa using body.length_eq }

/-- Largest rowid in a leaf, which is SQLite's separator key for that child. -/
def leafSeparatorKey? (cells : List (List UInt8)) : Option Nat := do
  let last ← cells.getLast?
  let (_, afterPayload) ← decodeVarint last
  let (rowid, _) ← decodeVarint afterPayload
  some rowid.val

/-- Interior root page for a table whose rows span several leaves. Children are
consecutive page numbers starting at `firstLeaf`; the final leaf is the
rightmost pointer and gets no cell, exactly as SQLite lays it out. -/
def tableInteriorCells? (firstLeaf : Nat)
    (leaves : List (List (List UInt8))) : Option (List (List UInt8)) :=
  (leaves.dropLast.zipIdx).mapM fun pair => do
    let key ← leafSeparatorKey? pair.1
    let childNumber := firstLeaf + pair.2
    if childBound : childNumber < 2 ^ 32 then
      if keyBound : key < 2 ^ 64 then
        let child : U32Value := ⟨childNumber, by simpa using childBound⟩
        let rowid : U64Value := ⟨key, by simpa using keyBound⟩
        some (PhysicalTableBTree.encodeU32Nat child.val ++ encodeVarint rowid)
      else none
    else none

def tableInteriorPage? (firstLeaf : Nat) (leaves : List (List (List UInt8))) :
    Option Page := do
  let rightmostNumber := firstLeaf + leaves.length - 1
  if rightmostBound : rightmostNumber < 2 ^ 32 then
    let rightmost : U32Value := ⟨rightmostNumber, by simpa using rightmostBound⟩
    let cells ← tableInteriorCells? firstLeaf leaves
    if fits : PhysicalTableBTree.InteriorPageFit cells then
      some {
        bytes := PhysicalTableBTree.interiorPageBody rightmost cells
        length_eq := PhysicalTableBTree.interiorPageBody_length rightmost cells fits }
    else none
  else none

/-- Pages for one table, in page-number order: root first, then leaves. -/
def tablePages? (layout : TableLayout) : Option (List Page) :=
  match layout.leaves with
  | [] => do let page ← tableLeafPage? []; some [page]
  | [only] => do let page ← tableLeafPage? only; some [page]
  | _ => do
      let root ← tableInteriorPage? (layout.rootPage + 1) layout.leaves
      let leafPages ← layout.leaves.mapM tableLeafPage?
      some (root :: leafPages)

private theorem optionMapM_length {α β : Type} (f : α → Option β) :
    ∀ (input : List α) (output : List β),
      input.mapM f = some output → output.length = input.length
  | [], output, success => by
      simp only [List.mapM_nil, pure, Pure.pure] at success
      injection success with equal
      subst output
      rfl
  | value :: input, output, success => by
      cases headResult : f value with
      | none => simp [List.mapM_cons, headResult] at success
      | some result =>
          cases tailResult : input.mapM f with
          | none => simp [List.mapM_cons, headResult, tailResult] at success
          | some remaining =>
              simp only [List.mapM_cons, headResult, tailResult,
                Option.bind_eq_bind, Option.bind] at success
              injection success with equal
              subst output
              simp [optionMapM_length f input remaining tailResult]

theorem tablePages_length_of_success {layout : TableLayout} {pages : List Page}
    (built : tablePages? layout = some pages) :
    pages.length = tableFootprint layout.leaves := by
  cases leavesShape : layout.leaves with
  | nil =>
      unfold tablePages? at built
      rw [leavesShape] at built
      cases pageResult : tableLeafPage? [] with
      | none => simp [pageResult] at built
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at built
          injection built with equal
          subst pages
          rfl
  | cons first rest =>
    cases restShape : rest with
    | nil =>
      unfold tablePages? at built
      rw [leavesShape, restShape] at built
      cases pageResult : tableLeafPage? first with
      | none => simp [pageResult] at built
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at built
          injection built with equal
          subst pages
          rfl
    | cons second remaining =>
      unfold tablePages? at built
      rw [leavesShape, restShape] at built
      cases rootResult : tableInteriorPage? (layout.rootPage + 1)
          (first :: second :: remaining) with
      | none => simp [rootResult] at built
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at built
        cases leafResult : (first :: second :: remaining).mapM tableLeafPage? with
        | none => simp [leafResult] at built
        | some leaves =>
          simp only [leafResult] at built
          injection built with equal
          subst pages
          have leafLength := optionMapM_length tableLeafPage?
            (first :: second :: remaining) leaves leafResult
          simp [tableFootprint, leavesShape, restShape, leafLength]

/-- Cells a table layout stores, read back off the layout in page order. -/
def TableLayout.storedCells (layout : TableLayout) : List (List UInt8) :=
  layout.leaves.flatten

/-- **Multi-page layout is contents-preserving.** Whatever the split, the cells
distributed across a table's leaves are exactly the cells the table encoded, in
the same order. Nothing is lost, duplicated or reordered by paging.

This is the part of `decode (encode db) = db` that the multi-page work is
responsible for. The remaining gap is the catalog's SQL text: `decode` recovers
a schema by running the real parser over the `CREATE TABLE` string that
`encode` printed, so closing the full round trip needs
`parseTableSchema (tableSQL s) = some s`, a parser-correctness result that is
tracked separately in `docs/TRUST.md`. -/
theorem tableLeaves_storedCells (table : Core.Table)
    {leaves : List (List (List UInt8))} {cells : List (List UInt8)}
    (encoded : tableCells table = some cells)
    (paged : tableLeaves table = some leaves) :
    (TableLayout.storedCells ⟨0, leaves⟩) = cells := by
  unfold tableLeaves at paged
  rw [encoded] at paged
  simp at paged
  subst paged
  exact CellPagination.flatten_paginateCells cells

/-- Every leaf a layout emits fits a page, so page construction cannot fail for
size reasons once each individual cell fits. -/
theorem tableLeaves_fit (table : Core.Table)
    {leaves : List (List (List UInt8))} {cells : List (List UInt8)}
    (encoded : tableCells table = some cells)
    (paged : tableLeaves table = some leaves)
    (singles : ∀ cell ∈ cells, PhysicalCodec.PageFit 0 [cell]) :
    ∀ page ∈ leaves, PhysicalCodec.PageFit 0 page := by
  unfold tableLeaves at paged
  rw [encoded] at paged
  simp at paged
  subst paged
  exact CellPagination.paginateCells_fits cells singles

def indexRecord? (index : Core.Index)
    (row : Core.Row) : Option PhysicalRecord :=
  physicalRecord? [
    (row.value index.column).recordField,
    (PhysicalCodec.Value.integer row.rowid).recordField]

def indexCell? (index : Core.Index)
    (row : Core.Row) : Option (List UInt8) := do
  let record ← indexRecord? index row
  if bound : record.encode.length < 2 ^ 64 then
    let payloadSize : U64Value := ⟨record.encode.length, by simpa using bound⟩
    some (encodeVarint payloadSize ++ record.encode)
  else none

def indexRowLess (index : Core.Index)
    (left right : Core.Row) : Bool :=
  match PhysicalQuery.compareValue (left.value index.column) (right.value index.column) with
  | .lt => true
  | .gt => false
  | .eq => left.rowid.value < right.rowid.value

def indexRowValueLe (index : Core.Index) (left right : Core.Row) : Prop :=
  PhysicalQuery.compareValue (left.value index.column)
    (right.value index.column) ≠ .gt

theorem indexRowLess_true_valueLe (index : Core.Index)
    (left right : Core.Row)
    (less : indexRowLess index left right = true) :
    indexRowValueLe index left right := by
  unfold indexRowLess at less
  unfold indexRowValueLe
  intro greater
  rw [greater] at less
  simp at less

theorem indexRowLess_false_reverse_valueLe (index : Core.Index)
    (left right : Core.Row)
    (leftInteger : ∃ value : Core.Integer,
      left.value index.column = .integer value)
    (rightInteger : ∃ value : Core.Integer,
      right.value index.column = .integer value)
    (notLess : indexRowLess index left right = false) :
    indexRowValueLe index right left := by
  rcases leftInteger with ⟨leftValue, leftEqual⟩
  rcases rightInteger with ⟨rightValue, rightEqual⟩
  unfold indexRowLess at notLess
  unfold indexRowValueLe
  simp only [leftEqual, rightEqual, PhysicalQuery.compareValue] at notLess ⊢
  have forwardLt : compare leftValue.value rightValue.value = .lt ↔
      leftValue.value < rightValue.value := by
    change compareOfLessAndEq leftValue.value rightValue.value = .lt ↔ _
    exact compareOfLessAndEq_eq_lt
  have reverseGt : compare rightValue.value leftValue.value = .gt ↔
      leftValue.value < rightValue.value := by
    change compareOfLessAndEq rightValue.value leftValue.value = .gt ↔ _
    exact compareOfLessAndEq_eq_gt Int.le_antisymm Int.le_total Int.not_le _ _
  intro greater
  have forward := forwardLt.mpr (reverseGt.mp greater)
  rw [forward] at notLess
  simp at notLess

theorem indexRowValueLe_trans_integer (index : Core.Index)
    (left middle right : Core.Row)
    (leftInteger : ∃ value : Core.Integer,
      left.value index.column = .integer value)
    (middleInteger : ∃ value : Core.Integer,
      middle.value index.column = .integer value)
    (rightInteger : ∃ value : Core.Integer,
      right.value index.column = .integer value)
    (leftMiddle : indexRowValueLe index left middle)
    (middleRight : indexRowValueLe index middle right) :
    indexRowValueLe index left right := by
  rcases leftInteger with ⟨leftValue, leftEqual⟩
  rcases middleInteger with ⟨middleValue, middleEqual⟩
  rcases rightInteger with ⟨rightValue, rightEqual⟩
  unfold indexRowValueLe at leftMiddle middleRight ⊢
  simp only [leftEqual, middleEqual, rightEqual,
    PhysicalQuery.compareValue] at leftMiddle middleRight ⊢
  have gtIff (left right : Int) : compare left right = .gt ↔ right < left := by
    change compareOfLessAndEq left right = .gt ↔ _
    exact compareOfLessAndEq_eq_gt Int.le_antisymm Int.le_total Int.not_le _ _
  have notMiddleLeft : ¬ middleValue.value < leftValue.value := by
    intro less
    exact leftMiddle ((gtIff _ _).mpr less)
  have notRightMiddle : ¬ rightValue.value < middleValue.value := by
    intro less
    exact middleRight ((gtIff _ _).mpr less)
  intro greater
  have rightLeft := (gtIff _ _).mp greater
  omega

theorem indexRowLess_false_reverse_valueLe_text (index : Core.Index)
    (left right : Core.Row)
    (leftText : ∃ value : PhysicalCodec.Text,
      left.value index.column = .text value)
    (rightText : ∃ value : PhysicalCodec.Text,
      right.value index.column = .text value)
    (notLess : indexRowLess index left right = false) :
    indexRowValueLe index right left := by
  rcases leftText with ⟨leftValue, leftEqual⟩
  rcases rightText with ⟨rightValue, rightEqual⟩
  unfold indexRowLess at notLess
  unfold indexRowValueLe
  simp only [leftEqual, rightEqual, PhysicalQuery.compareValue] at notLess ⊢
  intro greater
  have forward : compare leftValue.bytes rightValue.bytes = .lt :=
    Std.OrientedCmp.lt_of_gt greater
  rw [forward] at notLess
  contradiction

theorem indexRowValueLe_trans_text (index : Core.Index)
    (left middle right : Core.Row)
    (leftText : ∃ value : PhysicalCodec.Text,
      left.value index.column = .text value)
    (middleText : ∃ value : PhysicalCodec.Text,
      middle.value index.column = .text value)
    (rightText : ∃ value : PhysicalCodec.Text,
      right.value index.column = .text value)
    (leftMiddle : indexRowValueLe index left middle)
    (middleRight : indexRowValueLe index middle right) :
    indexRowValueLe index left right := by
  rcases leftText with ⟨leftValue, leftEqual⟩
  rcases middleText with ⟨middleValue, middleEqual⟩
  rcases rightText with ⟨rightValue, rightEqual⟩
  unfold indexRowValueLe at leftMiddle middleRight ⊢
  simp only [leftEqual, middleEqual, rightEqual,
    PhysicalQuery.compareValue] at leftMiddle middleRight ⊢
  have leftMiddleLE :
      (compare leftValue.bytes middleValue.bytes).isLE := by
    cases result : compare leftValue.bytes middleValue.bytes <;>
      simp_all
  have middleRightLE :
      (compare middleValue.bytes rightValue.bytes).isLE := by
    cases result : compare middleValue.bytes rightValue.bytes <;>
      simp_all
  have leftRightLE :=
    Std.TransOrd.isLE_trans leftMiddleLE middleRightLE
  intro greater
  rw [greater] at leftRightLE
  contradiction

def insertIndexRow (index : Core.Index) (row : Core.Row) :
    List Core.Row → List Core.Row
  | [] => [row]
  | candidate :: rows =>
      if indexRowLess index row candidate then row :: candidate :: rows
      else candidate :: insertIndexRow index row rows

theorem insertIndexRow_perm (index : Core.Index) (row : Core.Row)
    (rows : List Core.Row) :
    (insertIndexRow index row rows).Perm (row :: rows) := by
  induction rows with
  | nil => rfl
  | cons candidate rows induction =>
      unfold insertIndexRow
      split
      · exact List.Perm.refl _
      · exact (induction.cons candidate).trans
          (List.Perm.swap row candidate rows)

theorem insertIndexRow_pairwise (index : Core.Index) (row : Core.Row) :
    ∀ (rows : List Core.Row),
      (∃ value : Core.Integer, row.value index.column = .integer value) →
      (∀ candidate ∈ rows, ∃ value : Core.Integer,
        candidate.value index.column = .integer value) →
      rows.Pairwise (indexRowValueLe index) →
      (insertIndexRow index row rows).Pairwise (indexRowValueLe index)
  | [], _, _, _ => by simp [insertIndexRow]
  | candidate :: rows, rowInteger, allInteger, sorted => by
      have candidateInteger := allInteger candidate (by simp)
      have tailInteger : ∀ current ∈ rows, ∃ value : Core.Integer,
          current.value index.column = .integer value := by
        intro current member
        exact allInteger current (by simp [member])
      have candidateBefore : ∀ current ∈ rows,
          indexRowValueLe index candidate current :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted := (List.pairwise_cons.mp sorted).2
      unfold insertIndexRow
      split
      next less =>
        have rowBeforeCandidate := indexRowLess_true_valueLe index row candidate
          less
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          rcases List.mem_cons.mp member with rfl | member
          · exact rowBeforeCandidate
          · exact indexRowValueLe_trans_integer index row candidate current
              rowInteger candidateInteger (tailInteger current member)
              rowBeforeCandidate
              (candidateBefore current member)
        · exact sorted
      next notLess =>
        have notLessFalse : indexRowLess index row candidate = false :=
          (Bool.not_eq_true _).mp notLess
        have candidateBeforeRow := indexRowLess_false_reverse_valueLe index
          row candidate rowInteger candidateInteger notLessFalse
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          have sourceMember : current ∈ row :: rows :=
            (insertIndexRow_perm index row rows).subset member
          rcases List.mem_cons.mp sourceMember with rfl | sourceMember
          · exact candidateBeforeRow
          · exact candidateBefore current sourceMember
        · exact insertIndexRow_pairwise index row rows rowInteger tailInteger
            tailSorted

theorem insertIndexRow_pairwise_text (index : Core.Index) (row : Core.Row) :
    ∀ (rows : List Core.Row),
      (∃ value : PhysicalCodec.Text,
        row.value index.column = .text value) →
      (∀ candidate ∈ rows, ∃ value : PhysicalCodec.Text,
        candidate.value index.column = .text value) →
      rows.Pairwise (indexRowValueLe index) →
      (insertIndexRow index row rows).Pairwise (indexRowValueLe index)
  | [], _, _, _ => by simp [insertIndexRow]
  | candidate :: rows, rowText, allText, sorted => by
      have candidateText := allText candidate (by simp)
      have tailText : ∀ current ∈ rows, ∃ value : PhysicalCodec.Text,
          current.value index.column = .text value := by
        intro current member
        exact allText current (by simp [member])
      have candidateBefore : ∀ current ∈ rows,
          indexRowValueLe index candidate current :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted := (List.pairwise_cons.mp sorted).2
      unfold insertIndexRow
      split
      next less =>
        have rowBeforeCandidate := indexRowLess_true_valueLe index row candidate
          less
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          rcases List.mem_cons.mp member with rfl | member
          · exact rowBeforeCandidate
          · exact indexRowValueLe_trans_text index row candidate current
              rowText candidateText (tailText current member)
              rowBeforeCandidate (candidateBefore current member)
        · exact sorted
      next notLess =>
        have notLessFalse : indexRowLess index row candidate = false :=
          (Bool.not_eq_true _).mp notLess
        have candidateBeforeRow := indexRowLess_false_reverse_valueLe_text index
          row candidate rowText candidateText notLessFalse
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          have sourceMember : current ∈ row :: rows :=
            (insertIndexRow_perm index row rows).subset member
          rcases List.mem_cons.mp sourceMember with rfl | sourceMember
          · exact candidateBeforeRow
          · exact candidateBefore current sourceMember
        · exact insertIndexRow_pairwise_text index row rows rowText tailText
            tailSorted

theorem foldInsertIndexRow_pairwise (index : Core.Index) :
    ∀ (rows accumulator : List Core.Row),
      (∀ row ∈ rows, ∃ value : Core.Integer,
        row.value index.column = .integer value) →
      (∀ row ∈ accumulator, ∃ value : Core.Integer,
        row.value index.column = .integer value) →
      accumulator.Pairwise (indexRowValueLe index) →
      (rows.foldl (fun sorted row => insertIndexRow index row sorted)
        accumulator).Pairwise (indexRowValueLe index)
  | [], _, _, _, sorted => by simpa
  | row :: rows, accumulator, allRows, allAccumulator, sorted => by
      have rowInteger := allRows row (by simp)
      have tailInteger : ∀ current ∈ rows, ∃ value : Core.Integer,
          current.value index.column = .integer value := by
        intro current member
        exact allRows current (by simp [member])
      have insertedInteger : ∀ current ∈ insertIndexRow index row accumulator,
          ∃ value : Core.Integer,
            current.value index.column = .integer value := by
        intro current member
        have sourceMember : current ∈ row :: accumulator :=
          (insertIndexRow_perm index row accumulator).subset member
        rcases List.mem_cons.mp sourceMember with rfl | sourceMember
        · exact rowInteger
        · exact allAccumulator current sourceMember
      exact foldInsertIndexRow_pairwise index rows
        (insertIndexRow index row accumulator) tailInteger insertedInteger
        (insertIndexRow_pairwise index row accumulator rowInteger
          allAccumulator sorted)

theorem foldInsertIndexRow_pairwise_text (index : Core.Index) :
    ∀ (rows accumulator : List Core.Row),
      (∀ row ∈ rows, ∃ value : PhysicalCodec.Text,
        row.value index.column = .text value) →
      (∀ row ∈ accumulator, ∃ value : PhysicalCodec.Text,
        row.value index.column = .text value) →
      accumulator.Pairwise (indexRowValueLe index) →
      (rows.foldl (fun sorted row => insertIndexRow index row sorted)
        accumulator).Pairwise (indexRowValueLe index)
  | [], _, _, _, sorted => by simpa
  | row :: rows, accumulator, allRows, allAccumulator, sorted => by
      have rowText := allRows row (by simp)
      have tailText : ∀ current ∈ rows, ∃ value : PhysicalCodec.Text,
          current.value index.column = .text value := by
        intro current member
        exact allRows current (by simp [member])
      have insertedText : ∀ current ∈ insertIndexRow index row accumulator,
          ∃ value : PhysicalCodec.Text,
            current.value index.column = .text value := by
        intro current member
        have sourceMember : current ∈ row :: accumulator :=
          (insertIndexRow_perm index row accumulator).subset member
        rcases List.mem_cons.mp sourceMember with rfl | sourceMember
        · exact rowText
        · exact allAccumulator current sourceMember
      exact foldInsertIndexRow_pairwise_text index rows
        (insertIndexRow index row accumulator) tailText insertedText
        (insertIndexRow_pairwise_text index row accumulator rowText
          allAccumulator sorted)

/-- The executable INTEGER key used by the verified merge-sort fast path.
Non-INTEGER values receive a harmless default; the fast path is selected only
after `indexValuesInteger` has certified every source row.  Keeping the key
total makes the comparator's order laws unconditional and therefore suitable
for `List.mergeSort`. -/
def integerIndexKey (index : Core.Index) (row : Core.Row) : Int :=
  match row.value index.column with
  | .integer value => value.value
  | _ => 0

/-- Lexicographic non-strict order on `(indexed INTEGER value, rowid)`.
The rowid component makes the physical index order deterministic when indexed
values are equal. -/
def integerIndexRowLe (index : Core.Index)
    (left right : Core.Row) : Bool :=
  decide (integerIndexKey index left < integerIndexKey index right ∨
    (integerIndexKey index left = integerIndexKey index right ∧
      left.rowid.value ≤ right.rowid.value))

theorem integerIndexRowLe_trans (index : Core.Index)
    (left middle right : Core.Row)
    (leftMiddle : integerIndexRowLe index left middle = true)
    (middleRight : integerIndexRowLe index middle right = true) :
    integerIndexRowLe index left right = true := by
  simp only [integerIndexRowLe, decide_eq_true_eq] at leftMiddle middleRight ⊢
  omega

theorem integerIndexRowLe_total (index : Core.Index)
    (left right : Core.Row) :
    (integerIndexRowLe index left right ||
      integerIndexRowLe index right left) = true := by
  simp only [integerIndexRowLe, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem integerIndexRowLe_valueLe (index : Core.Index)
    (left right : Core.Row)
    (leftInteger : ∃ value : Core.Integer,
      left.value index.column = .integer value)
    (rightInteger : ∃ value : Core.Integer,
      right.value index.column = .integer value)
    (ordered : integerIndexRowLe index left right = true) :
    indexRowValueLe index left right := by
  rcases leftInteger with ⟨leftValue, leftEqual⟩
  rcases rightInteger with ⟨rightValue, rightEqual⟩
  simp only [integerIndexRowLe, integerIndexKey, leftEqual, rightEqual,
    decide_eq_true_eq] at ordered
  unfold indexRowValueLe
  simp only [leftEqual, rightEqual, PhysicalQuery.compareValue]
  have gtIff : compare leftValue.value rightValue.value = .gt ↔
      rightValue.value < leftValue.value := by
    change compareOfLessAndEq leftValue.value rightValue.value = .gt ↔ _
    exact compareOfLessAndEq_eq_gt Int.le_antisymm Int.le_total Int.not_le _ _
  intro greater
  have := gtIff.mp greater
  omega

theorem pairwise_integerIndexRowLe_valueLe (index : Core.Index) :
    ∀ (rows : List Core.Row),
      (∀ row ∈ rows, ∃ value : Core.Integer,
        row.value index.column = .integer value) →
      rows.Pairwise (fun left right =>
        integerIndexRowLe index left right = true) →
      rows.Pairwise (indexRowValueLe index)
  | [], _, _ => by simp
  | row :: rows, allInteger, sorted => by
      apply List.pairwise_cons.mpr
      constructor
      · intro candidate member
        exact integerIndexRowLe_valueLe index row candidate
          (allInteger row (by simp))
          (allInteger candidate (by simp [member]))
          ((List.pairwise_cons.mp sorted).1 candidate member)
      · exact pairwise_integerIndexRowLe_valueLe index rows
          (fun candidate member => allInteger candidate (by simp [member]))
          (List.pairwise_cons.mp sorted).2

/-- Total executable TEXT sort key.  The fallback key is unreachable on the
certified fast path but keeps the comparator lawful over all `Core.Row`s. -/
def textIndexSortKey (index : Core.Index) (row : Core.Row) :
    List UInt8 × Int :=
  let bytes := match row.value index.column with
    | .text value => value.bytes
    | _ => []
  (bytes, row.rowid.value)

def textIndexRowLe (index : Core.Index) (left right : Core.Row) : Bool :=
  (compare (textIndexSortKey index left) (textIndexSortKey index right)).isLE

theorem textIndexRowLe_trans (index : Core.Index)
    (left middle right : Core.Row)
    (leftMiddle : textIndexRowLe index left middle = true)
    (middleRight : textIndexRowLe index middle right = true) :
    textIndexRowLe index left right = true := by
  unfold textIndexRowLe at leftMiddle middleRight ⊢
  exact Std.TransOrd.isLE_trans leftMiddle middleRight

theorem textIndexRowLe_total (index : Core.Index)
    (left right : Core.Row) :
    (textIndexRowLe index left right || textIndexRowLe index right left) =
      true := by
  unfold textIndexRowLe
  cases comparison : compare (textIndexSortKey index left)
      (textIndexSortKey index right) with
  | lt => simp [comparison]
  | eq => simp [comparison]
  | gt =>
      have reverse : compare (textIndexSortKey index right)
          (textIndexSortKey index left) = .lt :=
        Std.OrientedCmp.lt_of_gt comparison
      simp [comparison, reverse]

theorem textIndexRowLe_valueLe (index : Core.Index)
    (left right : Core.Row)
    (leftText : ∃ value : PhysicalCodec.Text,
      left.value index.column = .text value)
    (rightText : ∃ value : PhysicalCodec.Text,
      right.value index.column = .text value)
    (ordered : textIndexRowLe index left right = true) :
    indexRowValueLe index left right := by
  rcases leftText with ⟨leftValue, leftEqual⟩
  rcases rightText with ⟨rightValue, rightEqual⟩
  unfold textIndexRowLe textIndexSortKey at ordered
  simp only [leftEqual, rightEqual] at ordered
  unfold indexRowValueLe
  simp only [leftEqual, rightEqual, PhysicalQuery.compareValue]
  intro greater
  have keyGreater : compare (leftValue.bytes, left.rowid.value)
      (rightValue.bytes, right.rowid.value) = .gt := by
    change (compare leftValue.bytes rightValue.bytes).then
      (compare left.rowid.value right.rowid.value) = .gt
    rw [greater]
    rfl
  rw [keyGreater] at ordered
  contradiction

theorem pairwise_textIndexRowLe_valueLe (index : Core.Index) :
    ∀ (rows : List Core.Row),
      (∀ row ∈ rows, ∃ value : PhysicalCodec.Text,
        row.value index.column = .text value) →
      rows.Pairwise (fun left right => textIndexRowLe index left right = true) →
      rows.Pairwise (indexRowValueLe index)
  | [], _, _ => by simp
  | row :: rows, allText, sorted => by
      apply List.pairwise_cons.mpr
      constructor
      · intro candidate member
        exact textIndexRowLe_valueLe index row candidate
          (allText row (by simp))
          (allText candidate (by simp [member]))
          ((List.pairwise_cons.mp sorted).1 candidate member)
      · exact pairwise_textIndexRowLe_valueLe index rows
          (fun candidate member => allText candidate (by simp [member]))
          (List.pairwise_cons.mp sorted).2

def sortedIndexRows (table : Core.Table) (index : Core.Index) :
    List Core.Row :=
  if indexValuesInteger table index then
    table.rows.mergeSort (integerIndexRowLe index)
  else if indexValuesText table index then
    table.rows.mergeSort (textIndexRowLe index)
  else table.rows.foldl (fun rows row => insertIndexRow index row rows) []

/-- An INTEGER-certified generated index is ordered by its SQL comparison
value. Rowid tie-breaking may refine equal values, but never reverses their
value order. -/
theorem sortedIndexRows_pairwise_valueLe (table : Core.Table)
    (index : Core.Index)
    (integers : indexValuesInteger table index = true) :
    (sortedIndexRows table index).Pairwise (indexRowValueLe index) := by
  rw [sortedIndexRows, if_pos integers]
  apply pairwise_integerIndexRowLe_valueLe index
  · intro row member
    exact (indexValuesInteger_iff table index).mp integers row
      (List.mem_mergeSort.mp member)
  · exact List.pairwise_mergeSort (integerIndexRowLe_trans index)
      (integerIndexRowLe_total index) table.rows

theorem sortedIndexRows_pairwise_valueLe_text (table : Core.Table)
    (index : Core.Index)
    (texts : indexValuesText table index = true) :
    (sortedIndexRows table index).Pairwise (indexRowValueLe index) := by
  unfold sortedIndexRows
  by_cases integers : indexValuesInteger table index = true
  · rw [if_pos integers]
    have empty : table.rows = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro row member
      rcases (indexValuesInteger_iff table index).mp integers row member with
        ⟨integer, integerEqual⟩
      rcases (indexValuesText_iff table index).mp texts row member with
        ⟨text, textEqual⟩
      rw [integerEqual] at textEqual
      contradiction
    simp [empty]
  · rw [if_neg integers]
    rw [if_pos texts]
    apply pairwise_textIndexRowLe_valueLe index
    · intro row member
      exact (indexValuesText_iff table index).mp texts row
        (List.mem_mergeSort.mp member)
    · exact List.pairwise_mergeSort (textIndexRowLe_trans index)
        (textIndexRowLe_total index) table.rows

theorem foldInsertIndexRow_perm (index : Core.Index)
    (rows accumulator : List Core.Row) :
    (rows.foldl (fun sorted row => insertIndexRow index row sorted)
      accumulator).Perm (rows ++ accumulator) := by
  induction rows generalizing accumulator with
  | nil => exact List.Perm.refl _
  | cons row rows induction =>
      have tail := induction (insertIndexRow index row accumulator)
      have inserted :=
        (insertIndexRow_perm index row accumulator).append_left rows
      exact tail.trans (inserted.trans List.perm_middle)

theorem sortedIndexRows_perm (table : Core.Table) (index : Core.Index) :
    (sortedIndexRows table index).Perm table.rows := by
  unfold sortedIndexRows
  split
  · exact List.mergeSort_perm table.rows (integerIndexRowLe index)
  · split
    · exact List.mergeSort_perm table.rows (textIndexRowLe index)
    · simpa using foldInsertIndexRow_perm index table.rows []

def indexCells (table : Core.Table) (index : Core.Index) :
    Option (List (List UInt8)) :=
  (sortedIndexRows table index).mapM (indexCell? index)

/-- Index cells split into leaf-sized runs, same byte-driven policy as tables. -/
def indexLeaves (table : Core.Table) (index : Core.Index) :
    Option (List (List (List UInt8))) := do
  let cells ← indexCells table index
  some (CellPagination.paginateCells cells)

theorem sortedIndexRows_canonicalize (table : Core.Table) (index : Core.Index) :
    sortedIndexRows table.canonicalize index = sortedIndexRows table index := by
  simp [sortedIndexRows, Core.Table.canonicalize_rows]

theorem indexCells_canonicalize (table : Core.Table) (index : Core.Index) :
    indexCells table.canonicalize index = indexCells table index := by
  unfold indexCells
  rw [sortedIndexRows_canonicalize]

theorem indexLeaves_canonicalize (table : Core.Table) (index : Core.Index) :
    indexLeaves table.canonicalize index = indexLeaves table index := by
  unfold indexLeaves
  rw [indexCells_canonicalize]

def indexLeafPage? (cells : List (List UInt8)) : Option Page := do
  let body ← leafBody? 10 0 cells
  some { bytes := body.bytes, length_eq := by simpa using body.length_eq }

/-- In an index B-tree the interior cells are *themselves* index entries, not
mere separators as in a table B-tree. So the promoted key must be removed from
its leaf, or the index would hold it twice and C SQLite reports
"wrong # of entries in index".

Splits leaves into (leaves with promoted keys removed, promoted keys). -/
def promoteSeparators :
    List (List (List UInt8)) → List (List (List UInt8)) × List (List UInt8)
  | [] => ([], [])
  | [last] => ([last], [])
  | leaf :: rest =>
      let (trimmed, separators) := promoteSeparators rest
      match leaf.getLast? with
      | some key => (leaf.dropLast :: trimmed, key :: separators)
      | none => (leaf :: trimmed, separators)

/-- Interior index page (type 2). An interior index cell is a 4-byte left-child
page number followed by the same payload an index leaf cell carries. -/
def indexInteriorPage? (firstLeaf : Nat) (separators : List (List UInt8))
    (leafCount : Nat) : Option Page := do
  let rightmostNumber := firstLeaf + leafCount - 1
  if rightmostBound : rightmostNumber < 2 ^ 32 then
    let rightmost : U32Value := ⟨rightmostNumber, by simpa using rightmostBound⟩
    let cells ← (separators.zipIdx).mapM fun pair => do
      let childNumber := firstLeaf + pair.2
      if childBound : childNumber < 2 ^ 32 then
        let child : U32Value := ⟨childNumber, by simpa using childBound⟩
        some (PhysicalTableBTree.encodeU32Nat child.val ++ pair.1)
      else none
    if fits : PhysicalTableBTree.InteriorPageFit cells then
      -- interiorPageBody emits an interior TABLE header (type 5); an interior
      -- index page is type 2. Patch the tag, as leafBody? does for leaves.
      some {
        bytes := replaceFirst 2 (PhysicalTableBTree.interiorPageBody rightmost cells)
        length_eq := by
          rw [replaceFirst_length]
          exact PhysicalTableBTree.interiorPageBody_length rightmost cells fits }
    else none
  else none

/-- Pages for one index, in page-number order: root first, then leaves. -/
def indexPages? (rootPage : Nat) (leaves : List (List (List UInt8))) :
    Option (List Page) :=
  match leaves with
  | [] => do let page ← indexLeafPage? []; some [page]
  | [only] => do let page ← indexLeafPage? only; some [page]
  | _ => do
      let (trimmed, separators) := promoteSeparators leaves
      let root ← indexInteriorPage? (rootPage + 1) separators trimmed.length
      let leafPages ← trimmed.mapM indexLeafPage?
      some (root :: leafPages)

structure PageList (length : Nat) where
  pages : List Page
  pages_length : pages.length = length

def mapPages? {A : Type} (makePage : A → Option Page) :
    (values : List A) → Option (PageList values.length)
  | [] => some ⟨[], rfl⟩
  | value :: values => do
      let page ← makePage value
      let remaining ← mapPages? makePage values
      some ⟨page :: remaining.pages, by simp [remaining.pages_length]⟩

/-- Every table's pages, concatenated in page-number order. -/
def allTablePages (layouts : List TableLayout) : Option (List Page) := do
  let grouped ← layouts.mapM tablePages?
  some grouped.flatten

def allIndexPages (layouts : List IndexLayout) : Option (List Page) := do
  let grouped ← layouts.mapM fun layout => indexPages? layout.rootPage layout.leaves
  some grouped.flatten

/-- One table's layout and already-built pages. Keeping these together avoids
recomputing the page grouping and gives the codec proof an aligned witness. -/
structure TableEncoding where
  layout : TableLayout
  pages : List Page

def encodeTables : Nat → List Core.Table → Option (List TableEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let leaves ← tableLeaves table
      let layout : TableLayout := ⟨nextPage, leaves⟩
      let physicalPages ← tablePages? layout
      let remaining ← encodeTables (nextPage + tableFootprint leaves) tables
      some (⟨layout, physicalPages⟩ :: remaining)

theorem encodeTables_canonicalize : ∀ (nextPage : Nat)
    (tables : List Core.Table),
    encodeTables nextPage (tables.map Core.Table.canonicalize) =
      encodeTables nextPage tables
  | _, [] => rfl
  | nextPage, table :: tables => by
      simp only [List.map_cons, encodeTables]
      rw [tableLeaves_canonicalize]
      cases leavesResult : tableLeaves table with
      | none => rfl
      | some leaves =>
          simp only [Option.bind_eq_bind, Option.bind]
          cases pagesResult : tablePages? ⟨nextPage, leaves⟩ with
          | none => rfl
          | some pages =>
              simp only
              rw [encodeTables_canonicalize]

def tableLayoutsOf (encodings : List TableEncoding) : List TableLayout :=
  encodings.map (·.layout)

def tablePagesOf (encodings : List TableEncoding) : List Page :=
  encodings.flatMap (·.pages)

structure IndexEncoding where
  table : Core.Table
  index : Core.Index
  layout : IndexLayout
  pages : List Page

def IndexEncoding.canonicalize (encoding : IndexEncoding) : IndexEncoding := {
  encoding with table := encoding.table.canonicalize }

@[simp] theorem IndexEncoding.canonicalize_pages (encoding : IndexEncoding) :
    encoding.canonicalize.pages = encoding.pages := rfl

def encodeIndexes : Nat → List (Core.Table × Core.Index) →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, indexed :: indexes => do
      let leaves ← indexLeaves indexed.1 indexed.2
      let layout : IndexLayout := ⟨nextPage, leaves⟩
      let physicalPages ← indexPages? layout.rootPage layout.leaves
      let remaining ← encodeIndexes (nextPage + tableFootprint leaves) indexes
      some (⟨indexed.1, indexed.2, layout, physicalPages⟩ :: remaining)

def indexPagesOf (encodings : List IndexEncoding) : List Page :=
  encodings.flatMap (·.pages)

def IndexEncoding.catalogEntry (encoding : IndexEncoding) : CatalogEntry := {
  kind := "index"
  name := encoding.index.name
  table := encoding.table.schema.name
  rootPage := encoding.layout.rootPage
  sql := indexSQL encoding.table encoding.index
  sqlIsNull := encoding.index.isImplicitPrimary encoding.table.schema }

@[simp] theorem IndexEncoding.canonicalize_catalogEntry
    (encoding : IndexEncoding) :
    encoding.canonicalize.catalogEntry = encoding.catalogEntry := by
  unfold IndexEncoding.canonicalize IndexEncoding.catalogEntry indexSQL
  simp

def indexEntriesOf (encodings : List IndexEncoding) : List CatalogEntry :=
  encodings.map (·.catalogEntry)

theorem indexEntriesOf_kind (encodings : List IndexEncoding)
    (entry : CatalogEntry) (member : entry ∈ indexEntriesOf encodings) :
    entry.kind = "index" := by
  unfold indexEntriesOf at member
  rcases List.mem_map.mp member with ⟨encoding, _, rfl⟩
  rfl

/-- First unused page after an aligned run of already-built index encodings. -/
def indexEndPage (nextPage : Nat) (encodings : List IndexEncoding) : Nat :=
  encodings.foldl
    (fun page encoding => page + tableFootprint encoding.layout.leaves) nextPage

/-- Encode indexes table by table. Besides matching catalog order, this exposes
the table boundary needed by the decoder proof instead of recovering that
boundary from a flattened list after the fact. -/
def encodeIndexTableGroups : Nat → List Core.Table →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let current ← encodeIndexes nextPage
        (table.indexes.map fun index => (table, index))
      let remaining ← encodeIndexTableGroups (indexEndPage nextPage current) tables
      some (current ++ remaining)

theorem encodeIndexes_canonicalize : ∀ (nextPage : Nat)
    (table : Core.Table) (indexes : List Core.Index),
    encodeIndexes nextPage
        (indexes.map fun index => (table.canonicalize, index)) =
      (encodeIndexes nextPage
        (indexes.map fun index => (table, index))).map
          (List.map IndexEncoding.canonicalize)
  | _, _, [] => rfl
  | nextPage, table, index :: indexes => by
      simp only [List.map_cons, encodeIndexes]
      rw [indexLeaves_canonicalize]
      cases leavesResult : indexLeaves table index with
      | none => rfl
      | some leaves =>
          simp only [Option.bind_eq_bind, Option.bind]
          cases pagesResult : indexPages? nextPage leaves with
          | none => rfl
          | some pages =>
              simp only
              rw [encodeIndexes_canonicalize]
              cases remainingResult : encodeIndexes
                  (nextPage + tableFootprint leaves)
                  (indexes.map fun candidate => (table, candidate)) with
              | none => rfl
              | some remaining => rfl

theorem indexEndPage_canonicalize : ∀ (encodings : List IndexEncoding)
    (nextPage : Nat),
    indexEndPage nextPage (encodings.map IndexEncoding.canonicalize) =
      indexEndPage nextPage encodings
  | [], _ => rfl
  | encoding :: encodings, nextPage => by
      simp only [List.map_cons, indexEndPage, List.foldl_cons,
        IndexEncoding.canonicalize]
      exact indexEndPage_canonicalize encodings
        (nextPage + tableFootprint encoding.layout.leaves)

theorem encodeIndexTableGroups_canonicalize : ∀ (nextPage : Nat)
    (tables : List Core.Table),
    encodeIndexTableGroups nextPage (tables.map Core.Table.canonicalize) =
      (encodeIndexTableGroups nextPage tables).map
        (List.map IndexEncoding.canonicalize)
  | _, [] => rfl
  | nextPage, table :: tables => by
      simp only [List.map_cons, encodeIndexTableGroups,
        Core.Table.canonicalize_indexes]
      rw [encodeIndexes_canonicalize]
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => rfl
      | some current =>
          rw [show Option.map (List.map IndexEncoding.canonicalize)
              (some current) =
                some (current.map IndexEncoding.canonicalize) by rfl]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [indexEndPage_canonicalize, encodeIndexTableGroups_canonicalize]
          cases remainingResult : encodeIndexTableGroups
              (indexEndPage nextPage current) tables with
          | none => rfl
          | some remaining => simp

@[simp] theorem indexPagesOf_canonicalize
    (encodings : List IndexEncoding) :
    indexPagesOf (encodings.map IndexEncoding.canonicalize) =
      indexPagesOf encodings := by
  unfold indexPagesOf
  simp only [List.flatMap, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro encoding member
  rfl

@[simp] theorem indexEntriesOf_canonicalize
    (encodings : List IndexEncoding) :
    indexEntriesOf (encodings.map IndexEncoding.canonicalize) =
      indexEntriesOf encodings := by
  simp [indexEntriesOf, List.map_map, Function.comp_def]

theorem tableEntriesFor_canonicalize : ∀ (tables : List Core.Table)
    (layouts : List TableLayout),
    tableEntriesFor (tables.map Core.Table.canonicalize) layouts =
      tableEntriesFor tables layouts
  | [], _ => rfl
  | _ :: _, [] => rfl
  | table :: tables, _ :: layouts => by
      simp only [List.map_cons, tableEntriesFor,
        Core.Table.canonicalize_schema, tableSQL, Core.Table.catalogSQL, Core.Table.canonicalize]
      rw [tableEntriesFor_canonicalize]

theorem tableEntries_canonicalize (database : Core.Database)
    (layouts : List TableLayout) :
    tableEntries database.canonicalize layouts = tableEntries database layouts := by
  unfold tableEntries Core.Database.canonicalize
  exact tableEntriesFor_canonicalize database.tables layouts

theorem encodeIndexes_pairs : ∀ (nextPage : Nat)
    (indexes : List (Core.Table × Core.Index)) (encodings : List IndexEncoding),
    encodeIndexes nextPage indexes = some encodings →
      encodings.map (fun encoding => (encoding.table, encoding.index)) = indexes
  | _, [], encodings, encoded => by
      simp only [encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, indexed :: indexes, encodings, encoded => by
      simp only [encodeIndexes, Option.bind_eq_bind, Option.bind] at encoded
      cases leavesResult : indexLeaves indexed.1 indexed.2 with
      | none => simp [leavesResult] at encoded
      | some leaves =>
        simp only [leavesResult] at encoded
        let layout : IndexLayout := ⟨nextPage, leaves⟩
        cases pagesResult : indexPages? layout.rootPage layout.leaves with
        | none => simp [layout, pagesResult] at encoded
        | some physicalPages =>
          simp only [layout, pagesResult] at encoded
          cases remainingResult : encodeIndexes
              (nextPage + tableFootprint leaves) indexes with
          | none => simp [remainingResult] at encoded
          | some remaining =>
            simp only [remainingResult] at encoded
            injection encoded with equal
            subst encodings
            simp only [List.map_cons, Prod.mk.injEq, true_and]
            simpa using encodeIndexes_pairs
              (nextPage + tableFootprint leaves) indexes remaining
              remainingResult

theorem encodeIndexTableGroups_tables : ∀ (nextPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups nextPage tables = some encodings →
      ∀ encoding ∈ encodings, encoding.table ∈ tables
  | _, [], encodings, encoded => by
      simp only [encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      simp
  | nextPage, table :: tables, encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind] at encoded
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : encodeIndexTableGroups
            (indexEndPage nextPage current) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult] at encoded
          injection encoded with equal
          subst encodings
          intro encoding member
          simp only [List.mem_append] at member
          rcases member with currentMember | remainingMember
          ·
            have aligned := encodeIndexes_pairs nextPage
              (table.indexes.map fun index => (table, index)) current currentResult
            have mapped : (encoding.table, encoding.index) ∈
                current.map (fun candidate => (candidate.table, candidate.index)) :=
              List.mem_map_of_mem currentMember
            rw [aligned] at mapped
            rcases List.mem_map.mp mapped with ⟨index, _, pairEqual⟩
            have tableEqual : encoding.table = table := by
              exact (Prod.mk.inj pairEqual.symm).1
            simp [tableEqual]
          · right
            exact encodeIndexTableGroups_tables
              (indexEndPage nextPage current) tables remaining remainingResult
              encoding remainingMember

structure Image where
  database : Core.Database
  pages : List Page

/-- Number of pages actually emitted. With multi-leaf tables this is no longer
a closed formula over table and index counts, so it is read off the layout. -/
def Image.pageCount (image : Image) : Nat := image.pages.length

def encode (database : Core.Database) : Option Image := do
  let tableEncodings ← encodeTables 2 database.tables
  let layouts := tableLayoutsOf tableEncodings
  let indexEncodings ← encodeIndexTableGroups (indexRootBase layouts)
    database.tables
  let entries := tableEntries database layouts ++ indexEntriesOf indexEncodings
  let remaining := tablePagesOf tableEncodings ++ indexPagesOf indexEncodings
  let total := 1 + remaining.length
  if countFits : total < 2 ^ 32 then
    let count : U32Value := ⟨total, by simpa using countFits⟩
    let schema ← schemaPageForEntries? entries count
    some { database, pages := schema :: remaining }
  else none

/-- Canonicalizing the in-memory persistent tree may change its split shape,
but cannot change a single emitted SQLite page.  This is the serialization
boundary needed when physical topology is intentionally absent from logical
database equivalence. -/
theorem encode_canonicalize_pages (database : Core.Database) :
    (encode database.canonicalize).map (fun image => image.pages) =
      (encode database).map (fun image => image.pages) := by
  unfold encode Core.Database.canonicalize
  simp only
  rw [encodeTables_canonicalize]
  cases tableResult : encodeTables 2 database.tables with
  | none => rfl
  | some tableEncodings =>
      simp only [Option.bind_eq_bind, Option.bind]
      let layouts := tableLayoutsOf tableEncodings
      rw [encodeIndexTableGroups_canonicalize]
      cases indexResult : encodeIndexTableGroups (indexRootBase layouts)
          database.tables with
      | none => rfl
      | some indexEncodings =>
          rw [show Option.map (List.map IndexEncoding.canonicalize)
              (some indexEncodings) =
                some (indexEncodings.map IndexEncoding.canonicalize) by rfl]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [indexEntriesOf_canonicalize, indexPagesOf_canonicalize]
          have entriesEqual := tableEntries_canonicalize database layouts
          unfold Core.Database.canonicalize at entriesEqual
          rw [entriesEqual]
          dsimp only [layouts]
          split
          next =>
            cases schemaResult : schemaPageForEntries?
                (tableEntries database (tableLayoutsOf tableEncodings) ++
                  indexEntriesOf indexEncodings)
                ⟨1 + (tablePagesOf tableEncodings ++
                  indexPagesOf indexEncodings).length, by assumption⟩ <;> rfl
          next => rfl

theorem encode_header {database : Core.Database} {image : Image}
    (encoded : encode database = some image) :
    ∃ (count : U32Value) (schema : Page) (remaining : List Page)
      (body : List UInt8),
      image.pages = schema :: remaining ∧
      image.pageCount = count.val ∧
      schema.bytes = encodeDatabaseHeader (databaseHeader count) ++ body := by
  unfold encode at encoded
  cases tableResult : encodeTables 2 database.tables with
  | none => simp [tableResult] at encoded
  | some tableEncodings =>
    simp only [tableResult, Option.bind_eq_bind, Option.bind] at encoded
    let layouts := tableLayoutsOf tableEncodings
    cases indexResult : encodeIndexTableGroups
        (indexRootBase layouts) database.tables with
    | none => simp [layouts, indexResult] at encoded
    | some indexEncodings =>
      simp only [layouts, indexResult] at encoded
      split at encoded
      next countFits =>
        let remaining := tablePagesOf tableEncodings ++ indexPagesOf indexEncodings
        let count : U32Value :=
          ⟨1 + (tablePagesOf tableEncodings ++
            indexPagesOf indexEncodings).length, countFits⟩
        cases schemaResult : schemaPageForEntries?
            (tableEntries database layouts ++ indexEntriesOf indexEncodings) count with
        | none =>
          simp only [count, layouts] at schemaResult
          rw [schemaResult] at encoded
          contradiction
        | some schema =>
          have headerBuilt := schemaResult
          simp only [count, layouts] at schemaResult
          rw [schemaResult] at encoded
          simp only [Option.bind_eq_bind, Option.bind] at encoded
          injection encoded with equal
          subst image
          rcases schemaPageForEntries_header headerBuilt with ⟨body, bytes⟩
          refine ⟨count, schema, remaining, body, rfl, ?_, bytes⟩
          simp [Image.pageCount, count, remaining, Nat.add_comm]
      next countTooLarge => contradiction

def Image.fileBytes (image : Image) : List UInt8 :=
  image.pages.flatMap Page.bytes

theorem Image.fileBytes_length (image : Image) :
    image.fileBytes.length = PhysicalCodec.pageSize * image.pageCount := by
  unfold Image.fileBytes Image.pageCount
  induction image.pages with
  | nil => rfl
  | cons page pages induction =>
      simp [page.length_eq, induction, Nat.mul_add, Nat.add_comm]

end CoreFile
end SQLeanite
