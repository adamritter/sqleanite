import SQLeanite.CellPagination
import SQLeanite.CoreEngine.RowValue
import SQLeanite.CoreRecord
import SQLeanite.PhysicalTableBTree

namespace SQLeanite
namespace CoreFile
attribute [local instance] lexOrd
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

end CoreFile

end SQLeanite
