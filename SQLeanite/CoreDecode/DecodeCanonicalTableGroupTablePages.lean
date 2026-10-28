import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeOffsets

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem decodeCanonicalTableGroup_tablePages (table : Core.Table)
    (layout : CoreFile.TableLayout) {cells : List (List UInt8)}
    {physicalPages : List CoreFile.Page}
    (encoded : CoreFile.tableCells table = some cells)
    (paged : CoreFile.tableLeaves table = some layout.leaves)
    (built : CoreFile.tablePages? layout = some physicalPages) :
    decodeCanonicalTableGroup table.schema
      (physicalPages.map CoreFile.Page.bytes) = some table.rows := by
  have leavesNonempty : layout.leaves ≠ [] := by
    unfold CoreFile.tableLeaves at paged
    rw [encoded] at paged
    simp only [Option.bind_eq_bind, Option.bind, Option.some.injEq] at paged
    rw [← paged]
    exact CellPagination.paginateCells_nonempty cells
  cases leavesShape : layout.leaves with
  | nil => exact absurd leavesShape leavesNonempty
  | cons first rest =>
    cases restShape : rest with
    | nil =>
      unfold CoreFile.tablePages? at built
      rw [leavesShape, restShape] at built
      cases pageResult : CoreFile.tableLeafPage? first with
      | none => simp [pageResult] at built
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at built
          injection built with equal
          subst physicalPages
          have leafPagesBuilt :
              layout.leaves.mapM CoreFile.tableLeafPage? = some [page] := by
            simp [leavesShape, restShape, pageResult]
          have decoded := decodeCanonicalRowsPages_tableLeaves table encoded paged
            leafPagesBuilt
          simpa [decodeCanonicalTableGroup, decodeCanonicalRowsPages] using decoded
    | cons second remaining =>
      unfold CoreFile.tablePages? at built
      rw [leavesShape, restShape] at built
      cases rootResult : CoreFile.tableInteriorPage?
          (layout.rootPage + 1) layout.leaves with
      | none =>
        have rootResult' : CoreFile.tableInteriorPage?
            (layout.rootPage + 1) (first :: second :: remaining) = none := by
          simpa [leavesShape, restShape] using rootResult
        simp [rootResult'] at built
      | some root =>
        have rootResult' : CoreFile.tableInteriorPage?
            (layout.rootPage + 1) (first :: second :: remaining) = some root := by
          simpa [leavesShape, restShape] using rootResult
        simp only [rootResult', Option.bind_eq_bind, Option.bind] at built
        cases leafPagesResult : layout.leaves.mapM CoreFile.tableLeafPage? with
        | none =>
          have leafPagesResult' :
              (first :: second :: remaining).mapM CoreFile.tableLeafPage? = none := by
            simpa [leavesShape, restShape] using leafPagesResult
          simp [leafPagesResult'] at built
        | some leafPages =>
          have leafPagesResult' :
              (first :: second :: remaining).mapM CoreFile.tableLeafPage? =
                some leafPages := by
            simpa [leavesShape, restShape] using leafPagesResult
          simp only [leafPagesResult', Option.bind_eq_bind, Option.bind] at built
          injection built with equal
          subst physicalPages
          have leafCount := canonicalInteriorLeafCount_tableInteriorPage
            (layout.rootPage + 1) layout.leaves (by simp [leavesShape, restShape])
            rootResult
          have decoded := decodeCanonicalRowsPages_tableLeaves table encoded paged
            leafPagesResult
          have pageCount := mapM_length_of_eq_some CoreFile.tableLeafPage?
            layout.leaves leafPages leafPagesResult
          cases leafPages with
          | nil => simp [leavesShape, restShape] at pageCount
          | cons leaf remainingPages =>
            simp only [List.map_cons, decodeCanonicalTableGroup]
            rw [leafCount]
            simp only [Option.bind_eq_bind, Option.bind]
            have countMatches : layout.leaves.length =
                (leaf.bytes :: remainingPages.map CoreFile.Page.bytes).length := by
              simpa using pageCount.symm
            rw [dif_pos countMatches]
            simpa [decodeCanonicalRowsPages] using decoded

def leafTableOffsets? (headerOffset : Nat) (page : List UInt8) :
    Option (List Nat) := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    let (header, afterHeader) ← decodeBTreePageHeader (page.drop headerOffset)
    match header with
    | .leafTable common => do
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        if _bounded : offsets.all (fun offset => decide (offset < page.length)) then
          some offsets
        else none
    | _ => none
  else none

/-- Page-size-polymorphic table-leaf pointer decoding for foreign SQLite
images.  The proof-oriented writer remains fixed at `PhysicalCodec.pageSize`;
only the validated read boundary selects this geometry at runtime. -/
def leafTableOffsetsFor? (pageSize headerOffset : Nat) (page : List UInt8) :
    Option (List Nat) := do
  if _pageLength : page.length = pageSize then
    let (header, afterHeader) ← decodeBTreePageHeader (page.drop headerOffset)
    match header with
    | .leafTable common => do
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        if _bounded : offsets.all (fun offset => decide (offset < page.length)) then
          some offsets
        else none
    | _ => none
  else none

def cellInputsFor? (pageSize headerOffset : Nat) (page : List UInt8) :
    Option (List (List UInt8)) := do
  let offsets ← leafTableOffsetsFor? pageSize headerOffset page
  some (offsets.map page.drop)

def cellInputs? (headerOffset : Nat) (page : List UInt8) :
    Option (List (List UInt8)) := do
  let offsets ← leafTableOffsets? headerOffset page
  some (offsets.map page.drop)

def fieldText? : RecordField → Option String
  | .text _ payload => String.fromUTF8? (ByteArray.mk payload.bytes.toArray)
  | _ => none

def fieldNat? : RecordField → Option Nat
  | .integer _ value =>
      if _nonnegative : 0 ≤ value.value then some value.value.toNat else none
  | .constantZero => some 0
  | .constantOne => some 1
  | _ => none

def fieldOptionalText? : RecordField → Option (Option String)
  | .null => some none
  | field => some <$> fieldText? field

/-- The exact standard-library UTF-8 obligation used by catalog decoding.
Keeping it explicit avoids treating the compiler implementation of
`String.fromUTF8?` as a proof. -/
def TextRoundtrips (value : String) : Prop :=
  String.fromUTF8?
    (ByteArray.mk value.toUTF8.data.toList.toArray) = some value

/-- The single library-level codec law needed to lift byte-level catalog
proofs to arbitrary SQL identifiers. It is an explicit hypothesis until the
Lean standard library exposes a theorem for its UTF-8 implementation. -/
def UTF8Roundtrips : Prop := ∀ value : String, TextRoundtrips value

instance (value : String) : Decidable (TextRoundtrips value) :=
  inferInstanceAs (Decidable
    (String.fromUTF8? (ByteArray.mk value.toUTF8.data.toList.toArray) = some value))

theorem fieldText_text {value : String} {text : PhysicalCodec.Text}
    (made : CoreFile.text? value = some text)
    (roundtrips : TextRoundtrips value) :
    fieldText? text.recordField = some value := by
  unfold CoreFile.text? at made
  dsimp only at made
  split at made
  next bound =>
    injection made with equal
    subst text
    exact roundtrips
  next tooLong => contradiction

theorem fieldNat_signedNat {value : Nat}
    {integer : SignedInteger .eight}
    (made : CoreFile.signedNat? value = some integer) :
    fieldNat? (.integer .eight integer) = some value := by
  unfold CoreFile.signedNat? at made
  split at made
  next upper =>
    injection made with equal
    subst integer
    simp [fieldNat?]
  next tooLarge => contradiction

theorem fieldOptionalText_text {value : String} (text : PhysicalCodec.Text)
    (decoded : fieldText? text.recordField = some value) :
    fieldOptionalText? text.recordField = some (some value) := by
  unfold fieldOptionalText? PhysicalCodec.Text.recordField
  change some <$> fieldText? text.recordField = some (some value)
  rw [decoded]
  rfl

structure CatalogEntry where
  kind : String
  name : String
  table : String
  rootPage : Nat
  sql : Option String
  deriving DecidableEq, Repr

def CatalogEntry.ofEncoded (entry : CoreFile.CatalogEntry) : CatalogEntry :=
  ⟨entry.kind, entry.name, entry.table, entry.rootPage,
    if entry.sqlIsNull then none else some entry.sql⟩

/-- Split the canonical catalog at its first non-table entry. The encoder emits
all tables first and then all indexes. -/
def splitCanonicalCatalog : List CatalogEntry →
    List CatalogEntry × List CatalogEntry
  | [] => ([], [])
  | entry :: entries =>
      if entry.kind = "table" then
        let split := splitCanonicalCatalog entries
        (entry :: split.1, split.2)
      else ([], entry :: entries)

theorem splitCanonicalCatalog_append (tables indexes : List CatalogEntry)
    (tableKinds : ∀ entry ∈ tables, entry.kind = "table")
    (indexKinds : ∀ entry ∈ indexes, entry.kind ≠ "table") :
    splitCanonicalCatalog (tables ++ indexes) = (tables, indexes) := by
  induction tables with
  | nil =>
      cases indexes with
      | nil => rfl
      | cons entry entries =>
        simp [splitCanonicalCatalog, indexKinds entry (by simp)]
  | cons entry entries induction =>
      simp [splitCanonicalCatalog, tableKinds entry (by simp),
        induction (fun candidate member =>
          tableKinds candidate (by simp [member]))]

theorem encodedCatalogKinds
    (tableEntries indexEntries : List CoreFile.CatalogEntry)
    (tables : ∀ entry ∈ tableEntries, entry.kind = "table")
    (indexes : ∀ entry ∈ indexEntries, entry.kind = "index") :
    splitCanonicalCatalog
      ((tableEntries ++ indexEntries).map CatalogEntry.ofEncoded) =
      (tableEntries.map CatalogEntry.ofEncoded,
        indexEntries.map CatalogEntry.ofEncoded) := by
  rw [List.map_append]
  apply splitCanonicalCatalog_append
  · intro entry member
    rcases List.mem_map.mp member with ⟨encoded, encodedMember, rfl⟩
    exact tables encoded encodedMember
  · intro entry member
    rcases List.mem_map.mp member with ⟨encoded, encodedMember, rfl⟩
    have kind := indexes encoded encodedMember
    simp [CatalogEntry.ofEncoded, kind]

def CatalogTextRoundtrips (entry : CoreFile.CatalogEntry) : Prop :=
  CoreDecode.TextRoundtrips entry.kind ∧
  CoreDecode.TextRoundtrips entry.name ∧
  CoreDecode.TextRoundtrips entry.table ∧
  CoreDecode.TextRoundtrips entry.sql

instance (entry : CoreFile.CatalogEntry) : Decidable (CatalogTextRoundtrips entry) := by
  unfold CatalogTextRoundtrips
  infer_instance

def decodeCatalogCellWithSuffix (input : List UInt8) :
    Option (CatalogEntry × List UInt8) := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (_, afterRowid) ← decodeVarint afterSize
  let (record, suffix) ← decodePhysicalRecord afterRowid
  if _sizeMatches : record.encode.length = payloadSize.val then
    match record.fields with
    | [kindField, nameField, tableField, rootField, sqlField] => do
        let kind ← fieldText? kindField
        let name ← fieldText? nameField
        let table ← fieldText? tableField
        let rootPage ← fieldNat? rootField
        let sql ← fieldOptionalText? sqlField
        some ({ kind, name, table, rootPage, sql }, suffix)
    | _ => none
  else none

def decodeCatalogCell (input : List UInt8) : Option CatalogEntry := do
  let (entry, _) ← decodeCatalogCellWithSuffix input
  some entry

theorem decodeCatalogCell_catalogCell {rowid : Nat}
    {entry : CoreFile.CatalogEntry} {cell : List UInt8}
    (built : CoreFile.catalogCell? rowid entry = some cell)
    (textRoundtrips : CatalogTextRoundtrips entry) (suffix : List UInt8) :
    decodeCatalogCellWithSuffix (cell ++ suffix) =
      some (CatalogEntry.ofEncoded entry, suffix) := by
  unfold CoreFile.catalogCell? at built
  cases rowidResult : CoreFile.signedNat? rowid with
  | none => simp [rowidResult] at built
  | some encodedRowid =>
    simp only [rowidResult, Option.bind_eq_bind, Option.bind] at built
    cases kindResult : CoreFile.text? entry.kind with
    | none => simp [kindResult] at built
    | some kind =>
      simp only [kindResult, Option.bind_eq_bind, Option.bind] at built
      cases nameResult : CoreFile.text? entry.name with
      | none => simp [nameResult] at built
      | some name =>
        simp only [nameResult, Option.bind_eq_bind, Option.bind] at built
        cases tableResult : CoreFile.text? entry.table with
          | none => simp [tableResult] at built
          | some table =>
            simp only [tableResult, Option.bind_eq_bind, Option.bind] at built
            cases rootResult : CoreFile.signedNat? entry.rootPage with
            | none => simp [rootResult] at built
            | some rootPage =>
              simp only [rootResult, Option.bind_eq_bind, Option.bind] at built
              by_cases nullSQL : entry.sqlIsNull = true
              · simp only [nullSQL, if_pos, Option.bind_eq_bind, Option.bind] at built
                let fields : List RecordField :=
                  [kind.recordField, name.recordField, table.recordField,
                    .integer .eight rootPage, .null]
                have recordCell : CoreFile.recordCell? encodedRowid fields = some cell := by
                  simpa [fields] using built
                unfold CoreFile.recordCell? at recordCell
                cases recordResult : CoreFile.physicalRecord? fields with
                | none => simp [recordResult] at recordCell
                | some record =>
                  simp only [recordResult, Option.bind_eq_bind, Option.bind] at recordCell
                  split at recordCell
                  next payloadBound =>
                    injection recordCell with cellEqual
                    subst cell
                    have recordFields : record.fields = fields := by
                      unfold CoreFile.physicalRecord? at recordResult
                      split at recordResult
                      next headerBound =>
                        exact congrArg PhysicalRecord.fields
                          (Option.some.inj recordResult.symm)
                      next headerTooLarge => contradiction
                    unfold decodeCatalogCellWithSuffix
                    simp only [List.append_assoc]
                    rw [decodeVarint_encode]
                    simp only [Option.bind_eq_bind, Option.bind]
                    rw [decodeVarint_encode]
                    simp only [Option.bind_eq_bind, Option.bind]
                    rw [decodePhysicalRecord_encode]
                    simp only [Option.bind_eq_bind, Option.bind, dif_pos True.intro]
                    rw [recordFields]
                    simp only [fields]
                    rw [fieldText_text kindResult textRoundtrips.1]
                    simp only [Option.bind_eq_bind, Option.bind]
                    rw [fieldText_text nameResult textRoundtrips.2.1]
                    simp only [Option.bind_eq_bind, Option.bind]
                    rw [fieldText_text tableResult textRoundtrips.2.2.1]
                    simp only [Option.bind_eq_bind, Option.bind]
                    rw [fieldNat_signedNat rootResult]
                    simp [fieldOptionalText?, CatalogEntry.ofEncoded, nullSQL]
                  next payloadTooLarge => contradiction
              · simp only [nullSQL, if_neg, Option.bind_eq_bind, Option.bind] at built
                cases sqlResult : CoreFile.text? entry.sql with
                | none => simp [sqlResult] at built
                | some sql =>
                  simp only [sqlResult, Option.bind_eq_bind, Option.bind] at built
                  let fields : List RecordField :=
                    [kind.recordField, name.recordField, table.recordField,
                      .integer .eight rootPage, sql.recordField]
                  have recordCell : CoreFile.recordCell? encodedRowid fields = some cell := by
                    simpa [fields] using built
                  unfold CoreFile.recordCell? at recordCell
                  cases recordResult : CoreFile.physicalRecord? fields with
                  | none => simp [recordResult] at recordCell
                  | some record =>
                    simp only [recordResult, Option.bind_eq_bind, Option.bind] at recordCell
                    split at recordCell
                    next payloadBound =>
                      injection recordCell with cellEqual
                      subst cell
                      have recordFields : record.fields = fields := by
                        unfold CoreFile.physicalRecord? at recordResult
                        split at recordResult
                        next headerBound =>
                          exact congrArg PhysicalRecord.fields
                            (Option.some.inj recordResult.symm)
                        next headerTooLarge => contradiction
                      unfold decodeCatalogCellWithSuffix
                      simp only [List.append_assoc]
                      rw [decodeVarint_encode]
                      simp only [Option.bind_eq_bind, Option.bind]
                      rw [decodeVarint_encode]
                      simp only [Option.bind_eq_bind, Option.bind]
                      rw [decodePhysicalRecord_encode]
                      simp only [Option.bind_eq_bind, Option.bind, dif_pos True.intro]
                      rw [recordFields]
                      simp only [fields]
                      rw [fieldText_text kindResult textRoundtrips.1]
                      simp only [Option.bind_eq_bind, Option.bind]
                      rw [fieldText_text nameResult textRoundtrips.2.1]
                      simp only [Option.bind_eq_bind, Option.bind]
                      rw [fieldText_text tableResult textRoundtrips.2.2.1]
                      simp only [Option.bind_eq_bind, Option.bind]
                      rw [fieldNat_signedNat rootResult]
                      simp only [Option.bind_eq_bind, Option.bind]
                      have sqlDecoded := fieldText_text sqlResult textRoundtrips.2.2.2
                      rw [fieldOptionalText_text sql sqlDecoded]
                      simp [CatalogEntry.ofEncoded, nullSQL]
                    next payloadTooLarge => contradiction

def decodeCatalogCells : Nat → List UInt8 →
    Option (List CatalogEntry × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (entry, afterEntry) ← decodeCatalogCellWithSuffix input
      let (entries, suffix) ← decodeCatalogCells count afterEntry
      some (entry :: entries, suffix)

theorem decodeCatalogCells_encode :
    ∀ (rowid : Nat) (entries : List CoreFile.CatalogEntry)
      (cells : List (List UInt8)),
      (∀ entry ∈ entries, CatalogTextRoundtrips entry) →
      CoreFile.catalogCellsFrom rowid entries = some cells →
      ∀ suffix, decodeCatalogCells entries.length
        (PhysicalCodec.cellBytes cells ++ suffix) =
          some (entries.map CatalogEntry.ofEncoded, suffix)
  | _, [], cells, _, encoded, suffix => by
      simp only [CoreFile.catalogCellsFrom] at encoded
      injection encoded with equal
      subst cells
      rfl
  | rowid, entry :: entries, cells, safe, encoded, suffix => by
      simp only [CoreFile.catalogCellsFrom, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : CoreFile.catalogCell? rowid entry with
      | none => simp [headResult] at encoded
      | some cell =>
          simp only [headResult] at encoded
          cases tailResult : CoreFile.catalogCellsFrom (rowid + 1) entries with
          | none => simp [tailResult] at encoded
          | some remaining =>
              simp only [tailResult] at encoded
              injection encoded with equal
              subst cells
              change decodeCatalogCells (entries.length + 1)
                (cell ++ PhysicalCodec.cellBytes remaining ++ suffix) =
                  some (CatalogEntry.ofEncoded entry ::
                    entries.map CatalogEntry.ofEncoded, suffix)
              rw [show cell ++ PhysicalCodec.cellBytes remaining ++ suffix =
                cell ++ (PhysicalCodec.cellBytes remaining ++ suffix) by
                  simp [List.append_assoc]]
              unfold decodeCatalogCells
              rw [decodeCatalogCell_catalogCell headResult
                (safe entry (by simp))]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [decodeCatalogCells_encode (rowid + 1) entries remaining
                (fun candidate member => safe candidate (by simp [member]))
                tailResult suffix]

def decodeCanonicalCatalog (firstPage : List UInt8) :
    Option (List CatalogEntry) := do
  let (cellCount, content) ← canonicalLeafContent? 100 firstPage
  let (entries, suffix) ← decodeCatalogCells cellCount content
  if _consumed : suffix = [] then some entries else none

theorem decodeCanonicalCatalog_leafPageBody
    (headerBytes : List UInt8) (entries : List CoreFile.CatalogEntry)
    (cells : List (List UInt8))
    (headerLength : headerBytes.length = 100)
    (fits : PhysicalCodec.PageFit 100 cells)
    (safe : ∀ entry ∈ entries, CatalogTextRoundtrips entry)
    (encoded : CoreFile.catalogCellsFrom 1 entries = some cells) :
    decodeCanonicalCatalog
      (headerBytes ++ PhysicalCodec.leafPageBody 100 cells) =
        some (entries.map CatalogEntry.ofEncoded) := by
  unfold decodeCanonicalCatalog
  rw [canonicalLeafContent_leafPageBody headerBytes 100 cells
    headerLength fits]
  simp only [Option.bind_eq_bind, Option.bind]
  have cellsLength := CoreFile.catalogCellsFrom_length encoded
  have decoded := decodeCatalogCells_encode 1 entries cells safe encoded []
  simp only [List.append_nil] at decoded
  rw [cellsLength, decoded]
  simp

end CoreDecode

end SQLeanite
