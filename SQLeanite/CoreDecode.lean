import SQLeanite.CoreFile
import SQLeanite.CoreSQL
import SQLeanite.CanonicalSchemaSQL
import SQLeanite.CanonicalIndexSQL
import SQLeanite.CoreOverflow
import Init.Data.Int.Compare

namespace SQLeanite
namespace CoreDecode

-- Retain elaboration of dependent page sizes; all terms remain kernel-checked.
set_option backward.isDefEq.respectTransparency false
-- Normalize the identity monad in executable cursor refinement proofs.
attribute [local simp] bind pure Functor.map

open FileFormat

def decodeOffsets : Nat → List UInt8 → Option (List Nat × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (offset, afterOffset) ← decodeUnsignedFixed 2 input
      let (offsets, suffix) ← decodeOffsets count afterOffset
      some (offset :: offsets, suffix)

theorem decodeOffsets_length {count : Nat} {input : List UInt8}
    {offsets : List Nat} {suffix : List UInt8}
    (decoded : decodeOffsets count input = some (offsets, suffix)) :
    offsets.length = count := by
  induction count generalizing input offsets suffix with
  | zero =>
      simp [decodeOffsets] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      rfl
  | succ count induction =>
      simp only [decodeOffsets, Option.bind_eq_bind, Option.bind] at decoded
      cases first : decodeUnsignedFixed 2 input with
      | none => simp [first] at decoded
      | some pair =>
          rcases pair with ⟨offset, afterOffset⟩
          simp only [first] at decoded
          cases rest : decodeOffsets count afterOffset with
          | none => simp [rest] at decoded
          | some pair =>
              rcases pair with ⟨remaining, finalSuffix⟩
              simp only [rest] at decoded
              have pairEq : (offset :: remaining, finalSuffix) = (offsets, suffix) :=
                Option.some.inj decoded
              have offsetsEq : offset :: remaining = offsets :=
                congrArg Prod.fst pairEq
              subst offsets
              simp [induction rest]

/-- Decode only the pointer array, intentionally discarding the suffix.  Table
interior traversal does not consume cell payloads sequentially; it follows
the decoded offsets back into the complete page.  Returning no dependent
suffix pair also keeps the traversal equation straightforward to rewrite. -/
def decodeOffsetList : Nat → List UInt8 → Option (List Nat)
  | 0, _ => some []
  | count + 1, input => do
      let (offset, afterOffset) ← decodeUnsignedFixed 2 input
      let offsets ← decodeOffsetList count afterOffset
      some (offset :: offsets)

/-- Read the contiguous content region of a canonical table-leaf page. This is
the proof-facing inverse of `PhysicalCodec.leafPageBody`; the tolerant decoder
below still follows cell pointers for C-written pages. -/
def canonicalLeafContent? (headerOffset : Nat) (page : List UInt8) :
    Option (Nat × List UInt8) := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    match page.drop headerOffset with
    | 13 :: 0 :: 0 :: afterFreeblock => do
        let (cellCount, afterCount) ← decodeUnsignedFixed 2 afterFreeblock
        let (contentStart, afterContentStart) ← decodeUnsignedFixed 2 afterCount
        match afterContentStart with
        | 0 :: _ => some (cellCount, page.drop contentStart)
        | _ => none
    | _ => none
  else none

theorem canonicalLeafContent_leafPageBody (headerBytes : List UInt8)
    (headerOffset : Nat) (cells : List (List UInt8))
    (headerLength : headerBytes.length = headerOffset)
    (fits : PhysicalCodec.PageFit headerOffset cells) :
    canonicalLeafContent? headerOffset
      (headerBytes ++ PhysicalCodec.leafPageBody headerOffset cells) =
        some (cells.length, PhysicalCodec.cellBytes cells) := by
  let contentStart := PhysicalCodec.pageSize - (PhysicalCodec.cellBytes cells).length
  let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
    List.replicate
      (contentStart - headerOffset -
        (PhysicalCodec.leafHeader cells.length contentStart ++
          PhysicalCodec.leafPointers contentStart cells).length) 0 ++
    PhysicalCodec.cellBytes cells
  have offsetLe : headerOffset ≤ PhysicalCodec.pageSize := by
    unfold PhysicalCodec.PageFit at fits
    omega
  have pageLength :
      (headerBytes ++ PhysicalCodec.leafPageBody headerOffset cells).length =
        PhysicalCodec.pageSize := by
    rw [List.length_append, headerLength,
      PhysicalCodec.leafPageBody_length headerOffset cells fits]
    omega
  have bodyLayout : PhysicalCodec.leafPageBody headerOffset cells =
      13 :: 0 :: 0 ::
        (PhysicalCodec.encodeU16Nat cells.length ++
          PhysicalCodec.encodeU16Nat contentStart ++ 0 :: afterHeader) := by
    unfold PhysicalCodec.leafPageBody PhysicalCodec.leafHeader
    simp only [List.cons_append, List.nil_append]
    rfl
  have countBound : cells.length < 256 ^ 2 := by
    simpa using fits.cellCount_lt
  have contentBound : contentStart < 256 ^ 2 := by
    exact PhysicalCodec.contentStart_lt cells
  have dropHeader :
      (headerBytes ++ PhysicalCodec.leafPageBody headerOffset cells).drop headerOffset =
        PhysicalCodec.leafPageBody headerOffset cells := by
    rw [← headerLength]
    simp
  have dropped :
      (headerBytes ++ PhysicalCodec.leafPageBody headerOffset cells).drop contentStart =
        PhysicalCodec.cellBytes cells :=
    PhysicalCodec.prefix_leafPageBody_drop_content headerBytes headerOffset cells
      headerLength fits
  rw [bodyLayout] at dropped
  unfold canonicalLeafContent?
  rw [dif_pos pageLength, dropHeader, bodyLayout]
  simp only
  unfold PhysicalCodec.encodeU16Nat
  unfold PhysicalCodec.encodeU16Nat at dropped
  simp only [List.append_assoc]
  rw [decodeUnsignedFixed_encode _ countBound]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeUnsignedFixed_encode _ contentBound]
  simp only [Option.bind_eq_bind, Option.bind]
  simp only [List.append_assoc] at dropped
  rw [dropped]

def decodeRowCells (schema : Core.Schema) : Nat → List UInt8 →
    Option (List Core.Row × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (row, afterRow) ← CoreRecord.decodeRowCell schema input
      let (rows, suffix) ← decodeRowCells schema count afterRow
      some (row :: rows, suffix)

theorem mapM_length_of_eq_some {α β : Type} (f : α → Option β) :
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
              simp [mapM_length_of_eq_some f input remaining tailResult]

theorem decodeRowCells_encode (schema : Core.Schema) :
    ∀ (rows : List Core.Row) (cells : List (List UInt8)),
      (∀ row ∈ rows, row.WellFormed schema) →
      rows.mapM (CoreRecord.encodeCell? schema) = some cells →
      ∀ suffix, decodeRowCells schema rows.length
        (PhysicalCodec.cellBytes cells ++ suffix) = some (rows, suffix)
  | [], cells, _, encoded, suffix => by
      simp only [List.mapM_nil, pure, Pure.pure] at encoded
      injection encoded with cellsEq
      subst cells
      rfl
  | row :: rows, cells, valid, encoded, suffix => by
      cases headResult : CoreRecord.encodeCell? schema row with
      | none => simp [List.mapM_cons, headResult] at encoded
      | some cell =>
          cases tailResult : rows.mapM (CoreRecord.encodeCell? schema) with
          | none => simp [List.mapM_cons, headResult, tailResult] at encoded
          | some remaining =>
              simp only [List.mapM_cons, headResult, tailResult,
                Option.bind_eq_bind, Option.bind] at encoded
              injection encoded with cellsEq
              subst cells
              change decodeRowCells schema (rows.length + 1)
                (cell ++ PhysicalCodec.cellBytes remaining ++ suffix) =
                  some (row :: rows, suffix)
              rw [show cell ++ PhysicalCodec.cellBytes remaining ++ suffix =
                cell ++ (PhysicalCodec.cellBytes remaining ++ suffix) by
                  simp [List.append_assoc]]
              unfold decodeRowCells
              rw [CoreRecord.decodeRowCell_encode (valid row (by simp)) headResult]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [decodeRowCells_encode schema rows remaining
                (fun candidate member => valid candidate (by simp [member]))
                tailResult suffix]

def decodeCanonicalRows (schema : Core.Schema) (headerOffset : Nat)
    (page : List UInt8) : Option (List Core.Row) := do
  let (cellCount, content) ← canonicalLeafContent? headerOffset page
  let (rows, suffix) ← decodeRowCells schema cellCount content
  if _consumed : suffix = [] then some rows else none

theorem decodeCanonicalRows_leafPageBody (schema : Core.Schema)
    (rows : List Core.Row) (cells : List (List UInt8))
    (headerBytes : List UInt8) (headerOffset : Nat)
    (headerLength : headerBytes.length = headerOffset)
    (fits : PhysicalCodec.PageFit headerOffset cells)
    (valid : ∀ row ∈ rows, row.WellFormed schema)
    (encoded : rows.mapM (CoreRecord.encodeCell? schema) = some cells) :
    decodeCanonicalRows schema headerOffset
      (headerBytes ++ PhysicalCodec.leafPageBody headerOffset cells) = some rows := by
  unfold decodeCanonicalRows
  rw [canonicalLeafContent_leafPageBody headerBytes headerOffset cells
    headerLength fits]
  simp only [Option.bind_eq_bind, Option.bind]
  have cellsLength := mapM_length_of_eq_some
    (CoreRecord.encodeCell? schema) rows cells encoded
  have decoded := decodeRowCells_encode schema rows cells valid encoded []
  simp only [List.append_nil] at decoded
  rw [cellsLength, decoded]
  simp

theorem decodeCanonicalRows_tableLeafPage {table : Core.Table}
    {cells : List (List UInt8)} {page : CoreFile.Page}
    (encoded : CoreFile.tableCells table = some cells)
    (built : CoreFile.tableLeafPage? cells = some page) :
    decodeCanonicalRows table.schema 0 page.bytes = some table.rows := by
  unfold CoreFile.tableLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 13 0 cells with
  | none => simp [bodyResult] at built
  | some body =>
      simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
      injection built with equal
      subst page
      rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
      change decodeCanonicalRows table.schema 0 body.bytes = some table.rows
      rw [bodyBytes]
      have encodedRows :
          table.rows.mapM (CoreRecord.encodeCell? table.schema) = some cells := by
        simpa [CoreFile.tableCells] using encoded
      exact decodeCanonicalRows_leafPageBody table.schema table.rows cells [] 0
        rfl fits table.rowsWellFormed.1 encodedRows

theorem canonicalLeafContent_tableLeafPage {cells : List (List UInt8)}
    {page : CoreFile.Page}
    (built : CoreFile.tableLeafPage? cells = some page) :
    canonicalLeafContent? 0 page.bytes =
      some (cells.length, PhysicalCodec.cellBytes cells) := by
  unfold CoreFile.tableLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 13 0 cells with
  | none => simp [bodyResult] at built
  | some body =>
      simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
      injection built with equal
      subst page
      rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
      change canonicalLeafContent? 0 body.bytes = _
      rw [bodyBytes]
      exact canonicalLeafContent_leafPageBody [] 0 cells rfl fits

def decodeCanonicalLeafContents : List (List UInt8) →
    Option (Nat × List UInt8)
  | [] => some (0, [])
  | pageBytes :: pages => do
      let (count, content) ← canonicalLeafContent? 0 pageBytes
      let (remainingCount, remainingContent) ← decodeCanonicalLeafContents pages
      some (count + remainingCount, content ++ remainingContent)

/-- Number of leaf children advertised by a canonical interior table root. -/
def canonicalInteriorLeafCount? (page : List UInt8) : Option Nat := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    match page with
    | 5 :: 0 :: 0 :: afterFreeblock => do
        let (cellCount, _) ← decodeUnsignedFixed 2 afterFreeblock
        some (cellCount + 1)
    | _ => none
  else none

theorem canonicalInteriorLeafCount_interiorPageBody (rightmost : U32Value)
    (cells : List (List UInt8))
    (fits : PhysicalTableBTree.InteriorPageFit cells) :
    canonicalInteriorLeafCount?
      (PhysicalTableBTree.interiorPageBody rightmost cells) =
        some (cells.length + 1) := by
  let contentStart := PhysicalCodec.pageSize - (PhysicalCodec.cellBytes cells).length
  let afterHeader := PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
    FileFormat.encodeU32Bytes rightmost ++
    PhysicalCodec.leafPointers contentStart cells ++
    List.replicate
      (contentStart -
        (PhysicalTableBTree.interiorHeader cells.length contentStart rightmost ++
          PhysicalCodec.leafPointers contentStart cells).length) 0 ++
    PhysicalCodec.cellBytes cells
  have pageLength := PhysicalTableBTree.interiorPageBody_length rightmost cells fits
  have bodyLayout : PhysicalTableBTree.interiorPageBody rightmost cells =
      5 :: 0 :: 0 :: (PhysicalCodec.encodeU16Nat cells.length ++ afterHeader) := by
    unfold PhysicalTableBTree.interiorPageBody PhysicalTableBTree.interiorHeader
    simp only [List.cons_append, List.nil_append]
    rfl
  have countBound : cells.length < 256 ^ 2 := by
    simpa using fits.cellCount_lt
  have pageLength' :
      (5 :: 0 :: 0 :: (PhysicalCodec.encodeU16Nat cells.length ++ afterHeader)).length =
        PhysicalCodec.pageSize := by
    rw [← bodyLayout]
    exact pageLength
  rw [bodyLayout]
  unfold canonicalInteriorLeafCount?
  rw [dif_pos pageLength']
  simp only
  unfold PhysicalCodec.encodeU16Nat
  rw [decodeUnsignedFixed_encode _ countBound]
  rfl

theorem canonicalInteriorLeafCount_tableInteriorPage
    (firstLeaf : Nat) (leaves : List (List (List UInt8)))
    {page : CoreFile.Page} (multiple : 2 ≤ leaves.length)
    (built : CoreFile.tableInteriorPage? firstLeaf leaves = some page) :
    canonicalInteriorLeafCount? page.bytes = some leaves.length := by
  unfold CoreFile.tableInteriorPage? at built
  dsimp only at built
  split at built
  next rightmostBound =>
    let rightmost : U32Value :=
      ⟨firstLeaf + leaves.length - 1, by simpa using rightmostBound⟩
    cases cellsResult : CoreFile.tableInteriorCells? firstLeaf leaves with
    | none => simp [cellsResult] at built
    | some cells =>
      simp only [cellsResult, Option.bind_eq_bind, Option.bind] at built
      split at built
      next fits =>
        injection built with equal
        subst page
        change canonicalInteriorLeafCount?
          (PhysicalTableBTree.interiorPageBody rightmost cells) = some leaves.length
        rw [canonicalInteriorLeafCount_interiorPageBody rightmost cells fits]
        unfold CoreFile.tableInteriorCells? at cellsResult
        have cellsLength := mapM_length_of_eq_some _
          leaves.dropLast.zipIdx cells cellsResult
        simp only [List.length_zipIdx, List.length_dropLast] at cellsLength
        rw [cellsLength]
        have positive : 1 ≤ leaves.length := Nat.le_trans (by decide) multiple
        rw [Nat.sub_add_cancel positive]
      next doesNotFit => contradiction
  next rightmostTooLarge => contradiction

theorem canonicalInteriorLeafCount_tableLeafPage {cells : List (List UInt8)}
    {page : CoreFile.Page}
    (built : CoreFile.tableLeafPage? cells = some page) :
    canonicalInteriorLeafCount? page.bytes = none := by
  unfold CoreFile.tableLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 13 0 cells with
  | none => simp [bodyResult] at built
  | some body =>
      simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
      injection built with equal
      subst page
      rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
      change canonicalInteriorLeafCount? body.bytes = none
      rw [bodyBytes]
      have bodyLength := PhysicalCodec.leafPageBody_length 0 cells fits
      unfold canonicalInteriorLeafCount?
      rw [dif_pos (by simpa using bodyLength)]
      unfold PhysicalCodec.leafPageBody PhysicalCodec.leafHeader
      rfl

theorem decodeCanonicalLeafContents_tablePages :
    ∀ (leaves : List (List (List UInt8))) (physicalPages : List CoreFile.Page),
      leaves.mapM CoreFile.tableLeafPage? = some physicalPages →
      decodeCanonicalLeafContents (physicalPages.map CoreFile.Page.bytes) =
        some (leaves.flatten.length,
          PhysicalCodec.cellBytes leaves.flatten)
  | [], physicalPages, built => by
      simp only [List.mapM_nil, pure, Pure.pure] at built
      injection built with equal
      subst physicalPages
      rfl
  | leaf :: leaves, physicalPages, built => by
      cases headResult : CoreFile.tableLeafPage? leaf with
      | none => simp [List.mapM_cons, headResult] at built
      | some page =>
          cases tailResult : leaves.mapM CoreFile.tableLeafPage? with
          | none => simp [List.mapM_cons, headResult, tailResult] at built
          | some remaining =>
              simp only [List.mapM_cons, headResult, tailResult,
                Option.bind_eq_bind, Option.bind] at built
              injection built with equal
              subst physicalPages
              simp only [List.map_cons]
              unfold decodeCanonicalLeafContents
              rw [canonicalLeafContent_tableLeafPage headResult]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [decodeCanonicalLeafContents_tablePages leaves remaining tailResult]
              simp [PhysicalCodec.cellBytes, List.append_assoc]

def decodeCanonicalRowsBytes (schema : Core.Schema)
    (physicalPages : List (List UInt8)) : Option (List Core.Row) := do
  let (cellCount, content) ← decodeCanonicalLeafContents physicalPages
  let (rows, suffix) ← decodeRowCells schema cellCount content
  if _consumed : suffix = [] then some rows else none

def decodeCanonicalRowsPages (schema : Core.Schema)
    (physicalPages : List CoreFile.Page) : Option (List Core.Row) :=
  decodeCanonicalRowsBytes schema (physicalPages.map CoreFile.Page.bytes)

def decodeCanonicalTableGroup (schema : Core.Schema) :
    List (List UInt8) → Option (List Core.Row)
  | [] => none
  | [leaf] => decodeCanonicalRowsBytes schema [leaf]
  | root :: firstLeaf :: remainingLeaves => do
      let leafCount ← canonicalInteriorLeafCount? root
      let leaves := firstLeaf :: remainingLeaves
      if _countMatches : leafCount = leaves.length then
        decodeCanonicalRowsBytes schema leaves
      else none

theorem decodeCanonicalRowsPages_tableLeaves (table : Core.Table)
    {cells : List (List UInt8)} {leaves : List (List (List UInt8))}
    {physicalPages : List CoreFile.Page}
    (encoded : CoreFile.tableCells table = some cells)
    (paged : CoreFile.tableLeaves table = some leaves)
    (built : leaves.mapM CoreFile.tableLeafPage? = some physicalPages) :
    decodeCanonicalRowsPages table.schema physicalPages = some table.rows := by
  unfold decodeCanonicalRowsPages decodeCanonicalRowsBytes
  rw [decodeCanonicalLeafContents_tablePages leaves physicalPages built]
  simp only [Option.bind_eq_bind, Option.bind]
  have flattened := CoreFile.tableLeaves_storedCells table encoded paged
  change leaves.flatten = cells at flattened
  rw [flattened]
  have encodedRows :
      table.rows.mapM (CoreRecord.encodeCell? table.schema) = some cells := by
    simpa [CoreFile.tableCells] using encoded
  have cellsLength := mapM_length_of_eq_some
    (CoreRecord.encodeCell? table.schema) table.rows cells encodedRows
  have decoded := decodeRowCells_encode table.schema table.rows cells
    table.rowsWellFormed.1 encodedRows []
  simp only [List.append_nil] at decoded
  rw [cellsLength, decoded]
  simp

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

private theorem decodedU16Nat (value : Nat) (bounded : value < 65536) :
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
falls through to the general parser as before. -/
def parseTableSchema (sql : String) : Option Core.Schema :=
  match CanonicalSchemaSQL.parse sql with
  | some schema => some schema
  | none => do
      let statements ← (parse sql).toOption
      match statements.toList with
      | [.createTable name columns constraints _] =>
          (CoreSQL.schema name columns constraints).toOption
      | _ => none

/-- The canonical path is taken for every schema this engine prints. -/
theorem parseTableSchema_tableSQL (schema : Core.Schema)
    (printable : CanonicalSchemaSQL.Printable schema) :
    parseTableSchema (CanonicalSchemaSQL.print schema) = some schema := by
  unfold parseTableSchema CanonicalSchemaSQL.print CanonicalSchemaSQL.parse
  rw [String.toList_ofList,
    CanonicalSchemaSQL.parseChars_tableChars schema printable]

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
            let table ← (Core.Table.rebuild schema [] rows).toOption
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
          if index.isImplicitPrimary schema then some index else none
    else none
  else none

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
    rw [indexEq, if_pos automatic']
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
      let rebuilt ← (Core.Table.rebuild table.schema indexes table.rows).toOption
      let (restored, suffix) ← restoreCanonicalIndexes tables remaining
      some (rebuilt :: restored, suffix)

def rebuildCanonicalDatabase (tables : List Core.Table)
    (indexEntries : List CatalogEntry) : Option Core.Database := do
  let (restored, suffix) ← restoreCanonicalIndexes tables indexEntries
  if _consumed : suffix = [] then
    (Core.Database.rebuild restored).toOption
  else none

/-- Every table returned by the canonical metadata rebuilder is an exact
canonicalization fixed point.  The proof follows the executable recursion and
uses the checked `Table.rebuild` result at each table. -/
theorem restoreCanonicalIndexes_fixed :
    ∀ (tables : List Core.Table) (entries restored : List CatalogEntry)
      (resultTables : List Core.Table),
      restoreCanonicalIndexes tables entries =
        some (resultTables, restored) →
      ∀ table ∈ resultTables, table.canonicalize = table
  | [], entries, restored, resultTables, success => by
      simp only [restoreCanonicalIndexes, Option.some.injEq] at success
      injection success with tablesEqual
      subst resultTables
      simp
  | input :: inputs, entries, restored, resultTables, success => by
      simp only [restoreCanonicalIndexes, Option.bind_eq_bind, Option.bind]
        at success
      cases metadataResult : decodeCanonicalIndexesForTable input.schema
          input.schema.name entries with
      | none => simp [metadataResult] at success
      | some metadata =>
          rcases metadata with ⟨indexes, remaining⟩
          simp only [metadataResult] at success
          cases rebuiltResult :
              (Core.Table.rebuild input.schema indexes input.rows).toOption with
          | none => simp [rebuiltResult] at success
          | some table =>
              simp only [rebuiltResult] at success
              cases tailResult : restoreCanonicalIndexes inputs remaining with
              | none => simp [tailResult] at success
              | some tail =>
                  rcases tail with ⟨tailTables, suffix⟩
                  simp only [tailResult, Option.some.injEq] at success
                  injection success with tablesEqual suffixEqual
                  subst resultTables
                  subst restored
                  intro candidate member
                  simp only [List.mem_cons] at member
                  cases member with
                  | inl equal =>
                      subst candidate
                      cases rebuild : Core.Table.rebuild input.schema indexes
                          input.rows with
                      | error message =>
                          rw [rebuild] at rebuiltResult
                          cases rebuiltResult
                      | ok value =>
                          rw [rebuild] at rebuiltResult
                          have valueEqual : value = table := by
                            simpa only [Except.toOption,
                              Option.some.injEq] using rebuiltResult
                          subst table
                          exact Core.Table.rebuild_canonicalize_fixed rebuild
                  | inr tailMember =>
                      exact restoreCanonicalIndexes_fixed inputs remaining
                        suffix tailTables tailResult candidate tailMember

private theorem map_canonicalize_eq_self (tables : List Core.Table)
    (fixed : ∀ table ∈ tables, table.canonicalize = table) :
    tables.map Core.Table.canonicalize = tables := by
  induction tables with
  | nil => rfl
  | cons table tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨fixed table (by simp), induction (fun candidate member =>
        fixed candidate (by simp [member]))⟩

/-- `rebuildCanonicalDatabase` deserves its name extensionally as well as
logically: every successful result is already a fixed point of the public
canonicalization operation. -/
theorem rebuildCanonicalDatabase_fixed
    {tables : List Core.Table} {entries : List CatalogEntry}
    {database : Core.Database}
    (success : rebuildCanonicalDatabase tables entries = some database) :
    database.canonicalize = database := by
  unfold rebuildCanonicalDatabase at success
  cases restoredResult : restoreCanonicalIndexes tables entries with
  | none => simp [restoredResult] at success
  | some restored =>
      rcases restored with ⟨resultTables, suffix⟩
      simp only [restoredResult, Option.bind_eq_bind, Option.bind] at success
      split at success
      next consumed =>
        cases rebuilt : Core.Database.rebuild resultTables with
        | error message =>
          rw [rebuilt] at success
          cases success
        | ok value =>
          rw [rebuilt] at success
          have equal : value = database := by
            simpa only [Except.toOption, Option.some.injEq] using success
          subst database
          have tablesEqual : value.tables = resultTables :=
            Core.Database.rebuild_tables rebuilt
          cases value with
          | mk valueTables valueWellFormed =>
              simp only [Core.Database.canonicalize]
              congr 1
              have fixed : ∀ table ∈ valueTables,
                  table.canonicalize = table := by
                intro table member
                exact restoreCanonicalIndexes_fixed tables entries suffix
                  resultTables restoredResult table (by
                    rw [← tablesEqual]
                    exact member)
              exact map_canonicalize_eq_self valueTables fixed
      next => contradiction

theorem decodeCanonicalIndexesForTable_encodeIndexes (table : Core.Table) :
    ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List CoreFile.IndexEncoding) (suffix : List CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      CoreFile.encodeIndexes nextPage (indexes.map fun index => (table, index)) =
        some encodings →
      decodeCanonicalIndexesForTable table.schema table.schema.name
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (indexes, suffix)
  | _, [], encodings, suffix, _, boundary, encoded => by
      simp only [List.map_nil, CoreFile.encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold decodeCanonicalIndexesForTable
          exact dif_neg (boundary entry (by simp))
  | nextPage, index :: indexes, encodings, suffix, members, boundary, encoded => by
      simp only [List.map_cons, CoreFile.encodeIndexes,
        Option.bind_eq_bind, Option.bind] at encoded
      cases leavesResult : CoreFile.indexLeaves table index with
      | none => simp [leavesResult] at encoded
      | some leaves =>
        simp only [leavesResult] at encoded
        let layout : CoreFile.IndexLayout := ⟨nextPage, leaves⟩
        cases pagesResult : CoreFile.indexPages? layout.rootPage layout.leaves with
        | none => simp [layout, pagesResult] at encoded
        | some physicalPages =>
          simp only [layout, pagesResult] at encoded
          cases remainingResult : CoreFile.encodeIndexes
              (nextPage + CoreFile.tableFootprint leaves)
              (indexes.map fun candidate => (table, candidate)) with
          | none => simp [remainingResult] at encoded
          | some remaining =>
            simp only [remainingResult] at encoded
            injection encoded with equal
            subst encodings
            simp only [List.map_cons, List.cons_append]
            unfold decodeCanonicalIndexesForTable
            have sameTable :
                (CatalogEntry.ofEncoded
                  (CoreFile.IndexEncoding.catalogEntry
                    (⟨table, index, layout, physicalPages⟩ :
                      CoreFile.IndexEncoding))).table =
                  table.schema.name := rfl
            rw [dif_pos sameTable]
            have decoded :
                decodeCanonicalIndex table.schema table.schema.name
                  (CatalogEntry.ofEncoded
                    (CoreFile.IndexEncoding.catalogEntry
                      (⟨table, index, layout, physicalPages⟩ :
                        CoreFile.IndexEncoding))) = some index := by
              change decodeCanonicalIndex table.schema table.schema.name
                (CatalogEntry.ofEncoded ({
                  kind := "index"
                  name := index.name
                  table := table.schema.name
                  rootPage := layout.rootPage
                  sql := CoreFile.indexSQL table index
                  sqlIsNull := index.isImplicitPrimary table.schema
                } : CoreFile.CatalogEntry)) = some index
              exact decodeCanonicalIndex_encoded table index
                (members index (by simp)) layout.rootPage
            rw [decoded]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [decodeCanonicalIndexesForTable_encodeIndexes table
              (nextPage + CoreFile.tableFootprint leaves) indexes remaining suffix
              (fun candidate member => members candidate (by simp [member]))
              boundary remainingResult]

theorem restoreCanonicalIndexes_encodeIndexTableGroups :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreFile.IndexEncoding) (suffix : List CatalogEntry),
      Core.TablesWellFormed tables →
      (∀ entry ∈ suffix, ∀ table ∈ tables,
        entry.table ≠ table.schema.name) →
      CoreFile.encodeIndexTableGroups nextPage tables = some encodings →
      restoreCanonicalIndexes (tables.map Core.Table.withoutIndexes)
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (tables.map Core.Table.canonicalize, suffix)
  | _, [], encodings, suffix, _, _, encoded => by
      simp only [CoreFile.encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, suffix, wellFormed, boundary,
      encoded => by
      simp only [Core.TablesWellFormed, Core.namesUnique, List.map_cons,
        List.pairwise_cons] at wellFormed
      rcases wellFormed with ⟨headDistinct, tailWellFormed⟩
      simp only [CoreFile.encodeIndexTableGroups,
        Option.bind_eq_bind, Option.bind] at encoded
      cases currentResult : CoreFile.encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : CoreFile.encodeIndexTableGroups
            (CoreFile.indexEndPage nextPage current) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult] at encoded
          injection encoded with equal
          subst encodings
          simp only [List.map_cons, List.map_append, List.append_assoc]
          unfold restoreCanonicalIndexes
          have remainingBelongs := CoreFile.encodeIndexTableGroups_tables
            (CoreFile.indexEndPage nextPage current) tables remaining
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
              simpa [CoreFile.IndexEncoding.catalogEntry,
                CatalogEntry.ofEncoded] using distinct.symm
            · exact boundary entry suffixMember table (by simp)
          simp only [Core.Table.withoutIndexes_schema,
            Core.Table.withoutIndexes_rows]
          rw [decodeCanonicalIndexesForTable_encodeIndexes table nextPage
            table.indexes current
            (remaining.map (fun encoding =>
              CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix)
            (by simp) currentBoundary currentResult]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [Core.Table.rebuild_self]
          simp only [Except.toOption]
          have tailBoundary : ∀ entry ∈ suffix, ∀ candidate ∈ tables,
              entry.table ≠ candidate.schema.name := by
            intro entry entryMember candidate candidateMember
            exact boundary entry entryMember candidate (by simp [candidateMember])
          rw [restoreCanonicalIndexes_encodeIndexTableGroups
            (CoreFile.indexEndPage nextPage current) tables remaining suffix
            tailWellFormed tailBoundary remainingResult]

theorem rebuildCanonicalDatabase_encoded (database : Core.Database)
    (nextPage : Nat) (encodings : List CoreFile.IndexEncoding)
    (encoded : CoreFile.encodeIndexTableGroups nextPage database.tables =
      some encodings) :
    rebuildCanonicalDatabase
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CatalogEntry.ofEncoded encoding.catalogEntry)) =
          some database.canonicalize := by
  unfold rebuildCanonicalDatabase
  have restored := restoreCanonicalIndexes_encodeIndexTableGroups nextPage
    database.tables encodings [] database.tablesWellFormed (by simp) encoded
  simp only [List.append_nil] at restored
  rw [restored]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]
  have rebuilt := Core.Database.rebuild_self database.canonicalize
  change Core.Database.rebuild
      (database.tables.map Core.Table.canonicalize) =
        .ok database.canonicalize at rebuilt
  rw [rebuilt]
  simp only [Except.toOption]

theorem decodeCanonicalIndexesForTable_encodeOverflowIndexes
    (table : Core.Table) :
    ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List CoreOverflow.IndexEncoding)
      (suffix : List CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      CoreOverflow.encodeIndexes nextPage
          (indexes.map fun index => (table, index)) = some encodings →
      decodeCanonicalIndexesForTable table.schema table.schema.name
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (indexes, suffix)
  | _, [], encodings, suffix, _, boundary, encoded => by
      simp only [List.map_nil, CoreOverflow.encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold decodeCanonicalIndexesForTable
          exact dif_neg (boundary entry (by simp))
  | nextPage, index :: indexes, encodings, suffix, members, boundary,
      encoded => by
      simp only [List.map_cons, CoreOverflow.encodeIndexes,
        Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : CoreOverflow.encodeIndex nextPage table index with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : CoreOverflow.encodeIndexes
            (nextPage + head.pages.length)
            (indexes.map fun candidate => (table, candidate)) with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          simp only [List.map_cons, List.cons_append]
          unfold decodeCanonicalIndexesForTable
          have identity := CoreOverflow.encodeIndex_identity headResult
          have sameTable :
              (CatalogEntry.ofEncoded head.catalogEntry).table =
                table.schema.name := by
            simp [CoreOverflow.IndexEncoding.catalogEntry,
              CatalogEntry.ofEncoded, identity.1]
          rw [dif_pos sameTable]
          have decoded : decodeCanonicalIndex table.schema table.schema.name
              (CatalogEntry.ofEncoded head.catalogEntry) = some index := by
            rw [show head = {
              table := table
              index := index
              rootPage := nextPage
              topology := head.topology
              treePages := head.treePages
              overflowPages := head.overflowPages
            } from by cases head; simp_all]
            change decodeCanonicalIndex table.schema table.schema.name
              (CatalogEntry.ofEncoded ({
                kind := "index"
                name := index.name
                table := table.schema.name
                rootPage := nextPage
                sql := CoreFile.indexSQL table index
                sqlIsNull := index.isImplicitPrimary table.schema
              } : CoreFile.CatalogEntry)) = some index
            exact decodeCanonicalIndex_encoded table index
              (members index (by simp)) nextPage
          rw [decoded]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [decodeCanonicalIndexesForTable_encodeOverflowIndexes table
            (nextPage + head.pages.length) indexes tail suffix
            (fun candidate member => members candidate (by simp [member]))
            boundary tailResult]

theorem restoreCanonicalIndexes_encodeOverflowIndexTableGroups :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreOverflow.IndexEncoding)
      (suffix : List CatalogEntry),
      Core.TablesWellFormed tables →
      (∀ entry ∈ suffix, ∀ table ∈ tables,
        entry.table ≠ table.schema.name) →
      CoreOverflow.encodeIndexTableGroups nextPage tables = some encodings →
      restoreCanonicalIndexes (tables.map Core.Table.withoutIndexes)
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some (tables.map Core.Table.canonicalize, suffix)
  | _, [], encodings, suffix, _, _, encoded => by
      simp only [CoreOverflow.encodeIndexTableGroups] at encoded
      injection encoded with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, suffix, wellFormed, boundary,
      encoded => by
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
          unfold restoreCanonicalIndexes
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
          simp only [Core.Table.withoutIndexes_schema,
            Core.Table.withoutIndexes_rows]
          rw [decodeCanonicalIndexesForTable_encodeOverflowIndexes table
            nextPage table.indexes current
            (remaining.map (fun encoding =>
              CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix)
            (by simp) currentBoundary currentResult]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [Core.Table.rebuild_self]
          simp only [Except.toOption]
          have tailBoundary : ∀ entry ∈ suffix, ∀ candidate ∈ tables,
              entry.table ≠ candidate.schema.name := by
            intro entry entryMember candidate candidateMember
            exact boundary entry entryMember candidate (by simp [candidateMember])
          rw [restoreCanonicalIndexes_encodeOverflowIndexTableGroups
            (nextPage + (CoreOverflow.indexPagesOf current).length) tables
            remaining suffix tailWellFormed tailBoundary remainingResult]

theorem rebuildCanonicalDatabase_overflowEncoded (database : Core.Database)
    (nextPage : Nat) (encodings : List CoreOverflow.IndexEncoding)
    (encoded : CoreOverflow.encodeIndexTableGroups nextPage database.tables =
      some encodings) :
    rebuildCanonicalDatabase
      (database.tables.map Core.Table.withoutIndexes)
      (encodings.map (fun encoding =>
        CatalogEntry.ofEncoded encoding.catalogEntry)) =
          some database.canonicalize := by
  unfold rebuildCanonicalDatabase
  have restored := restoreCanonicalIndexes_encodeOverflowIndexTableGroups
    nextPage database.tables encodings [] database.tablesWellFormed (by simp)
    encoded
  simp only [List.append_nil] at restored
  rw [restored]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]
  have rebuilt := Core.Database.rebuild_self database.canonicalize
  change Core.Database.rebuild
      (database.tables.map Core.Table.canonicalize) =
        .ok database.canonicalize at rebuilt
  rw [rebuilt]
  simp only [Except.toOption]

theorem decodeCanonicalTableStep_encoded (table : Core.Table)
    (layout : CoreFile.TableLayout) {cells : List (List UInt8)}
    {physicalPages : List CoreFile.Page}
    (encoded : CoreFile.tableCells table = some cells)
    (paged : CoreFile.tableLeaves table = some layout.leaves)
    (built : CoreFile.tablePages? layout = some physicalPages)
    (suffix : List (List UInt8)) :
    let entry : CoreFile.CatalogEntry := {
      kind := "table"
      name := table.schema.name
      table := table.schema.name
      rootPage := layout.rootPage
      sql := CoreFile.tableSQL table.schema }
    decodeCanonicalTableStep layout.rootPage (CatalogEntry.ofEncoded entry)
      (physicalPages.map CoreFile.Page.bytes ++ suffix) =
        some (table.withoutIndexes, physicalPages.length, suffix) := by
  dsimp only
  unfold decodeCanonicalTableStep CatalogEntry.ofEncoded CoreFile.tableSQL
  simp only [Bool.false_eq_true, if_false]
  simp only [dif_pos True.intro]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseTableSchema_tableSQL table.schema
    (CanonicalSchemaSQL.Printable.ofWellFormed table.schema table.schemaWellFormed)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]
  have groupDecoded := decodeCanonicalTableGroup_tablePages table layout encoded paged built
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
          simp only [List.map_cons, List.map_nil, List.nil_append,
            List.cons_append]
          rw [canonicalInteriorLeafCount_tableLeafPage pageResult]
          simp only [Option.bind_eq_bind, Option.bind]
          simp only [List.map_cons, List.map_nil] at groupDecoded
          rw [groupDecoded]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [Core.Table.rebuild_withoutIndexes]
          rfl
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
          have pageCount := mapM_length_of_eq_some CoreFile.tableLeafPage?
            layout.leaves leafPages leafPagesResult
          let leafBytes := leafPages.map CoreFile.Page.bytes
          have byteCount : leafBytes.length = layout.leaves.length := by
            simp [leafBytes, pageCount]
          simp only [List.map_cons, List.cons_append]
          rw [leafCount]
          simp only [Option.bind_eq_bind, Option.bind]
          have takeLeaves : (leafBytes ++ suffix).take layout.leaves.length = leafBytes := by
            rw [← byteCount]
            simp
          have dropLeaves : (leafBytes ++ suffix).drop layout.leaves.length = suffix := by
            rw [← byteCount]
            simp
          rw [takeLeaves, dif_pos byteCount, dropLeaves]
          simp only [List.map_cons] at groupDecoded
          change decodeCanonicalTableGroup table.schema
            (root.bytes :: leafBytes) = some table.rows at groupDecoded
          rw [groupDecoded]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [Core.Table.rebuild_withoutIndexes]
          simp [leafBytes]
          rfl

theorem decodeCanonicalTables_encodeTables :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreFile.TableEncoding)
      (indexSuffix : List (List UInt8)),
      CoreFile.encodeTables nextPage tables = some encodings →
      decodeCanonicalTables nextPage
        ((CoreFile.tableEntriesFor tables
          (CoreFile.tableLayoutsOf encodings)).map CatalogEntry.ofEncoded)
        ((CoreFile.tablePagesOf encodings).map CoreFile.Page.bytes ++ indexSuffix) =
          some (tables.map Core.Table.withoutIndexes, indexSuffix)
  | _, [], encodings, indexSuffix, encodedTables => by
      simp only [CoreFile.encodeTables] at encodedTables
      injection encodedTables with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, indexSuffix, encodedTables => by
      simp only [CoreFile.encodeTables, Option.bind_eq_bind, Option.bind] at encodedTables
      cases leavesResult : CoreFile.tableLeaves table with
      | none => simp [leavesResult] at encodedTables
      | some leaves =>
        simp only [leavesResult] at encodedTables
        let layout : CoreFile.TableLayout := ⟨nextPage, leaves⟩
        cases pagesResult : CoreFile.tablePages? layout with
        | none => simp [layout, pagesResult] at encodedTables
        | some physicalPages =>
          simp only [layout, pagesResult] at encodedTables
          cases remainingResult : CoreFile.encodeTables
              (nextPage + CoreFile.tableFootprint leaves) tables with
          | none => simp [remainingResult] at encodedTables
          | some remaining =>
            simp only [remainingResult] at encodedTables
            injection encodedTables with equal
            subst encodings
            cases cellsResult : CoreFile.tableCells table with
            | none =>
              unfold CoreFile.tableLeaves at leavesResult
              simp [cellsResult] at leavesResult
            | some cells =>
              have step := decodeCanonicalTableStep_encoded table layout cellsResult
                (by simpa [layout] using leavesResult) pagesResult
                ((CoreFile.tablePagesOf remaining).map CoreFile.Page.bytes ++ indexSuffix)
              have pageLength := CoreFile.tablePages_length_of_success pagesResult
              have rest := decodeCanonicalTables_encodeTables
                (nextPage + CoreFile.tableFootprint leaves) tables remaining
                indexSuffix remainingResult
              simp only [CoreFile.tableLayoutsOf, CoreFile.tablePagesOf,
                CoreFile.tableEntriesFor, List.map_cons, List.flatMap_cons,
                List.map_append]
              simp only [List.append_assoc]
              dsimp only at step
              unfold CoreFile.tablePagesOf at step rest
              unfold CoreFile.tableLayoutsOf at rest
              dsimp [layout] at step pageLength
              unfold decodeCanonicalTables
              rw [step]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [pageLength, rest]

def page? (pages : List (List UInt8)) (pageNumber : Nat) : Option (List UInt8) :=
  if _positive : 0 < pageNumber then pages[pageNumber - 1]? else none

/-- Read-only pager boundary used by recursive table and index traversal. A
decoder asks only for pages reachable from a root; the backing store decides
whether those pages are already resident, cached, or read on demand. -/
structure PageSource where
  pageCount : Nat
  readPage : Nat → Option (List UInt8)

def PageSource.ofList (physicalPages : List (List UInt8)) : PageSource := {
  pageCount := physicalPages.length
  readPage := page? physicalPages }

/-- Effectful counterpart of `PageSource`.  The parser and tree algorithms
remain pure Lean; only page acquisition is effectful, permitting a file-backed
pager to fetch a reachable page on demand. -/
structure IOPageSource where
  usable : UsablePageSize := PhysicalCodec.usablePageSize
  pageCount : Nat
  readPage : Nat → IO (Option (List UInt8))

private def sequenceOptions : List (Option α) → Option (List α)
  | [] => some []
  | some value :: rest => (sequenceOptions rest).map (value :: ·)
  | none :: _ => none

/-- Validate one decoded overflow page and either finish or invoke the
continuation on its successor. -/
def finishOverflowStep (recurse : Nat → Nat → Option (List UInt8))
    (remaining : Nat) (overflow : OverflowPage PhysicalCodec.usablePageSize)
    (suffix : List UInt8) : Option (List UInt8) :=
  if _consumed : suffix = [] then
    let amount := min remaining CoreOverflow.overflowCapacity
    let chunk := overflow.payload.bytes.take amount
    if _final : remaining ≤ CoreOverflow.overflowCapacity then
      match overflow.next with
      | .endOfChain => some chunk
      | .page _ => none
    else
      match overflow.next with
      | .endOfChain => none
      | .page next => do
          let rest ← recurse
            (remaining - CoreOverflow.overflowCapacity) next.value.val
          some (chunk ++ rest)
  else none

/-- Consume one nonempty logical segment of an overflow chain.  Factoring this
transition out of the fuel recursion keeps both the executable state machine
and its inverse theorem compositional. -/
def readOverflowStep (source : PageSource)
    (recurse : Nat → Nat → Option (List UInt8))
    (remaining pageNumber : Nat) : Option (List UInt8) := do
  let page ← source.readPage pageNumber
  let (overflow, suffix) ←
    decodeOverflowPage PhysicalCodec.usablePageSize page
  finishOverflowStep recurse remaining overflow suffix

/-- Resolve exactly the requested logical bytes from a SQLite overflow chain.
The page-count fuel rejects cycles and overlong malformed chains. -/
def readOverflowFrom (source : PageSource) :
    Nat → Nat → Nat → Option (List UInt8)
  | _, 0, _ => some []
  | 0, _ + 1, _ => none
  | fuel + 1, remaining, pageNumber =>
      readOverflowStep source (readOverflowFrom source fuel) remaining pageNumber

/-- The pages generated for one overflow payload are present at the page
numbers encoded in their next pointers.  This relation is intentionally about
page reads, not list positions, so the same inverse theorem applies to an
in-memory image and to a pager. -/
def ReadsGeneratedOverflow (source : PageSource) (start count : Nat)
    (bytes : List UInt8) : Prop :=
  ∀ offset, offset < count →
    source.readPage (start + offset) = some
      (CoreOverflow.overflowPageBytes start count offset bytes)

def ReadsPagesFrom (source : PageSource) (start : Nat)
    (pages : List CoreFile.Page) : Prop :=
  ∀ (offset : Nat) (inBounds : offset < pages.length),
    source.readPage (start + offset) = some pages[offset].bytes

theorem ReadsPagesFrom.left {source : PageSource} {start : Nat}
    {left right : List CoreFile.Page}
    (reads : ReadsPagesFrom source start (left ++ right)) :
    ReadsPagesFrom source start left := by
  intro offset inBounds
  have available := reads offset (by simp; omega)
  rw [List.getElem_append_left inBounds] at available
  exact available

theorem ReadsPagesFrom.right {source : PageSource} {start : Nat}
    {left right : List CoreFile.Page}
    (reads : ReadsPagesFrom source start (left ++ right)) :
    ReadsPagesFrom source (start + left.length) right := by
  intro offset inBounds
  have available := reads (left.length + offset) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at available
  have indexEq : left.length + offset - left.length = offset := by omega
  simpa only [indexEq, Nat.add_assoc] using available

theorem ReadsPagesFrom.ofList_append (leading : List (List UInt8))
    (pages : List CoreFile.Page) (suffix : List (List UInt8)) :
    ReadsPagesFrom
      (.ofList (leading ++ pages.map CoreFile.Page.bytes ++ suffix))
      (leading.length + 1) pages := by
  intro offset inBounds
  unfold PageSource.ofList page?
  dsimp only
  rw [dif_pos (by omega)]
  have indexEqual : leading.length + 1 + offset - 1 =
      leading.length + offset := by omega
  rw [indexEqual]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by omega)]
  have offsetEqual : leading.length + offset - leading.length = offset := by omega
  rw [offsetEqual, List.getElem?_map,
    List.getElem?_eq_getElem inBounds]
  rfl

theorem ReadsPagesFrom.ofList_tail (pages : List CoreFile.Page) :
    ReadsPagesFrom (.ofList (pages.map CoreFile.Page.bytes)) 2 pages.tail := by
  cases pages with
  | nil => simp [ReadsPagesFrom]
  | cons first rest =>
      simpa using ReadsPagesFrom.ofList_append [first.bytes] rest []

theorem ReadsPagesFrom.encodeOverflowIndexes (source : PageSource) :
    ∀ (nextPage : Nat) (indexes : List (Core.Table × Core.Index))
      (encodings : List CoreOverflow.IndexEncoding),
      CoreOverflow.encodeIndexes nextPage indexes = some encodings →
      ReadsPagesFrom source nextPage
        (CoreOverflow.indexPagesOf encodings) →
      ∀ encoding ∈ encodings,
        ReadsPagesFrom source encoding.rootPage encoding.pages
  | _, [], encodings, encoded, _ => by
      simp only [CoreOverflow.encodeIndexes, Option.some.injEq] at encoded
      subst encodings
      simp
  | nextPage, indexed :: indexes, encodings, encoded, reads => by
      simp only [CoreOverflow.encodeIndexes, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : CoreOverflow.encodeIndex nextPage indexed.1 indexed.2 with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : CoreOverflow.encodeIndexes
            (nextPage + head.pages.length) indexes with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          have normalized : ReadsPagesFrom source nextPage
              (head.pages ++ CoreOverflow.indexPagesOf tail) := by
            simpa [CoreOverflow.indexPagesOf] using reads
          have headReads : ReadsPagesFrom source nextPage head.pages :=
            ReadsPagesFrom.left normalized
          have tailReads : ReadsPagesFrom source
              (nextPage + head.pages.length)
              (CoreOverflow.indexPagesOf tail) :=
            ReadsPagesFrom.right normalized
          have identity := CoreOverflow.encodeIndex_identity headResult
          intro encoding member
          simp only [List.mem_cons] at member
          rcases member with rfl | tailMember
          · simpa [identity.2.2] using headReads
          · exact ReadsPagesFrom.encodeOverflowIndexes source
              (nextPage + head.pages.length) indexes tail tailResult tailReads
              encoding tailMember

theorem ReadsPagesFrom.encodeOverflowIndexTableGroups (source : PageSource) :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreOverflow.IndexEncoding),
      CoreOverflow.encodeIndexTableGroups nextPage tables = some encodings →
      ReadsPagesFrom source nextPage
        (CoreOverflow.indexPagesOf encodings) →
      ∀ encoding ∈ encodings,
        ReadsPagesFrom source encoding.rootPage encoding.pages
  | _, [], encodings, encoded, _ => by
      simp only [CoreOverflow.encodeIndexTableGroups, Option.some.injEq]
        at encoded
      subst encodings
      simp
  | nextPage, table :: tables, encodings, encoded, reads => by
      simp only [CoreOverflow.encodeIndexTableGroups, Option.bind_eq_bind,
        Option.bind] at encoded
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
          have normalized : ReadsPagesFrom source nextPage
              (CoreOverflow.indexPagesOf current ++
                CoreOverflow.indexPagesOf remaining) := by
            simpa [CoreOverflow.indexPagesOf] using reads
          have currentReads : ReadsPagesFrom source nextPage
              (CoreOverflow.indexPagesOf current) :=
            ReadsPagesFrom.left normalized
          have remainingReads : ReadsPagesFrom source
              (nextPage + (CoreOverflow.indexPagesOf current).length)
              (CoreOverflow.indexPagesOf remaining) :=
            ReadsPagesFrom.right normalized
          intro encoding member
          simp only [List.mem_append] at member
          rcases member with currentMember | remainingMember
          · exact ReadsPagesFrom.encodeOverflowIndexes source nextPage _ current
              currentResult currentReads encoding currentMember
          · exact ReadsPagesFrom.encodeOverflowIndexTableGroups source
              (nextPage + (CoreOverflow.indexPagesOf current).length) tables
              remaining remainingResult remainingReads encoding remainingMember

theorem readsGeneratedOverflow_of_makeOverflowPages
    (source : PageSource) (start : Nat) (bytes : List UInt8)
    (pages : List CoreFile.Page)
    (built : CoreOverflow.makeOverflowPages? start bytes = some pages)
    (reads : ReadsPagesFrom source start pages) :
    ReadsGeneratedOverflow source start
      (CoreOverflow.overflowPageCount bytes) bytes := by
  rw [CoreOverflow.makeOverflowPages?_eq] at built
  injection built with pagesEqual
  subst pages
  intro offset inBounds
  have available := reads offset (by simpa using inBounds)
  simpa [CoreOverflow.overflowPage] using available

set_option maxRecDepth 8192 in
private theorem readOverflowFrom_generated_final (source : PageSource)
    (start : Nat) (bytes : List UInt8) (nonempty : bytes ≠ [])
    (fits : bytes.length ≤ CoreOverflow.overflowCapacity)
    (bounded : start + 1 < 2 ^ 32)
    (firstRead : source.readPage start = some
      (CoreOverflow.overflowPageBytes start 1 0 bytes)) :
    readOverflowFrom source 2 bytes.length start = some bytes := by
  have lengthPositive : 0 < bytes.length := List.length_pos_iff.mpr nonempty
  obtain ⟨remaining, lengthEqual⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt lengthPositive)
  rw [lengthEqual]
  rw [readOverflowFrom] <;> try omega
  unfold readOverflowStep
  rw [firstRead]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [CoreOverflow.decodeOverflowPage_overflowPageBytes start 1 0 bytes bounded]
  simp only [Option.bind_eq_bind, Option.bind_some]
  unfold finishOverflowStep
  have finalNext := CoreOverflow.generatedOverflowPage_next_final start bytes
    bounded
  have payloadTake := CoreOverflow.generatedOverflowPage_payload_take_final
    start bytes fits bounded
  rw [← lengthEqual, dif_pos rfl, dif_pos fits, finalNext,
    Nat.min_eq_left fits, payloadTake]

private theorem finishOverflowStep_generated_step (count : Nat)
    (recurse : Nat → Nat → Option (List UInt8))
    (start : Nat) (bytes : List UInt8) (countPositive : 0 < count)
    (tooLarge : CoreOverflow.overflowCapacity < bytes.length)
    (bounded : start + (count + 1) < 2 ^ 32)
    (tailDecoded : recurse
      (bytes.drop CoreOverflow.overflowCapacity).length (start + 1) =
        some (bytes.drop CoreOverflow.overflowCapacity)) :
    finishOverflowStep recurse bytes.length
      (CoreOverflow.generatedOverflowPage start (count + 1) 0 bytes bounded) [] =
        some bytes := by
  unfold finishOverflowStep
  obtain ⟨next, nextEqual, nextValue⟩ :=
    CoreOverflow.generatedOverflowPage_next_step start count bytes
      countPositive bounded
  have payloadTake := CoreOverflow.generatedOverflowPage_payload_take_step
    start count bytes tooLarge bounded
  rw [dif_pos rfl, dif_neg (by omega), nextEqual]
  have minCapacity : min bytes.length CoreOverflow.overflowCapacity =
      CoreOverflow.overflowCapacity := Nat.min_eq_right (by omega)
  rw [minCapacity, payloadTake]
  have remaining : bytes.length - CoreOverflow.overflowCapacity =
      (bytes.drop CoreOverflow.overflowCapacity).length := by simp
  rw [remaining]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [nextValue, tailDecoded]
  exact congrArg some (List.take_append_drop _ bytes)

private theorem readOverflowStep_of_decoded (source : PageSource)
    (recurse : Nat → Nat → Option (List UInt8)) (remaining pageNumber : Nat)
    (page : List UInt8) (overflow : OverflowPage PhysicalCodec.usablePageSize)
    (suffix : List UInt8)
    (read : source.readPage pageNumber = some page)
    (decoded : decodeOverflowPage PhysicalCodec.usablePageSize page =
      some (overflow, suffix)) :
    readOverflowStep source recurse remaining pageNumber =
      finishOverflowStep recurse remaining overflow suffix := by
  unfold readOverflowStep
  rw [read]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [decoded]
  simp only [Option.bind_eq_bind, Option.bind_some]

private theorem readOverflowStep_generated_step (count : Nat)
    (source : PageSource) (recurse : Nat → Nat → Option (List UInt8))
    (start : Nat) (bytes : List UInt8) (countPositive : 0 < count)
    (tooLarge : CoreOverflow.overflowCapacity < bytes.length)
    (bounded : start + (count + 1) < 2 ^ 32)
    (firstRead : source.readPage start = some
      (CoreOverflow.overflowPageBytes start (count + 1) 0 bytes))
    (tailDecoded : recurse
      (bytes.drop CoreOverflow.overflowCapacity).length (start + 1) =
        some (bytes.drop CoreOverflow.overflowCapacity)) :
    readOverflowStep source recurse bytes.length start = some bytes := by
  rw [readOverflowStep_of_decoded source recurse bytes.length start
    (CoreOverflow.overflowPageBytes start (count + 1) 0 bytes)
    (CoreOverflow.generatedOverflowPage start (count + 1) 0 bytes bounded) []
    firstRead (CoreOverflow.decodeOverflowPage_overflowPageBytes start
      (count + 1) 0 bytes bounded)]
  exact finishOverflowStep_generated_step count recurse start bytes
    countPositive tooLarge bounded tailDecoded

private theorem readOverflowFrom_generated_step (count : Nat)
    (source : PageSource) (start : Nat) (bytes : List UInt8)
    (countPositive : 0 < count)
    (tooLarge : CoreOverflow.overflowCapacity < bytes.length)
    (bounded : start + (count + 1) < 2 ^ 32)
    (firstRead : source.readPage start = some
      (CoreOverflow.overflowPageBytes start (count + 1) 0 bytes))
    (tailDecoded : readOverflowFrom source (count + 1)
      (bytes.drop CoreOverflow.overflowCapacity).length (start + 1) =
        some (bytes.drop CoreOverflow.overflowCapacity)) :
    readOverflowFrom source (count + 2) bytes.length start = some bytes := by
  have lengthPositive : 0 < bytes.length := by omega
  obtain ⟨remainingFuel, lengthEqual⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt lengthPositive)
  rw [lengthEqual]
  rw [readOverflowFrom] <;> try omega
  rw [← lengthEqual]
  exact readOverflowStep_generated_step count source
    (readOverflowFrom source (count + 1)) start bytes countPositive tooLarge
    bounded firstRead tailDecoded

set_option maxRecDepth 8192 in
private theorem readOverflowFrom_generated_final_fuel (source : PageSource)
    (start fuel : Nat) (bytes : List UInt8) (nonempty : bytes ≠ [])
    (fits : bytes.length ≤ CoreOverflow.overflowCapacity)
    (fuelPositive : 0 < fuel)
    (bounded : start + 1 < 2 ^ 32)
    (firstRead : source.readPage start = some
      (CoreOverflow.overflowPageBytes start 1 0 bytes)) :
    readOverflowFrom source fuel bytes.length start = some bytes := by
  obtain ⟨remainingFuel, fuelEqual⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt fuelPositive)
  subst fuel
  have lengthPositive : 0 < bytes.length := List.length_pos_iff.mpr nonempty
  obtain ⟨remaining, lengthEqual⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt lengthPositive)
  rw [lengthEqual]
  rw [readOverflowFrom] <;> try omega
  unfold readOverflowStep
  rw [firstRead]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [CoreOverflow.decodeOverflowPage_overflowPageBytes start 1 0 bytes bounded]
  simp only [Option.bind_eq_bind, Option.bind_some]
  unfold finishOverflowStep
  have finalNext := CoreOverflow.generatedOverflowPage_next_final start bytes
    bounded
  have payloadTake := CoreOverflow.generatedOverflowPage_payload_take_final
    start bytes fits bounded
  rw [← lengthEqual, dif_pos rfl, dif_pos fits, finalNext,
    Nat.min_eq_left fits, payloadTake]

private theorem readOverflowFrom_generated_step_fuel (count fuel : Nat)
    (source : PageSource) (start : Nat) (bytes : List UInt8)
    (countPositive : 0 < count)
    (tooLarge : CoreOverflow.overflowCapacity < bytes.length)
    (bounded : start + (count + 1) < 2 ^ 32)
    (firstRead : source.readPage start = some
      (CoreOverflow.overflowPageBytes start (count + 1) 0 bytes))
    (tailDecoded : readOverflowFrom source fuel
      (bytes.drop CoreOverflow.overflowCapacity).length (start + 1) =
        some (bytes.drop CoreOverflow.overflowCapacity)) :
    readOverflowFrom source (fuel + 1) bytes.length start = some bytes := by
  have lengthPositive : 0 < bytes.length := by omega
  obtain ⟨remainingFuel, fuelEqual⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt lengthPositive)
  rw [fuelEqual]
  rw [readOverflowFrom] <;> try omega
  rw [← fuelEqual]
  exact readOverflowStep_generated_step count source
    (readOverflowFrom source fuel) start bytes countPositive tooLarge
    bounded firstRead tailDecoded

/-- Reading every page of a generated overflow chain returns exactly its
logical payload.  Unsigned page-number bounds are explicit: they are the same
condition required by the SQLite 32-bit page-number format. -/
theorem readOverflowFrom_generated :
    ∀ (count : Nat) (source : PageSource) (start : Nat) (bytes : List UInt8),
      CoreOverflow.overflowPageCount bytes = count →
      start + count < 2 ^ 32 →
      ReadsGeneratedOverflow source start count bytes →
      readOverflowFrom source (count + 1) bytes.length start = some bytes
  | 0, source, start, bytes, countEqual, bounded, reads => by
      have empty : bytes = [] :=
        (CoreOverflow.overflowPageCount_eq_zero_iff bytes).mp countEqual
      subst bytes
      simp [readOverflowFrom]
  | count + 1, source, start, bytes, countEqual, bounded, reads => by
      have nonempty : bytes ≠ [] := by
        intro empty
        subst bytes
        simp [CoreOverflow.overflowPageCount] at countEqual
      by_cases fits : bytes.length ≤ CoreOverflow.overflowCapacity
      · have pageCountOne :=
          CoreOverflow.overflowPageCount_eq_one_of_length_le nonempty fits
        have countZero : count = 0 := by omega
        subst count
        apply readOverflowFrom_generated_final source start bytes nonempty fits
          (by simpa using bounded)
        simpa using reads 0 (by omega)
      · have tooLarge : CoreOverflow.overflowCapacity < bytes.length := by omega
        let tail := bytes.drop CoreOverflow.overflowCapacity
        have tailNonempty : tail ≠ [] := by
          apply List.ne_nil_of_length_pos
          simp [tail]
          omega
        have tailCount := CoreOverflow.overflowPageCount_drop_capacity tooLarge
        have tailCountEqual : CoreOverflow.overflowPageCount tail = count := by
          simp only [tail]
          omega
        have countPositive : 0 < count := by
          have := CoreOverflow.overflowPageCount_positive tailNonempty
          omega
        have tailBounded : start + 1 + count < 2 ^ 32 := by omega
        have tailReads : ReadsGeneratedOverflow source (start + 1) count tail := by
          intro offset offsetBound
          have originalRead := reads (offset + 1) (by omega)
          rw [show start + 1 + offset = start + (offset + 1) by omega,
            originalRead]
          congr 1
          exact CoreOverflow.overflowPageBytes_succ start (count + 1) count
            offset bytes rfl
        have tailDecoded := readOverflowFrom_generated count source (start + 1)
          tail tailCountEqual tailBounded tailReads
        apply readOverflowFrom_generated_step count source start bytes
          countPositive tooLarge bounded
        · simpa using reads 0 (by omega)
        · simpa [tail] using tailDecoded

/-- Generated overflow chains decode with any fuel strictly larger than their
page count.  This is the form used by the live pager, whose shared fuel is the
database page count rather than a chain-specific constant. -/
theorem readOverflowFrom_generated_fuel :
    ∀ (count : Nat) (source : PageSource) (start : Nat) (bytes : List UInt8)
      (fuel : Nat),
      CoreOverflow.overflowPageCount bytes = count →
      start + count < 2 ^ 32 →
      ReadsGeneratedOverflow source start count bytes →
      count < fuel →
      readOverflowFrom source fuel bytes.length start = some bytes
  | 0, source, start, bytes, fuel, countEqual, _, _, _ => by
      have empty : bytes = [] :=
        (CoreOverflow.overflowPageCount_eq_zero_iff bytes).mp countEqual
      subst bytes
      simp [readOverflowFrom]
  | count + 1, source, start, bytes, fuel, countEqual, bounded, reads,
      fuelEnough => by
      have nonempty : bytes ≠ [] := by
        intro empty
        subst bytes
        simp [CoreOverflow.overflowPageCount] at countEqual
      by_cases fits : bytes.length ≤ CoreOverflow.overflowCapacity
      · have pageCountOne :=
          CoreOverflow.overflowPageCount_eq_one_of_length_le nonempty fits
        have countZero : count = 0 := by omega
        subst count
        apply readOverflowFrom_generated_final_fuel source start fuel bytes
          nonempty fits (by omega) (by simpa using bounded)
        simpa using reads 0 (by omega)
      · have tooLarge : CoreOverflow.overflowCapacity < bytes.length := by omega
        let tail := bytes.drop CoreOverflow.overflowCapacity
        have tailNonempty : tail ≠ [] := by
          apply List.ne_nil_of_length_pos
          simp [tail]
          omega
        have tailCount := CoreOverflow.overflowPageCount_drop_capacity tooLarge
        have tailCountEqual : CoreOverflow.overflowPageCount tail = count := by
          simp only [tail]
          omega
        have countPositive : 0 < count := by
          have := CoreOverflow.overflowPageCount_positive tailNonempty
          omega
        have tailBounded : start + 1 + count < 2 ^ 32 := by omega
        have tailReads : ReadsGeneratedOverflow source (start + 1) count tail := by
          intro offset offsetBound
          have originalRead := reads (offset + 1) (by omega)
          rw [show start + 1 + offset = start + (offset + 1) by omega,
            originalRead]
          congr 1
          exact CoreOverflow.overflowPageBytes_succ start (count + 1) count
            offset bytes rfl
        obtain ⟨tailFuel, fuelEqual⟩ :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (show 0 < fuel by omega))
        have tailDecoded := readOverflowFrom_generated_fuel count source
          (start + 1) tail tailFuel tailCountEqual tailBounded tailReads
          (by omega)
        rw [fuelEqual]
        apply readOverflowFrom_generated_step_fuel count tailFuel source start
          bytes countPositive tooLarge bounded
        · simpa using reads 0 (by omega)
        · simpa [tail] using tailDecoded

def finishOverflowPayloadBytesFrom (source : PageSource) (fuel remaining : Nat)
    (localBytes : List UInt8) (first : PageNumber) (suffix : List UInt8) :
    Option (List UInt8 × List UInt8) := do
  let rest ← readOverflowFrom source fuel remaining first.value.val
  some (localBytes ++ rest, suffix)

def decodeOverflowAfterLocalBytesFrom (source : PageSource)
    (fuel remaining : Nat) (localBytes : List UInt8) (input : List UInt8) :
    Option (List UInt8 × List UInt8) := do
  let (first, suffix) ← decodePageNumber input
  finishOverflowPayloadBytesFrom source fuel remaining localBytes first suffix

def decodeOverflowPayloadBytesFrom (source : PageSource) (fuel payloadSize
    localSize : Nat) (input : List UInt8) :
    Option (List UInt8 × List UInt8) := do
  let (localPayload, afterLocal) ← decodeSizedBytes localSize input
  decodeOverflowAfterLocalBytesFrom source fuel (payloadSize - localSize)
    localPayload.bytes afterLocal

private theorem decodeOverflowPayloadBytesFrom_of_decoded
    (source : PageSource) (fuel payloadSize localSize : Nat)
    (input : List UInt8) (localPayload : SizedBytes localSize)
    (afterLocal : List UInt8) (result : List UInt8 × List UInt8)
    (localDecoded : decodeSizedBytes localSize input =
      some (localPayload, afterLocal))
    (restDecoded : decodeOverflowAfterLocalBytesFrom source fuel
      (payloadSize - localSize) localPayload.bytes afterLocal = some result) :
    decodeOverflowPayloadBytesFrom source fuel payloadSize localSize input =
      some result := by
  unfold decodeOverflowPayloadBytesFrom
  rw [localDecoded]
  simp only [Option.bind_eq_bind, Option.bind]
  exact restDecoded

def decodeTablePayloadBytesFrom (source : PageSource) (fuel payloadSize : Nat)
    (input : List UInt8) : Option (List UInt8 × List UInt8) :=
  if _fits : payloadSize ≤ tableLeafMaxLocal PhysicalCodec.usablePageSize then do
    let (payload, suffix) ← decodeSizedBytes payloadSize input
    some (payload.bytes, suffix)
  else
    decodeOverflowPayloadBytesFrom source fuel payloadSize
      (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize payloadSize) input

theorem finishOverflowPayloadBytesFrom_generated (source : PageSource)
    (localBytes overflowBytes suffix : List UInt8) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount overflowBytes <
      2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount overflowBytes) overflowBytes) :
    finishOverflowPayloadBytesFrom source
        (CoreOverflow.overflowPageCount overflowBytes + 1)
        overflowBytes.length localBytes first suffix =
      some (localBytes ++ overflowBytes, suffix) := by
  unfold finishOverflowPayloadBytesFrom
  rw [readOverflowFrom_generated
    (CoreOverflow.overflowPageCount overflowBytes) source first.value.val
    overflowBytes rfl bounded reads]
  simp only [Option.bind_eq_bind, Option.bind]

theorem decodeOverflowAfterLocalBytesFrom_generated (source : PageSource)
    (localBytes overflowBytes suffix : List UInt8) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount overflowBytes <
      2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount overflowBytes) overflowBytes) :
    decodeOverflowAfterLocalBytesFrom source
        (CoreOverflow.overflowPageCount overflowBytes + 1)
        overflowBytes.length localBytes (first.encode ++ suffix) =
      some (localBytes ++ overflowBytes, suffix) := by
  unfold decodeOverflowAfterLocalBytesFrom
  rw [decodePageNumber_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  exact finishOverflowPayloadBytesFrom_generated source localBytes overflowBytes
    suffix first bounded reads

theorem decodeOverflowPayloadBytesFrom_generated (source : PageSource)
    (payload suffix : List UInt8) (localSize : Nat)
    (localLe : localSize ≤ payload.length) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      (payload.drop localSize) < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount (payload.drop localSize))
      (payload.drop localSize)) :
    decodeOverflowPayloadBytesFrom source
        (CoreOverflow.overflowPageCount (payload.drop localSize) + 1)
        payload.length localSize
        (payload.take localSize ++ first.encode ++ suffix) =
      some (payload, suffix) := by
  let localPayload : SizedBytes localSize :=
    ⟨payload.take localSize, List.length_take_of_le localLe⟩
  have localDecoded := decodeSizedBytes_append localPayload
    (first.encode ++ suffix)
  have remaining : payload.length - localSize = (payload.drop localSize).length :=
    by simp
  have afterDecoded : decodeOverflowAfterLocalBytesFrom source
      (CoreOverflow.overflowPageCount (payload.drop localSize) + 1)
      (payload.length - localSize) (payload.take localSize)
      (first.encode ++ suffix) =
        some (payload.take localSize ++ payload.drop localSize, suffix) := by
    rw [remaining]
    exact decodeOverflowAfterLocalBytesFrom_generated source
      (payload.take localSize) (payload.drop localSize) suffix first bounded reads
  have decoded := decodeOverflowPayloadBytesFrom_of_decoded source
    (CoreOverflow.overflowPageCount (payload.drop localSize) + 1)
    payload.length localSize
    (payload.take localSize ++ first.encode ++ suffix) localPayload
    (first.encode ++ suffix)
    (payload.take localSize ++ payload.drop localSize, suffix)
    (by simpa [List.append_assoc] using localDecoded) afterDecoded
  rw [List.take_append_drop localSize payload] at decoded
  exact decoded

theorem decodeTablePayloadBytesFrom_overflow (source : PageSource)
    (payload suffix : List UInt8)
    (overflows : tableLeafMaxLocal PhysicalCodec.usablePageSize < payload.length)
    (first : PageNumber)
    (bounded : first.value.val +
      CoreOverflow.overflowPageCount
        (payload.drop (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
          payload.length)) < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount
        (payload.drop (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
          payload.length)))
      (payload.drop (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length))) :
    decodeTablePayloadBytesFrom source
        (CoreOverflow.overflowPageCount
          (payload.drop (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
            payload.length)) + 1)
        payload.length
        (payload.take (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
          payload.length) ++ first.encode ++ suffix) =
      some (payload, suffix) := by
  let localSize := tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
    payload.length
  let overflowBytes := payload.drop localSize
  have localLe : localSize ≤ payload.length :=
    tableLeafLocalPayloadSize_le_payload PhysicalCodec.usablePageSize
      payload.length
  unfold decodeTablePayloadBytesFrom
  rw [dif_neg (Nat.not_le_of_lt overflows)]
  exact decodeOverflowPayloadBytesFrom_generated source payload suffix localSize
    localLe first (by simpa [overflowBytes, localSize] using bounded)
    (by simpa [overflowBytes, localSize] using reads)

def decodeRowCellFrom (schema : Core.Schema) (source : PageSource)
    (fuel : Nat) (input : List UInt8) : Option Core.Row := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (rowidBits, afterRowid) ← decodeVarint afterSize
  let (payload, _) ← decodeTablePayloadBytesFrom source fuel
    payloadSize.val afterRowid
  let (record, suffix) ← decodePhysicalRecord payload
  if _consumed : suffix = [] then
    if _sizeMatches : record.encode.length = payloadSize.val then
      CoreRecord.decodeRowFields schema
        (signedIntegerFromUnsigned .eight rowidBits) record.fields
    else none
  else none

/-- Decode one table-leaf cell while retaining the bytes following that cell.
Unlike `decodeRowCellFrom`, this form composes over the contiguous content
area of encoder-produced pages, including cells whose payload continues on
overflow pages. -/
def decodeRowCellWithSuffixFrom (schema : Core.Schema) (source : PageSource)
    (fuel : Nat) (input : List UInt8) : Option (Core.Row × List UInt8) := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (rowidBits, afterRowid) ← decodeVarint afterSize
  let (payload, cellSuffix) ← decodeTablePayloadBytesFrom source fuel
    payloadSize.val afterRowid
  let (record, recordSuffix) ← decodePhysicalRecord payload
  if _consumed : recordSuffix = [] then
    if _sizeMatches : record.encode.length = payloadSize.val then
      let row ← CoreRecord.decodeRowFields schema
        (signedIntegerFromUnsigned .eight rowidBits) record.fields
      some (row, cellSuffix)
    else none
  else none

def decodePackedRowCellsFrom (schema : Core.Schema) (source : PageSource)
    (fuel : Nat) : Nat → List UInt8 → Option (List Core.Row × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (row, afterRow) ←
        decodeRowCellWithSuffixFrom schema source fuel input
      let (rows, suffix) ←
        decodePackedRowCellsFrom schema source fuel count afterRow
      some (row :: rows, suffix)

/-- The general page-source decoder is an inverse of the ordinary inline row
cell encoder.  The explicit local-payload bound is the condition that
distinguishes a self-contained leaf cell from one requiring an overflow
pointer; the packed bulk builder checks this condition before selecting its
non-overflow representation. -/
theorem decodeRowCellFrom_encodeCell {schema : Core.Schema} {row : Core.Row}
    {record : PhysicalRecord} {cell : List UInt8}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (encoded : CoreRecord.encodeCell? schema row = some cell)
    (inline : record.encode.length ≤
      tableLeafMaxLocal PhysicalCodec.usablePageSize)
    (source : PageSource) (fuel : Nat) (suffix : List UInt8) :
    decodeRowCellFrom schema source fuel (cell ++ suffix) = some row := by
  unfold CoreRecord.encodeCell? at encoded
  rw [recordResult] at encoded
  simp only [Option.bind_eq_bind, Option.bind] at encoded
  split at encoded
  next payloadBound =>
    injection encoded with equal
    subst cell
    unfold decodeRowCellFrom
    simp only [List.append_assoc]
    rw [decodeVarint_encode]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [decodeVarint_encode]
    simp only [Option.bind_eq_bind, Option.bind]
    unfold decodeTablePayloadBytesFrom
    rw [dif_pos inline]
    let payload : SizedBytes record.encode.length := ⟨record.encode, rfl⟩
    have payloadDecoded := decodeSizedBytes_append payload suffix
    rw [payloadDecoded]
    simp only [signedIntegerFromBits_toBits, Option.bind_eq_bind, Option.bind]
    have recordDecoded := decodePhysicalRecord_encode record []
    simp only [List.append_nil] at recordDecoded
    rw [recordDecoded]
    simp only [dif_pos True.intro]
    rw [show record.fields = CoreRecord.rowRecordFields schema row from
      CoreRecord.rowRecord_fields recordResult]
    rw [CoreRecord.decodeRowFields_record valid]
  next payloadUnbounded => contradiction

theorem decodeRowCellWithSuffixFrom_encodeCell {schema : Core.Schema}
    {row : Core.Row} {record : PhysicalRecord} {cell : List UInt8}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (encoded : CoreRecord.encodeCell? schema row = some cell)
    (inline : record.encode.length ≤
      tableLeafMaxLocal PhysicalCodec.usablePageSize)
    (source : PageSource) (fuel : Nat) (suffix : List UInt8) :
    decodeRowCellWithSuffixFrom schema source fuel (cell ++ suffix) =
      some (row, suffix) := by
  unfold CoreRecord.encodeCell? at encoded
  rw [recordResult] at encoded
  simp only [Option.bind_eq_bind, Option.bind] at encoded
  split at encoded
  next payloadBound =>
    injection encoded with equal
    subst cell
    unfold decodeRowCellWithSuffixFrom
    simp only [List.append_assoc]
    rw [decodeVarint_encode]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [decodeVarint_encode]
    simp only [Option.bind_eq_bind, Option.bind]
    unfold decodeTablePayloadBytesFrom
    rw [dif_pos inline]
    let payload : SizedBytes record.encode.length := ⟨record.encode, rfl⟩
    have payloadDecoded := decodeSizedBytes_append payload suffix
    rw [payloadDecoded]
    simp only [signedIntegerFromBits_toBits, Option.bind_eq_bind, Option.bind]
    have recordDecoded := decodePhysicalRecord_encode record []
    simp only [List.append_nil] at recordDecoded
    rw [recordDecoded]
    simp only [dif_pos True.intro]
    rw [show record.fields = CoreRecord.rowRecordFields schema row from
      CoreRecord.rowRecord_fields recordResult]
    rw [CoreRecord.decodeRowFields_record valid]
  next payloadUnbounded => contradiction

theorem decodeRowCellFrom_overflow {schema : Core.Schema} {row : Core.Row}
    {record : PhysicalRecord}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (payloadBound : record.encode.length < 2 ^ 64)
    (overflows : tableLeafMaxLocal PhysicalCodec.usablePageSize <
      record.encode.length)
    (source : PageSource) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      (record.encode.drop (tableLeafLocalPayloadSize
        PhysicalCodec.usablePageSize record.encode.length)) < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount
        (record.encode.drop (tableLeafLocalPayloadSize
          PhysicalCodec.usablePageSize record.encode.length)))
      (record.encode.drop (tableLeafLocalPayloadSize
        PhysicalCodec.usablePageSize record.encode.length)))
    (suffix : List UInt8) :
    let size : U64Value := ⟨record.encode.length, by simpa using payloadBound⟩
    decodeRowCellFrom schema source
        (CoreOverflow.overflowPageCount
          (record.encode.drop (tableLeafLocalPayloadSize
            PhysicalCodec.usablePageSize record.encode.length)) + 1)
        (encodeVarint size ++ encodeVarint (signedInteger64Bits row.rowid) ++
          record.encode.take (tableLeafLocalPayloadSize
            PhysicalCodec.usablePageSize record.encode.length) ++
          first.encode ++ suffix) = some row := by
  dsimp only
  unfold decodeRowCellFrom
  simp only [List.append_assoc]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [← List.append_assoc
    (record.encode.take (tableLeafLocalPayloadSize
      PhysicalCodec.usablePageSize record.encode.length)) first.encode suffix]
  rw [decodeTablePayloadBytesFrom_overflow source record.encode suffix
    overflows first bounded reads]
  simp only [signedIntegerFromBits_toBits, Option.bind_eq_bind, Option.bind]
  have recordDecoded := decodePhysicalRecord_encode record []
  simp only [List.append_nil] at recordDecoded
  rw [recordDecoded]
  simp only [dif_pos True.intro]
  rw [show record.fields = CoreRecord.rowRecordFields schema row from
    CoreRecord.rowRecord_fields recordResult]
  rw [CoreRecord.decodeRowFields_record valid]

theorem decodeRowCellFrom_tableCellPlan_overflow {schema : Core.Schema}
    {row : Core.Row} {record : PhysicalRecord} {plan : CoreOverflow.CellPlan}
    {cell : List UInt8}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (planned : CoreOverflow.tableCellPlan? schema row = some plan)
    (overflows : tableLeafMaxLocal PhysicalCodec.usablePageSize <
      record.encode.length)
    (source : PageSource) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      plan.overflowBytes < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount plan.overflowBytes) plan.overflowBytes)
    (cellBuilt : plan.cellBytes? (some first.value.val) = some cell)
    (suffix : List UInt8) :
    decodeRowCellFrom schema source
      (CoreOverflow.overflowPageCount plan.overflowBytes + 1)
      (cell ++ suffix) = some row := by
  unfold CoreOverflow.tableCellPlan? at planned
  rw [recordResult] at planned
  simp only [Option.bind_eq_bind, Option.bind] at planned
  split at planned
  next payloadBound =>
    injection planned with planEqual
    subst plan
    unfold CoreOverflow.CellPlan.cellBytes? at cellBuilt
    simp only [CoreOverflow.maxLocal, CoreOverflow.CellPlan.localBytes,
      CoreOverflow.localSize] at cellBuilt
    rw [dif_neg (Nat.not_le_of_lt overflows)] at cellBuilt
    simp only [Option.bind_eq_bind, Option.bind] at cellBuilt
    rw [CoreOverflow.boundedPageNumber?_page first] at cellBuilt
    injection cellBuilt with cellEqual
    subst cell
    exact decodeRowCellFrom_overflow valid recordResult payloadBound overflows
      source first (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using bounded)
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using reads) suffix
  next payloadUnbounded => contradiction

theorem decodeRowCellFrom_tableCellPlan_inline {schema : Core.Schema}
    {row : Core.Row} {record : PhysicalRecord} {plan : CoreOverflow.CellPlan}
    {cell : List UInt8}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (planned : CoreOverflow.tableCellPlan? schema row = some plan)
    (inline : record.encode.length ≤
      tableLeafMaxLocal PhysicalCodec.usablePageSize)
    (source : PageSource) (fuel : Nat) (firstOverflow : Option Nat)
    (cellBuilt : plan.cellBytes? firstOverflow = some cell)
    (suffix : List UInt8) :
    decodeRowCellFrom schema source fuel (cell ++ suffix) = some row := by
  unfold CoreOverflow.tableCellPlan? at planned
  rw [recordResult] at planned
  simp only [Option.bind_eq_bind, Option.bind] at planned
  split at planned
  next payloadBound =>
    injection planned with planEqual
    subst plan
    unfold CoreOverflow.CellPlan.cellBytes? at cellBuilt
    simp only [CoreOverflow.maxLocal] at cellBuilt
    rw [dif_pos inline] at cellBuilt
    injection cellBuilt with cellEqual
    subst cell
    have encoded : CoreRecord.encodeCell? schema row = some
        (encodeVarint ⟨record.encode.length, by simpa using payloadBound⟩ ++
          encodeVarint (signedInteger64Bits row.rowid) ++ record.encode) := by
      unfold CoreRecord.encodeCell?
      rw [recordResult]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [dif_pos payloadBound]
    exact decodeRowCellFrom_encodeCell valid recordResult encoded inline source
      fuel suffix
  next payloadUnbounded => contradiction

theorem decodeRowCellWithSuffixFrom_tableCellPlan_inline {schema : Core.Schema}
    {row : Core.Row} {record : PhysicalRecord} {plan : CoreOverflow.CellPlan}
    {cell : List UInt8}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (planned : CoreOverflow.tableCellPlan? schema row = some plan)
    (inline : record.encode.length ≤
      tableLeafMaxLocal PhysicalCodec.usablePageSize)
    (source : PageSource) (fuel : Nat) (firstOverflow : Option Nat)
    (cellBuilt : plan.cellBytes? firstOverflow = some cell)
    (suffix : List UInt8) :
    decodeRowCellWithSuffixFrom schema source fuel (cell ++ suffix) =
      some (row, suffix) := by
  unfold CoreOverflow.tableCellPlan? at planned
  rw [recordResult] at planned
  simp only [Option.bind_eq_bind, Option.bind] at planned
  split at planned
  next payloadBound =>
    injection planned with planEqual
    subst plan
    unfold CoreOverflow.CellPlan.cellBytes? at cellBuilt
    simp only [CoreOverflow.maxLocal] at cellBuilt
    rw [dif_pos inline] at cellBuilt
    injection cellBuilt with cellEqual
    subst cell
    have encoded : CoreRecord.encodeCell? schema row = some
        (encodeVarint ⟨record.encode.length, by simpa using payloadBound⟩ ++
          encodeVarint (signedInteger64Bits row.rowid) ++ record.encode) := by
      unfold CoreRecord.encodeCell?
      rw [recordResult]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [dif_pos payloadBound]
    exact decodeRowCellWithSuffixFrom_encodeCell valid recordResult encoded
      inline source fuel suffix
  next payloadUnbounded => contradiction

theorem finishOverflowPayloadBytesFrom_generated_fuel (source : PageSource)
    (fuel : Nat) (localBytes overflowBytes suffix : List UInt8)
    (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount overflowBytes <
      2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount overflowBytes) overflowBytes)
    (fuelEnough : CoreOverflow.overflowPageCount overflowBytes < fuel) :
    finishOverflowPayloadBytesFrom source fuel overflowBytes.length localBytes
      first suffix = some (localBytes ++ overflowBytes, suffix) := by
  unfold finishOverflowPayloadBytesFrom
  rw [readOverflowFrom_generated_fuel
    (CoreOverflow.overflowPageCount overflowBytes) source first.value.val
    overflowBytes fuel rfl bounded reads fuelEnough]
  simp only [Option.bind_eq_bind, Option.bind]

theorem decodeOverflowAfterLocalBytesFrom_generated_fuel (source : PageSource)
    (fuel : Nat) (localBytes overflowBytes suffix : List UInt8)
    (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount overflowBytes <
      2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount overflowBytes) overflowBytes)
    (fuelEnough : CoreOverflow.overflowPageCount overflowBytes < fuel) :
    decodeOverflowAfterLocalBytesFrom source fuel overflowBytes.length
      localBytes (first.encode ++ suffix) =
        some (localBytes ++ overflowBytes, suffix) := by
  unfold decodeOverflowAfterLocalBytesFrom
  rw [decodePageNumber_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  exact finishOverflowPayloadBytesFrom_generated_fuel source fuel localBytes
    overflowBytes suffix first bounded reads fuelEnough

theorem decodeOverflowPayloadBytesFrom_generated_fuel (source : PageSource)
    (fuel : Nat) (payload suffix : List UInt8) (localSize : Nat)
    (localLe : localSize ≤ payload.length) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      (payload.drop localSize) < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount (payload.drop localSize))
      (payload.drop localSize))
    (fuelEnough : CoreOverflow.overflowPageCount (payload.drop localSize) <
      fuel) :
    decodeOverflowPayloadBytesFrom source fuel payload.length localSize
      (payload.take localSize ++ first.encode ++ suffix) =
        some (payload, suffix) := by
  let localPayload : SizedBytes localSize :=
    ⟨payload.take localSize, List.length_take_of_le localLe⟩
  have localDecoded := decodeSizedBytes_append localPayload
    (first.encode ++ suffix)
  have remaining : payload.length - localSize = (payload.drop localSize).length :=
    by simp
  have afterDecoded : decodeOverflowAfterLocalBytesFrom source fuel
      (payload.length - localSize) (payload.take localSize)
      (first.encode ++ suffix) =
        some (payload.take localSize ++ payload.drop localSize, suffix) := by
    rw [remaining]
    exact decodeOverflowAfterLocalBytesFrom_generated_fuel source fuel
      (payload.take localSize) (payload.drop localSize) suffix first bounded
      reads fuelEnough
  have decoded := decodeOverflowPayloadBytesFrom_of_decoded source fuel
    payload.length localSize
    (payload.take localSize ++ first.encode ++ suffix) localPayload
    (first.encode ++ suffix)
    (payload.take localSize ++ payload.drop localSize, suffix)
    (by simpa [List.append_assoc] using localDecoded) afterDecoded
  rw [List.take_append_drop localSize payload] at decoded
  exact decoded

theorem decodeTablePayloadBytesFrom_overflow_fuel (source : PageSource)
    (fuel : Nat) (payload suffix : List UInt8)
    (overflows : tableLeafMaxLocal PhysicalCodec.usablePageSize < payload.length)
    (first : PageNumber)
    (bounded : first.value.val +
      CoreOverflow.overflowPageCount
        (payload.drop (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
          payload.length)) < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount
        (payload.drop (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
          payload.length)))
      (payload.drop (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length)))
    (fuelEnough : CoreOverflow.overflowPageCount
      (payload.drop (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length)) < fuel) :
    decodeTablePayloadBytesFrom source fuel payload.length
      (payload.take (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length) ++ first.encode ++ suffix) =
      some (payload, suffix) := by
  let localSize := tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
    payload.length
  let overflowBytes := payload.drop localSize
  have localLe : localSize ≤ payload.length :=
    tableLeafLocalPayloadSize_le_payload PhysicalCodec.usablePageSize
      payload.length
  unfold decodeTablePayloadBytesFrom
  rw [dif_neg (Nat.not_le_of_lt overflows)]
  exact decodeOverflowPayloadBytesFrom_generated_fuel source fuel payload suffix
    localSize localLe first
    (by simpa [overflowBytes, localSize] using bounded)
    (by simpa [overflowBytes, localSize] using reads)
    (by simpa [overflowBytes, localSize] using fuelEnough)

theorem decodeRowCellFrom_overflow_fuel {schema : Core.Schema} {row : Core.Row}
    {record : PhysicalRecord}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (payloadBound : record.encode.length < 2 ^ 64)
    (overflows : tableLeafMaxLocal PhysicalCodec.usablePageSize <
      record.encode.length)
    (source : PageSource) (fuel : Nat) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      (record.encode.drop (tableLeafLocalPayloadSize
        PhysicalCodec.usablePageSize record.encode.length)) < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount
        (record.encode.drop (tableLeafLocalPayloadSize
          PhysicalCodec.usablePageSize record.encode.length)))
      (record.encode.drop (tableLeafLocalPayloadSize
        PhysicalCodec.usablePageSize record.encode.length)))
    (fuelEnough : CoreOverflow.overflowPageCount
      (record.encode.drop (tableLeafLocalPayloadSize
        PhysicalCodec.usablePageSize record.encode.length)) < fuel)
    (suffix : List UInt8) :
    let size : U64Value := ⟨record.encode.length, by simpa using payloadBound⟩
    decodeRowCellFrom schema source fuel
      (encodeVarint size ++ encodeVarint (signedInteger64Bits row.rowid) ++
        record.encode.take (tableLeafLocalPayloadSize
          PhysicalCodec.usablePageSize record.encode.length) ++
        first.encode ++ suffix) = some row := by
  dsimp only
  unfold decodeRowCellFrom
  simp only [List.append_assoc]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [← List.append_assoc
    (record.encode.take (tableLeafLocalPayloadSize
      PhysicalCodec.usablePageSize record.encode.length)) first.encode suffix]
  rw [decodeTablePayloadBytesFrom_overflow_fuel source fuel record.encode suffix
    overflows first bounded reads fuelEnough]
  simp only [signedIntegerFromBits_toBits, Option.bind_eq_bind, Option.bind]
  have recordDecoded := decodePhysicalRecord_encode record []
  simp only [List.append_nil] at recordDecoded
  rw [recordDecoded]
  simp only [dif_pos True.intro]
  rw [show record.fields = CoreRecord.rowRecordFields schema row from
    CoreRecord.rowRecord_fields recordResult]
  rw [CoreRecord.decodeRowFields_record valid]

theorem decodeRowCellWithSuffixFrom_overflow_fuel {schema : Core.Schema}
    {row : Core.Row} {record : PhysicalRecord}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (payloadBound : record.encode.length < 2 ^ 64)
    (overflows : tableLeafMaxLocal PhysicalCodec.usablePageSize <
      record.encode.length)
    (source : PageSource) (fuel : Nat) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      (record.encode.drop (tableLeafLocalPayloadSize
        PhysicalCodec.usablePageSize record.encode.length)) < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount
        (record.encode.drop (tableLeafLocalPayloadSize
          PhysicalCodec.usablePageSize record.encode.length)))
      (record.encode.drop (tableLeafLocalPayloadSize
        PhysicalCodec.usablePageSize record.encode.length)))
    (fuelEnough : CoreOverflow.overflowPageCount
      (record.encode.drop (tableLeafLocalPayloadSize
        PhysicalCodec.usablePageSize record.encode.length)) < fuel)
    (suffix : List UInt8) :
    let size : U64Value := ⟨record.encode.length, by simpa using payloadBound⟩
    decodeRowCellWithSuffixFrom schema source fuel
      (encodeVarint size ++ encodeVarint (signedInteger64Bits row.rowid) ++
        record.encode.take (tableLeafLocalPayloadSize
          PhysicalCodec.usablePageSize record.encode.length) ++
        first.encode ++ suffix) = some (row, suffix) := by
  dsimp only
  unfold decodeRowCellWithSuffixFrom
  simp only [List.append_assoc]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeVarint_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [← List.append_assoc
    (record.encode.take (tableLeafLocalPayloadSize
      PhysicalCodec.usablePageSize record.encode.length)) first.encode suffix]
  rw [decodeTablePayloadBytesFrom_overflow_fuel source fuel record.encode suffix
    overflows first bounded reads fuelEnough]
  simp only [signedIntegerFromBits_toBits, Option.bind_eq_bind, Option.bind]
  have recordDecoded := decodePhysicalRecord_encode record []
  simp only [List.append_nil] at recordDecoded
  rw [recordDecoded]
  simp only [dif_pos True.intro]
  rw [show record.fields = CoreRecord.rowRecordFields schema row from
    CoreRecord.rowRecord_fields recordResult]
  rw [CoreRecord.decodeRowFields_record valid]

theorem decodeRowCellFrom_tableCellPlan_overflow_fuel {schema : Core.Schema}
    {row : Core.Row} {record : PhysicalRecord} {plan : CoreOverflow.CellPlan}
    {cell : List UInt8}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (planned : CoreOverflow.tableCellPlan? schema row = some plan)
    (overflows : tableLeafMaxLocal PhysicalCodec.usablePageSize <
      record.encode.length)
    (source : PageSource) (fuel : Nat) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      plan.overflowBytes < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount plan.overflowBytes) plan.overflowBytes)
    (fuelEnough : CoreOverflow.overflowPageCount plan.overflowBytes < fuel)
    (cellBuilt : plan.cellBytes? (some first.value.val) = some cell)
    (suffix : List UInt8) :
    decodeRowCellFrom schema source fuel (cell ++ suffix) = some row := by
  unfold CoreOverflow.tableCellPlan? at planned
  rw [recordResult] at planned
  simp only [Option.bind_eq_bind, Option.bind] at planned
  split at planned
  next payloadBound =>
    injection planned with planEqual
    subst plan
    unfold CoreOverflow.CellPlan.cellBytes? at cellBuilt
    simp only [CoreOverflow.maxLocal, CoreOverflow.CellPlan.localBytes,
      CoreOverflow.localSize] at cellBuilt
    rw [dif_neg (Nat.not_le_of_lt overflows)] at cellBuilt
    simp only [Option.bind_eq_bind, Option.bind] at cellBuilt
    rw [CoreOverflow.boundedPageNumber?_page first] at cellBuilt
    injection cellBuilt with cellEqual
    subst cell
    exact decodeRowCellFrom_overflow_fuel valid recordResult payloadBound
      overflows source fuel first
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using bounded)
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using reads)
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using fuelEnough) suffix
  next payloadUnbounded => contradiction

theorem decodeRowCellWithSuffixFrom_tableCellPlan_overflow_fuel
    {schema : Core.Schema} {row : Core.Row} {record : PhysicalRecord}
    {plan : CoreOverflow.CellPlan} {cell : List UInt8}
    (valid : row.WellFormed schema)
    (recordResult : CoreRecord.rowRecord? schema row = some record)
    (planned : CoreOverflow.tableCellPlan? schema row = some plan)
    (overflows : tableLeafMaxLocal PhysicalCodec.usablePageSize <
      record.encode.length)
    (source : PageSource) (fuel : Nat) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      plan.overflowBytes < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount plan.overflowBytes) plan.overflowBytes)
    (fuelEnough : CoreOverflow.overflowPageCount plan.overflowBytes < fuel)
    (cellBuilt : plan.cellBytes? (some first.value.val) = some cell)
    (suffix : List UInt8) :
    decodeRowCellWithSuffixFrom schema source fuel (cell ++ suffix) =
      some (row, suffix) := by
  unfold CoreOverflow.tableCellPlan? at planned
  rw [recordResult] at planned
  simp only [Option.bind_eq_bind, Option.bind] at planned
  split at planned
  next payloadBound =>
    injection planned with planEqual
    subst plan
    unfold CoreOverflow.CellPlan.cellBytes? at cellBuilt
    simp only [CoreOverflow.maxLocal, CoreOverflow.CellPlan.localBytes,
      CoreOverflow.localSize] at cellBuilt
    rw [dif_neg (Nat.not_le_of_lt overflows)] at cellBuilt
    simp only [Option.bind_eq_bind, Option.bind] at cellBuilt
    rw [CoreOverflow.boundedPageNumber?_page first] at cellBuilt
    injection cellBuilt with cellEqual
    subst cell
    exact decodeRowCellWithSuffixFrom_overflow_fuel valid recordResult
      payloadBound overflows source fuel first
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using bounded)
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using reads)
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using fuelEnough) suffix
  next payloadUnbounded => contradiction

/-- Resolving a list of proof-carrying row-cell plans and reading precisely
the generated overflow-page interval reconstructs every logical row.  The
proof splits the page interval at each plan, so no row can consume pages owned
by its successor. -/
theorem decodeRowCellsFrom_resolvePlans (schema : Core.Schema)
    (source : PageSource) (fuel : Nat) :
    ∀ (rows : List Core.Row) (plans : List CoreOverflow.CellPlan)
      (next : Nat) (resolved : CoreOverflow.Resolved),
      (∀ row ∈ rows, row.WellFormed schema) →
      rows.mapM (CoreOverflow.tableCellPlan? schema) = some plans →
      CoreOverflow.resolvePlans next plans = some resolved →
      0 < next →
      next + resolved.pages.length < 2 ^ 32 →
      resolved.pages.length < fuel →
      ReadsPagesFrom source next resolved.pages →
      resolved.cells.mapM (decodeRowCellFrom schema source fuel) = some rows
  | [], plans, next, resolved, _, planned, resolvedResult, _, _, _, _ => by
      simp only [List.mapM_nil, pure, Pure.pure] at planned
      injection planned with plansEqual
      subst plans
      simp only [CoreOverflow.resolvePlans, Option.some.injEq] at resolvedResult
      subst resolved
      rfl
  | row :: rows, plans, next, resolved, valid, planned, resolvedResult,
      nextPositive, pageBound, fuelBound, reads => by
      cases planResult : CoreOverflow.tableCellPlan? schema row with
      | none => simp [List.mapM_cons, planResult] at planned
      | some plan =>
        cases tailPlanResult : rows.mapM (CoreOverflow.tableCellPlan? schema) with
        | none => simp [List.mapM_cons, planResult, tailPlanResult] at planned
        | some tailPlans =>
          simp only [List.mapM_cons, planResult, tailPlanResult,
            Option.bind_eq_bind, Option.bind] at planned
          injection planned with plansEqual
          subst plans
          simp only [CoreOverflow.resolvePlans, Option.bind_eq_bind,
            Option.bind] at resolvedResult
          cases cellResult : plan.cellBytes?
              (if CoreOverflow.overflowPageCount plan.overflowBytes = 0 then
                none else some next) with
          | none => simp [cellResult] at resolvedResult
          | some cell =>
            simp only [cellResult] at resolvedResult
            cases pagesResult : CoreOverflow.makeOverflowPages? next
                plan.overflowBytes with
            | none => simp [pagesResult] at resolvedResult
            | some pages =>
              simp only [pagesResult] at resolvedResult
              cases restResult : CoreOverflow.resolvePlans
                  (next + pages.length) tailPlans with
              | none => simp [restResult] at resolvedResult
              | some rest =>
                simp only [restResult, Option.some.injEq] at resolvedResult
                subst resolved
                have headReads : ReadsPagesFrom source next pages :=
                  ReadsPagesFrom.left reads
                have tailReads : ReadsPagesFrom source (next + pages.length)
                    rest.pages := ReadsPagesFrom.right reads
                have pagesLength :=
                  CoreOverflow.makeOverflowPages?_length pagesResult
                have tailDecoded := decodeRowCellsFrom_resolvePlans schema source
                  fuel rows tailPlans (next + pages.length) rest
                  (fun candidate member => valid candidate (by simp [member]))
                  tailPlanResult restResult (by omega)
                  (by simp only [List.length_append] at pageBound; omega)
                  (by simp only [List.length_append] at fuelBound; omega)
                  tailReads
                cases recordResult : CoreRecord.rowRecord? schema row with
                | none =>
                  unfold CoreOverflow.tableCellPlan? at planResult
                  simp [recordResult] at planResult
                | some record =>
                  have plannedHead := planResult
                  have validHead : row.WellFormed schema := valid row (by simp)
                  by_cases inline : record.encode.length ≤
                      tableLeafMaxLocal PhysicalCodec.usablePageSize
                  · have headDecoded : decodeRowCellFrom schema source fuel cell =
                        some row := by
                      simpa using decodeRowCellFrom_tableCellPlan_inline
                        validHead recordResult plannedHead inline source fuel
                        (if CoreOverflow.overflowPageCount plan.overflowBytes = 0
                          then none else some next) cellResult []
                    simp [headDecoded, tailDecoded]
                  · have overflows : tableLeafMaxLocal
                        PhysicalCodec.usablePageSize < record.encode.length := by
                      omega
                    unfold CoreOverflow.tableCellPlan? at planResult
                    rw [recordResult] at planResult
                    simp only [Option.bind_eq_bind, Option.bind] at planResult
                    split at planResult
                    next payloadBound =>
                      injection planResult with planEqual
                      subst plan
                      have localLt : tableLeafLocalPayloadSize
                          PhysicalCodec.usablePageSize record.encode.length <
                          record.encode.length :=
                        tableLeafLocalPayloadSize_lt_payload_of_overflow
                          PhysicalCodec.usablePageSize record.encode.length
                          overflows
                      have overflowNonempty : record.encode.drop
                          (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
                            record.encode.length) ≠ [] := by
                        apply List.ne_nil_of_length_pos
                        simp
                        omega
                      have countPositive : 0 < CoreOverflow.overflowPageCount
                          (record.encode.drop (tableLeafLocalPayloadSize
                            PhysicalCodec.usablePageSize record.encode.length)) :=
                        CoreOverflow.overflowPageCount_positive overflowNonempty
                      let first : PageNumber :=
                        ⟨⟨next, by
                          simp only [List.length_append] at pageBound
                          omega⟩, nextPositive⟩
                      have cellBuilt :
                          ({
                            kind := CoreOverflow.PayloadKind.table
                            cellPrefix := encodeVarint
                                ⟨record.encode.length, by simpa using payloadBound⟩ ++
                              encodeVarint (signedInteger64Bits row.rowid)
                            payload := record.encode
                          } : CoreOverflow.CellPlan).cellBytes?
                            (some first.value.val) = some cell := by
                        simpa [CoreOverflow.CellPlan.overflowBytes,
                          CoreOverflow.localSize, first,
                          Nat.ne_of_gt countPositive] using cellResult
                      have generated := readsGeneratedOverflow_of_makeOverflowPages
                        source next
                        (record.encode.drop (tableLeafLocalPayloadSize
                          PhysicalCodec.usablePageSize record.encode.length))
                        pages pagesResult headReads
                      have headDecoded : decodeRowCellFrom schema source fuel cell =
                          some row := by
                        simpa using
                          decodeRowCellFrom_tableCellPlan_overflow_fuel validHead
                            recordResult plannedHead overflows source fuel first
                            (by
                              simp only [List.length_append] at pageBound
                              simpa [CoreOverflow.CellPlan.overflowBytes,
                                CoreOverflow.localSize, first, pagesLength] using
                                (show next + pages.length < 2 ^ 32 by omega))
                            (by simpa [CoreOverflow.CellPlan.overflowBytes,
                              CoreOverflow.localSize, first] using generated)
                            (by
                              simp only [List.length_append] at fuelBound
                              simpa [CoreOverflow.CellPlan.overflowBytes,
                                CoreOverflow.localSize, pagesLength] using
                                (show pages.length < fuel by omega))
                            cellBuilt []
                      simp [headDecoded, tailDecoded]
                    next payloadUnbounded => contradiction

/-- The packed content area produced from resolved cell plans decodes
sequentially to the original rows and leaves the caller's suffix untouched. -/
theorem decodePackedRowCellsFrom_resolvePlans (schema : Core.Schema)
    (source : PageSource) (fuel : Nat) :
    ∀ (rows : List Core.Row) (plans : List CoreOverflow.CellPlan)
      (next : Nat) (resolved : CoreOverflow.Resolved),
      (∀ row ∈ rows, row.WellFormed schema) →
      rows.mapM (CoreOverflow.tableCellPlan? schema) = some plans →
      CoreOverflow.resolvePlans next plans = some resolved →
      0 < next →
      next + resolved.pages.length < 2 ^ 32 →
      resolved.pages.length < fuel →
      ReadsPagesFrom source next resolved.pages →
      ∀ suffix,
      decodePackedRowCellsFrom schema source fuel rows.length
        (PhysicalCodec.cellBytes resolved.cells ++ suffix) =
          some (rows, suffix)
  | [], plans, next, resolved, _, planned, resolvedResult, _, _, _, _,
      suffix => by
      simp only [List.mapM_nil, pure, Pure.pure] at planned
      injection planned with plansEqual
      subst plans
      simp only [CoreOverflow.resolvePlans, Option.some.injEq] at resolvedResult
      subst resolved
      rfl
  | row :: rows, plans, next, resolved, valid, planned, resolvedResult,
      nextPositive, pageBound, fuelBound, reads, suffix => by
      cases planResult : CoreOverflow.tableCellPlan? schema row with
      | none => simp [List.mapM_cons, planResult] at planned
      | some plan =>
        cases tailPlanResult : rows.mapM (CoreOverflow.tableCellPlan? schema) with
        | none => simp [List.mapM_cons, planResult, tailPlanResult] at planned
        | some tailPlans =>
          simp only [List.mapM_cons, planResult, tailPlanResult,
            Option.bind_eq_bind, Option.bind] at planned
          injection planned with plansEqual
          subst plans
          simp only [CoreOverflow.resolvePlans, Option.bind_eq_bind,
            Option.bind] at resolvedResult
          cases cellResult : plan.cellBytes?
              (if CoreOverflow.overflowPageCount plan.overflowBytes = 0 then
                none else some next) with
          | none => simp [cellResult] at resolvedResult
          | some cell =>
            simp only [cellResult] at resolvedResult
            cases pagesResult : CoreOverflow.makeOverflowPages? next
                plan.overflowBytes with
            | none => simp [pagesResult] at resolvedResult
            | some pages =>
              simp only [pagesResult] at resolvedResult
              cases restResult : CoreOverflow.resolvePlans
                  (next + pages.length) tailPlans with
              | none => simp [restResult] at resolvedResult
              | some rest =>
                simp only [restResult, Option.some.injEq] at resolvedResult
                subst resolved
                have headReads : ReadsPagesFrom source next pages :=
                  ReadsPagesFrom.left reads
                have tailReads : ReadsPagesFrom source (next + pages.length)
                    rest.pages := ReadsPagesFrom.right reads
                have pagesLength :=
                  CoreOverflow.makeOverflowPages?_length pagesResult
                have tailDecoded :=
                  decodePackedRowCellsFrom_resolvePlans schema source fuel rows
                    tailPlans (next + pages.length) rest
                    (fun candidate member => valid candidate (by simp [member]))
                    tailPlanResult restResult (by omega)
                    (by simp only [List.length_append] at pageBound; omega)
                    (by simp only [List.length_append] at fuelBound; omega)
                    tailReads suffix
                let cellSuffix := PhysicalCodec.cellBytes rest.cells ++ suffix
                cases recordResult : CoreRecord.rowRecord? schema row with
                | none =>
                  unfold CoreOverflow.tableCellPlan? at planResult
                  simp [recordResult] at planResult
                | some record =>
                  have plannedHead := planResult
                  have validHead : row.WellFormed schema := valid row (by simp)
                  by_cases inline : record.encode.length ≤
                      tableLeafMaxLocal PhysicalCodec.usablePageSize
                  · have headDecoded : decodeRowCellWithSuffixFrom schema source
                        fuel (cell ++ cellSuffix) = some (row, cellSuffix) :=
                      decodeRowCellWithSuffixFrom_tableCellPlan_inline validHead
                        recordResult plannedHead inline source fuel
                        (if CoreOverflow.overflowPageCount plan.overflowBytes = 0
                          then none else some next) cellResult cellSuffix
                    change decodePackedRowCellsFrom schema source fuel
                      (rows.length + 1)
                      (cell ++ PhysicalCodec.cellBytes rest.cells ++ suffix) =
                        some (row :: rows, suffix)
                    rw [show cell ++ PhysicalCodec.cellBytes rest.cells ++ suffix =
                        cell ++ cellSuffix by simp [cellSuffix,
                          List.append_assoc]]
                    unfold decodePackedRowCellsFrom
                    rw [headDecoded]
                    simp only [Option.bind_eq_bind, Option.bind]
                    simp only [cellSuffix]
                    rw [tailDecoded]
                  · have overflows : tableLeafMaxLocal
                        PhysicalCodec.usablePageSize < record.encode.length := by
                      omega
                    unfold CoreOverflow.tableCellPlan? at planResult
                    rw [recordResult] at planResult
                    simp only [Option.bind_eq_bind, Option.bind] at planResult
                    split at planResult
                    next payloadBound =>
                      injection planResult with planEqual
                      subst plan
                      have localLt : tableLeafLocalPayloadSize
                          PhysicalCodec.usablePageSize record.encode.length <
                          record.encode.length :=
                        tableLeafLocalPayloadSize_lt_payload_of_overflow
                          PhysicalCodec.usablePageSize record.encode.length
                          overflows
                      have overflowNonempty : record.encode.drop
                          (tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
                            record.encode.length) ≠ [] := by
                        apply List.ne_nil_of_length_pos
                        simp
                        omega
                      have countPositive : 0 < CoreOverflow.overflowPageCount
                          (record.encode.drop (tableLeafLocalPayloadSize
                            PhysicalCodec.usablePageSize record.encode.length)) :=
                        CoreOverflow.overflowPageCount_positive overflowNonempty
                      let first : PageNumber :=
                        ⟨⟨next, by
                          simp only [List.length_append] at pageBound
                          omega⟩, nextPositive⟩
                      have cellBuilt :
                          ({
                            kind := CoreOverflow.PayloadKind.table
                            cellPrefix := encodeVarint
                                ⟨record.encode.length, by simpa using payloadBound⟩ ++
                              encodeVarint (signedInteger64Bits row.rowid)
                            payload := record.encode
                          } : CoreOverflow.CellPlan).cellBytes?
                            (some first.value.val) = some cell := by
                        simpa [CoreOverflow.CellPlan.overflowBytes,
                          CoreOverflow.localSize, first,
                          Nat.ne_of_gt countPositive] using cellResult
                      have generated := readsGeneratedOverflow_of_makeOverflowPages
                        source next
                        (record.encode.drop (tableLeafLocalPayloadSize
                          PhysicalCodec.usablePageSize record.encode.length))
                        pages pagesResult headReads
                      have headDecoded : decodeRowCellWithSuffixFrom schema source
                          fuel (cell ++ cellSuffix) = some (row, cellSuffix) := by
                        exact
                          decodeRowCellWithSuffixFrom_tableCellPlan_overflow_fuel
                            validHead recordResult plannedHead overflows source fuel
                            first
                            (by
                              simp only [List.length_append] at pageBound
                              simpa [CoreOverflow.CellPlan.overflowBytes,
                                CoreOverflow.localSize, first, pagesLength] using
                                (show next + pages.length < 2 ^ 32 by omega))
                            (by simpa [CoreOverflow.CellPlan.overflowBytes,
                              CoreOverflow.localSize, first] using generated)
                            (by
                              simp only [List.length_append] at fuelBound
                              simpa [CoreOverflow.CellPlan.overflowBytes,
                                CoreOverflow.localSize, pagesLength] using
                                (show pages.length < fuel by omega))
                            cellBuilt cellSuffix
                      change decodePackedRowCellsFrom schema source fuel
                        (rows.length + 1)
                        (cell ++ PhysicalCodec.cellBytes rest.cells ++ suffix) =
                          some (row :: rows, suffix)
                      rw [show cell ++ PhysicalCodec.cellBytes rest.cells ++ suffix =
                          cell ++ cellSuffix by simp [cellSuffix,
                            List.append_assoc]]
                      unfold decodePackedRowCellsFrom
                      rw [headDecoded]
                      simp only [Option.bind_eq_bind, Option.bind]
                      simp only [cellSuffix]
                      rw [tailDecoded]
                    next payloadUnbounded => contradiction

/-- The bulk encoder starts at contentStart and lays all cell bodies in key
order. Check the first pointer and the ordering of every following pointer;
SQLite may otherwise reuse bodies in a different physical order. -/
def canonicalPointersBeginAtContent (page : List UInt8) : Bool :=
  match page with
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

theorem canonicalPointersBeginAtContent_leafPageBody
    (cells : List (List UInt8)) (fits : PhysicalCodec.PageFit 0 cells) :
    canonicalPointersBeginAtContent
      (PhysicalCodec.leafPageBody 0 cells) = true := by
  have countBound : cells.length < 65536 := fits.cellCount_lt
  have contentBound : PhysicalCodec.pageSize -
      (PhysicalCodec.cellBytes cells).length < 65536 :=
    PhysicalCodec.contentStart_lt cells
  cases cells with
  | nil =>
      simp [canonicalPointersBeginAtContent, PhysicalCodec.leafPageBody,
        PhysicalCodec.leafHeader, PhysicalCodec.leafPointers,
        PhysicalCodec.cellOffsetsFrom, PhysicalCodec.cellBytes,
        PhysicalCodec.encodeU16Nat, FileFormat.encodeUnsignedFixed,
        FileFormat.decodeU16]
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
      simp [canonicalPointersBeginAtContent, PhysicalCodec.leafPageBody,
        PhysicalCodec.leafHeader, PhysicalCodec.leafPointers,
        PhysicalCodec.cellOffsetsFrom, PhysicalCodec.cellBytes,
        PhysicalCodec.encodeU16Nat, FileFormat.encodeUnsignedFixed,
        FileFormat.decodeU16, Nat.mod_eq_of_lt countBound,
        Nat.mod_eq_of_lt contentBound, restOrdered, decodedCount, decodedContent]

def decodeRowsByPointersFrom (schema : Core.Schema) (source : PageSource)
    (page : List UInt8) : Option (List Core.Row) := do
  let cells ← cellInputs? 0 page
  cells.mapM (decodeRowCellFrom schema source (source.pageCount + 1))

def decodeRowsFrom (schema : Core.Schema) (source : PageSource)
    (page : List UInt8) : Option (List Core.Row) :=
  -- Encoder-produced pages have monotonically packed cell bodies.  Decode
  -- that content sequentially so overflow cells preserve the precise suffix
  -- consumed by the next cell.  Arbitrary SQLite pages retain the tolerant
  -- pointer-directed path.
  if canonicalPointersBeginAtContent page then
    match canonicalLeafContent? 0 page with
    | some (count, content) =>
      match decodePackedRowCellsFrom schema source (source.pageCount + 1)
          count content with
      | some (rows, []) => some rows
      | _ => decodeRowsByPointersFrom schema source page
    | none => decodeRowsByPointersFrom schema source page
  else
    decodeRowsByPointersFrom schema source page

theorem decodeRowsFrom_resolvedLeaf (schema : Core.Schema)
    (source : PageSource) (rows : List Core.Row)
    (plans : List CoreOverflow.CellPlan) (next : Nat)
    (resolved : CoreOverflow.Resolved) (page : CoreFile.Page)
    (valid : ∀ row ∈ rows, row.WellFormed schema)
    (planned : rows.mapM (CoreOverflow.tableCellPlan? schema) = some plans)
    (resolvedResult : CoreOverflow.resolvePlans next plans = some resolved)
    (built : CoreFile.tableLeafPage? resolved.cells = some page)
    (nextPositive : 0 < next)
    (pageBound : next + resolved.pages.length < 2 ^ 32)
    (fuelBound : resolved.pages.length < source.pageCount + 1)
    (reads : ReadsPagesFrom source next resolved.pages) :
    decodeRowsFrom schema source page.bytes = some rows := by
  unfold CoreFile.tableLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 13 0 resolved.cells with
  | none => simp [bodyResult] at built
  | some body =>
    simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
    injection built with pageEqual
    subst page
    rcases CoreFile.leafBody_table_exact bodyResult with ⟨bodyBytes, fits⟩
    have pointers := canonicalPointersBeginAtContent_leafPageBody
      resolved.cells fits
    have content := canonicalLeafContent_leafPageBody [] 0 resolved.cells rfl fits
    have planLength := mapM_length_of_eq_some
      (CoreOverflow.tableCellPlan? schema) rows plans planned
    have cellLength := CoreOverflow.resolvePlans_cells_length resolvedResult
    have countEqual : resolved.cells.length = rows.length := by omega
    have decoded := decodePackedRowCellsFrom_resolvePlans schema source
      (source.pageCount + 1) rows plans next resolved valid planned resolvedResult
      nextPositive pageBound fuelBound reads []
    simp only [List.append_nil] at decoded
    change decodeRowsFrom schema source body.bytes = some rows
    rw [bodyBytes]
    unfold decodeRowsFrom
    simp only [List.nil_append] at content
    rw [pointers, content, countEqual]
    simp only [if_pos rfl]
    rw [decoded]
    simp

structure IndexEntry where
  value : Core.Value
  rowid : Core.Integer
  deriving DecidableEq

def decodeIndexCellWithSuffix (input : List UInt8) :
    Option (IndexEntry × List UInt8) := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (payload, suffix) ← decodeSizedBytes payloadSize.val afterSize
  let (record, recordSuffix) ← decodePhysicalRecord payload.bytes
  if _consumed : recordSuffix = [] then
    match record.fields with
    | [valueField, rowidField] => do
        let value ← PhysicalCodec.decodeValueField valueField
        let rowidValue ← PhysicalCodec.decodeValueField rowidField
        match rowidValue with
        | .integer rowid => some (⟨value, rowid⟩, suffix)
        | _ => none
    | _ => none
  else none

def decodeIndexPayloadBytesFrom (source : PageSource) (fuel payloadSize : Nat)
    (input : List UInt8) : Option (List UInt8 × List UInt8) :=
  if _fits : payloadSize ≤ indexMaxLocal PhysicalCodec.usablePageSize then do
    let (payload, suffix) ← decodeSizedBytes payloadSize input
    some (payload.bytes, suffix)
  else
    decodeOverflowPayloadBytesFrom source fuel payloadSize
      (indexLocalPayloadSize PhysicalCodec.usablePageSize payloadSize) input

theorem decodeIndexPayloadBytesFrom_overflow (source : PageSource)
    (payload suffix : List UInt8)
    (overflows : indexMaxLocal PhysicalCodec.usablePageSize < payload.length)
    (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      (payload.drop (indexLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length)) < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount
        (payload.drop (indexLocalPayloadSize PhysicalCodec.usablePageSize
          payload.length)))
      (payload.drop (indexLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length))) :
    decodeIndexPayloadBytesFrom source
        (CoreOverflow.overflowPageCount
          (payload.drop (indexLocalPayloadSize PhysicalCodec.usablePageSize
            payload.length)) + 1)
        payload.length
        (payload.take (indexLocalPayloadSize PhysicalCodec.usablePageSize
          payload.length) ++ first.encode ++ suffix) =
      some (payload, suffix) := by
  let localSize := indexLocalPayloadSize PhysicalCodec.usablePageSize
    payload.length
  have localLe : localSize ≤ payload.length :=
    indexLocalPayloadSize_le_payload PhysicalCodec.usablePageSize payload.length
  unfold decodeIndexPayloadBytesFrom
  rw [dif_neg (Nat.not_le_of_lt overflows)]
  exact decodeOverflowPayloadBytesFrom_generated source payload suffix localSize
    localLe first (by simpa [localSize] using bounded)
    (by simpa [localSize] using reads)

theorem decodeIndexPayloadBytesFrom_overflow_fuel (source : PageSource)
    (fuel : Nat) (payload suffix : List UInt8)
    (overflows : indexMaxLocal PhysicalCodec.usablePageSize < payload.length)
    (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      (payload.drop (indexLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length)) < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount
        (payload.drop (indexLocalPayloadSize PhysicalCodec.usablePageSize
          payload.length)))
      (payload.drop (indexLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length)))
    (fuelEnough : CoreOverflow.overflowPageCount
      (payload.drop (indexLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length)) < fuel) :
    decodeIndexPayloadBytesFrom source fuel payload.length
      (payload.take (indexLocalPayloadSize PhysicalCodec.usablePageSize
        payload.length) ++ first.encode ++ suffix) =
      some (payload, suffix) := by
  let localSize := indexLocalPayloadSize PhysicalCodec.usablePageSize
    payload.length
  have localLe : localSize ≤ payload.length :=
    indexLocalPayloadSize_le_payload PhysicalCodec.usablePageSize payload.length
  unfold decodeIndexPayloadBytesFrom
  rw [dif_neg (Nat.not_le_of_lt overflows)]
  exact decodeOverflowPayloadBytesFrom_generated_fuel source fuel payload suffix
    localSize localLe first (by simpa [localSize] using bounded)
    (by simpa [localSize] using reads)
    (by simpa [localSize] using fuelEnough)

def decodeIndexCellWithSuffixFrom (source : PageSource) (fuel : Nat)
    (input : List UInt8) : Option (IndexEntry × List UInt8) := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (payload, cellSuffix) ← decodeIndexPayloadBytesFrom source fuel
    payloadSize.val afterSize
  let (record, recordSuffix) ← decodePhysicalRecord payload
  if _consumed : recordSuffix = [] then
    match record.fields with
    | [valueField, rowidField] => do
        let value ← PhysicalCodec.decodeValueField valueField
        let rowidValue ← PhysicalCodec.decodeValueField rowidField
        match rowidValue with
        | .integer rowid => some (⟨value, rowid⟩, cellSuffix)
        | _ => none
    | _ => none
  else none

def decodePackedIndexCellsFrom (source : PageSource) (fuel : Nat) :
    Nat → List UInt8 → Option (List IndexEntry × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (entry, afterEntry) ←
        decodeIndexCellWithSuffixFrom source fuel input
      let (entries, suffix) ←
        decodePackedIndexCellsFrom source fuel count afterEntry
      some (entry :: entries, suffix)

def decodeIndexCellFrom (source : PageSource) (fuel : Nat)
    (input : List UInt8) : Option IndexEntry := do
  let (payloadSize, afterSize) ← decodeVarint input
  let (payload, _) ← decodeIndexPayloadBytesFrom source fuel
    payloadSize.val afterSize
  let (record, suffix) ← decodePhysicalRecord payload
  if _consumed : suffix = [] then
    match record.fields with
    | [valueField, rowidField] => do
        let value ← PhysicalCodec.decodeValueField valueField
        let rowidValue ← PhysicalCodec.decodeValueField rowidField
        match rowidValue with
        | .integer rowid => some ⟨value, rowid⟩
        | _ => none
    | _ => none
  else none

theorem decodeIndexCell_indexCell {index : Core.Index} {row : Core.Row}
    {cell : List UInt8} (built : CoreFile.indexCell? index row = some cell)
    (suffix : List UInt8) :
    decodeIndexCellWithSuffix (cell ++ suffix) =
      some (⟨row.value index.column, row.rowid⟩, suffix) := by
  unfold CoreFile.indexCell? at built
  cases recordResult : CoreFile.indexRecord? index row with
  | none => simp [recordResult] at built
  | some record =>
    simp only [recordResult, Option.bind_eq_bind, Option.bind] at built
    split at built
    next payloadBound =>
      injection built with equal
      subst cell
      unfold decodeIndexCellWithSuffix
      simp only [List.append_assoc]
      rw [decodeVarint_encode]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [decodeSizedBytes_append
        (⟨record.encode, rfl⟩ : SizedBytes record.encode.length) suffix]
      simp only
      have recordDecoded := decodePhysicalRecord_encode record []
      simp only [List.append_nil] at recordDecoded
      rw [recordDecoded]
      simp only [dif_pos True.intro]
      have fields : record.fields = [
          (row.value index.column).recordField,
          (PhysicalCodec.Value.integer row.rowid).recordField] := by
        unfold CoreFile.indexRecord? CoreFile.physicalRecord? at recordResult
        split at recordResult
        next headerBound =>
          exact congrArg PhysicalRecord.fields
            (Option.some.inj recordResult.symm)
        next headerTooLarge => contradiction
      rw [fields]
      simp only
      rw [PhysicalCodec.decodeValueField_recordField,
        PhysicalCodec.decodeValueField_recordField]
    next payloadTooLarge => contradiction

theorem decodeIndexCellWithSuffixFrom_indexPlan_inline {index : Core.Index}
    {row : Core.Row} {record : PhysicalRecord}
    {plan : CoreOverflow.CellPlan} {cell : List UInt8}
    (recordResult : CoreFile.indexRecord? index row = some record)
    (planned : CoreOverflow.indexCellPlan? index row = some plan)
    (inline : record.encode.length ≤
      indexMaxLocal PhysicalCodec.usablePageSize)
    (source : PageSource) (fuel : Nat) (firstOverflow : Option Nat)
    (cellBuilt : plan.cellBytes? firstOverflow = some cell)
    (suffix : List UInt8) :
    decodeIndexCellWithSuffixFrom source fuel (cell ++ suffix) =
      some (⟨row.value index.column, row.rowid⟩, suffix) := by
  unfold CoreOverflow.indexCellPlan? at planned
  rw [recordResult] at planned
  simp only [Option.bind_eq_bind, Option.bind] at planned
  split at planned
  next payloadBound =>
    injection planned with planEqual
    subst plan
    unfold CoreOverflow.CellPlan.cellBytes? at cellBuilt
    simp only [CoreOverflow.maxLocal] at cellBuilt
    rw [dif_pos inline] at cellBuilt
    injection cellBuilt with cellEqual
    subst cell
    unfold decodeIndexCellWithSuffixFrom
    simp only [List.append_assoc]
    rw [decodeVarint_encode]
    simp only [Option.bind_eq_bind, Option.bind]
    unfold decodeIndexPayloadBytesFrom
    rw [dif_pos inline]
    let payload : SizedBytes record.encode.length := ⟨record.encode, rfl⟩
    rw [decodeSizedBytes_append payload suffix]
    simp only [Option.bind_eq_bind, Option.bind]
    have recordDecoded := decodePhysicalRecord_encode record []
    simp only [List.append_nil] at recordDecoded
    rw [recordDecoded]
    simp only [dif_pos True.intro]
    have fields : record.fields = [
        (row.value index.column).recordField,
        (PhysicalCodec.Value.integer row.rowid).recordField] := by
      unfold CoreFile.indexRecord? CoreFile.physicalRecord? at recordResult
      split at recordResult
      next headerBound =>
        exact congrArg PhysicalRecord.fields
          (Option.some.inj recordResult.symm)
      next headerTooLarge => contradiction
    rw [fields]
    simp only
    rw [PhysicalCodec.decodeValueField_recordField,
      PhysicalCodec.decodeValueField_recordField]
  next payloadTooLarge => contradiction

theorem decodeIndexCellWithSuffixFrom_indexPlan_overflow {index : Core.Index}
    {row : Core.Row} {record : PhysicalRecord}
    {plan : CoreOverflow.CellPlan} {cell : List UInt8}
    (recordResult : CoreFile.indexRecord? index row = some record)
    (planned : CoreOverflow.indexCellPlan? index row = some plan)
    (overflows : indexMaxLocal PhysicalCodec.usablePageSize <
      record.encode.length)
    (source : PageSource) (fuel : Nat) (first : PageNumber)
    (bounded : first.value.val + CoreOverflow.overflowPageCount
      plan.overflowBytes < 2 ^ 32)
    (reads : ReadsGeneratedOverflow source first.value.val
      (CoreOverflow.overflowPageCount plan.overflowBytes) plan.overflowBytes)
    (fuelEnough : CoreOverflow.overflowPageCount plan.overflowBytes < fuel)
    (cellBuilt : plan.cellBytes? (some first.value.val) = some cell)
    (suffix : List UInt8) :
    decodeIndexCellWithSuffixFrom source fuel (cell ++ suffix) =
      some (⟨row.value index.column, row.rowid⟩, suffix) := by
  unfold CoreOverflow.indexCellPlan? at planned
  rw [recordResult] at planned
  simp only [Option.bind_eq_bind, Option.bind] at planned
  split at planned
  next payloadBound =>
    injection planned with planEqual
    subst plan
    unfold CoreOverflow.CellPlan.cellBytes? at cellBuilt
    simp only [CoreOverflow.maxLocal, CoreOverflow.CellPlan.localBytes,
      CoreOverflow.localSize] at cellBuilt
    rw [dif_neg (Nat.not_le_of_lt overflows)] at cellBuilt
    simp only [Option.bind_eq_bind, Option.bind] at cellBuilt
    rw [CoreOverflow.boundedPageNumber?_page first] at cellBuilt
    injection cellBuilt with cellEqual
    subst cell
    unfold decodeIndexCellWithSuffixFrom
    simp only [List.append_assoc]
    rw [decodeVarint_encode]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [← List.append_assoc
      (record.encode.take (indexLocalPayloadSize PhysicalCodec.usablePageSize
        record.encode.length)) first.encode suffix]
    rw [decodeIndexPayloadBytesFrom_overflow_fuel source fuel record.encode
      suffix overflows first
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using bounded)
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using reads)
      (by simpa [CoreOverflow.CellPlan.overflowBytes,
        CoreOverflow.localSize] using fuelEnough)]
    simp only [Option.bind_eq_bind, Option.bind]
    have recordDecoded := decodePhysicalRecord_encode record []
    simp only [List.append_nil] at recordDecoded
    rw [recordDecoded]
    simp only [dif_pos True.intro]
    have fields : record.fields = [
        (row.value index.column).recordField,
        (PhysicalCodec.Value.integer row.rowid).recordField] := by
      unfold CoreFile.indexRecord? CoreFile.physicalRecord? at recordResult
      split at recordResult
      next headerBound =>
        exact congrArg PhysicalRecord.fields
          (Option.some.inj recordResult.symm)
      next headerTooLarge => contradiction
    rw [fields]
    simp only
    rw [PhysicalCodec.decodeValueField_recordField,
      PhysicalCodec.decodeValueField_recordField]
  next payloadTooLarge => contradiction

theorem decodePackedIndexCellsFrom_resolvePlans (index : Core.Index)
    (source : PageSource) (fuel : Nat) :
    ∀ (rows : List Core.Row) (plans : List CoreOverflow.CellPlan)
      (next : Nat) (resolved : CoreOverflow.Resolved),
      rows.mapM (CoreOverflow.indexCellPlan? index) = some plans →
      CoreOverflow.resolvePlans next plans = some resolved →
      0 < next →
      next + resolved.pages.length < 2 ^ 32 →
      resolved.pages.length < fuel →
      ReadsPagesFrom source next resolved.pages →
      ∀ suffix,
      decodePackedIndexCellsFrom source fuel rows.length
        (PhysicalCodec.cellBytes resolved.cells ++ suffix) =
          some (rows.map fun row =>
            ⟨row.value index.column, row.rowid⟩, suffix)
  | [], plans, next, resolved, planned, resolvedResult, _, _, _, _, suffix => by
      simp only [List.mapM_nil, pure, Pure.pure] at planned
      injection planned with plansEqual
      subst plans
      simp only [CoreOverflow.resolvePlans, Option.some.injEq] at resolvedResult
      subst resolved
      rfl
  | row :: rows, plans, next, resolved, planned, resolvedResult,
      nextPositive, pageBound, fuelBound, reads, suffix => by
      cases planResult : CoreOverflow.indexCellPlan? index row with
      | none => simp [List.mapM_cons, planResult] at planned
      | some plan =>
        cases tailPlanResult : rows.mapM (CoreOverflow.indexCellPlan? index) with
        | none => simp [List.mapM_cons, planResult, tailPlanResult] at planned
        | some tailPlans =>
          simp only [List.mapM_cons, planResult, tailPlanResult,
            Option.bind_eq_bind, Option.bind] at planned
          injection planned with plansEqual
          subst plans
          simp only [CoreOverflow.resolvePlans, Option.bind_eq_bind,
            Option.bind] at resolvedResult
          cases cellResult : plan.cellBytes?
              (if CoreOverflow.overflowPageCount plan.overflowBytes = 0 then
                none else some next) with
          | none => simp [cellResult] at resolvedResult
          | some cell =>
            simp only [cellResult] at resolvedResult
            cases pagesResult : CoreOverflow.makeOverflowPages? next
                plan.overflowBytes with
            | none => simp [pagesResult] at resolvedResult
            | some pages =>
              simp only [pagesResult] at resolvedResult
              cases restResult : CoreOverflow.resolvePlans
                  (next + pages.length) tailPlans with
              | none => simp [restResult] at resolvedResult
              | some rest =>
                simp only [restResult, Option.some.injEq] at resolvedResult
                subst resolved
                have headReads : ReadsPagesFrom source next pages :=
                  ReadsPagesFrom.left reads
                have tailReads : ReadsPagesFrom source (next + pages.length)
                    rest.pages := ReadsPagesFrom.right reads
                have pagesLength :=
                  CoreOverflow.makeOverflowPages?_length pagesResult
                have tailDecoded := decodePackedIndexCellsFrom_resolvePlans
                  index source fuel rows tailPlans (next + pages.length) rest
                  tailPlanResult restResult (by omega)
                  (by simp only [List.length_append] at pageBound; omega)
                  (by simp only [List.length_append] at fuelBound; omega)
                  tailReads suffix
                let cellSuffix := PhysicalCodec.cellBytes rest.cells ++ suffix
                cases recordResult : CoreFile.indexRecord? index row with
                | none =>
                  unfold CoreOverflow.indexCellPlan? at planResult
                  simp [recordResult] at planResult
                | some record =>
                  have plannedHead := planResult
                  by_cases inline : record.encode.length ≤
                      indexMaxLocal PhysicalCodec.usablePageSize
                  · have headDecoded : decodeIndexCellWithSuffixFrom source fuel
                        (cell ++ cellSuffix) =
                          some (⟨row.value index.column, row.rowid⟩,
                            cellSuffix) :=
                      decodeIndexCellWithSuffixFrom_indexPlan_inline recordResult
                        plannedHead inline source fuel
                        (if CoreOverflow.overflowPageCount plan.overflowBytes = 0
                          then none else some next) cellResult cellSuffix
                    change decodePackedIndexCellsFrom source fuel
                      (rows.length + 1)
                      (cell ++ PhysicalCodec.cellBytes rest.cells ++ suffix) =
                        some (⟨row.value index.column, row.rowid⟩ ::
                          rows.map (fun candidate =>
                            ⟨candidate.value index.column, candidate.rowid⟩),
                          suffix)
                    rw [show cell ++ PhysicalCodec.cellBytes rest.cells ++ suffix =
                        cell ++ cellSuffix by simp [cellSuffix,
                          List.append_assoc]]
                    unfold decodePackedIndexCellsFrom
                    rw [headDecoded]
                    simp only [Option.bind_eq_bind, Option.bind, cellSuffix]
                    rw [tailDecoded]
                  · have overflows : indexMaxLocal
                        PhysicalCodec.usablePageSize < record.encode.length := by
                      omega
                    unfold CoreOverflow.indexCellPlan? at planResult
                    rw [recordResult] at planResult
                    simp only [Option.bind_eq_bind, Option.bind] at planResult
                    split at planResult
                    next payloadBound =>
                      injection planResult with planEqual
                      subst plan
                      have localLt : indexLocalPayloadSize
                          PhysicalCodec.usablePageSize record.encode.length <
                          record.encode.length :=
                        indexLocalPayloadSize_lt_payload_of_overflow
                          PhysicalCodec.usablePageSize record.encode.length
                          overflows
                      have overflowNonempty : record.encode.drop
                          (indexLocalPayloadSize PhysicalCodec.usablePageSize
                            record.encode.length) ≠ [] := by
                        apply List.ne_nil_of_length_pos
                        simp
                        omega
                      have countPositive : 0 < CoreOverflow.overflowPageCount
                          (record.encode.drop (indexLocalPayloadSize
                            PhysicalCodec.usablePageSize record.encode.length)) :=
                        CoreOverflow.overflowPageCount_positive overflowNonempty
                      let first : PageNumber :=
                        ⟨⟨next, by
                          simp only [List.length_append] at pageBound
                          omega⟩, nextPositive⟩
                      have cellBuilt :
                          ({
                            kind := CoreOverflow.PayloadKind.index
                            cellPrefix := encodeVarint
                              ⟨record.encode.length, by simpa using payloadBound⟩
                            payload := record.encode
                          } : CoreOverflow.CellPlan).cellBytes?
                            (some first.value.val) = some cell := by
                        simpa [CoreOverflow.CellPlan.overflowBytes,
                          CoreOverflow.localSize, first,
                          Nat.ne_of_gt countPositive] using cellResult
                      have generated := readsGeneratedOverflow_of_makeOverflowPages
                        source next
                        (record.encode.drop (indexLocalPayloadSize
                          PhysicalCodec.usablePageSize record.encode.length))
                        pages pagesResult headReads
                      have headDecoded : decodeIndexCellWithSuffixFrom source fuel
                          (cell ++ cellSuffix) =
                            some (⟨row.value index.column, row.rowid⟩,
                              cellSuffix) :=
                        decodeIndexCellWithSuffixFrom_indexPlan_overflow
                          recordResult plannedHead overflows source fuel first
                          (by
                            simp only [List.length_append] at pageBound
                            simpa [CoreOverflow.CellPlan.overflowBytes,
                              CoreOverflow.localSize, first, pagesLength] using
                              (show next + pages.length < 2 ^ 32 by omega))
                          (by simpa [CoreOverflow.CellPlan.overflowBytes,
                            CoreOverflow.localSize, first] using generated)
                          (by
                            simp only [List.length_append] at fuelBound
                            simpa [CoreOverflow.CellPlan.overflowBytes,
                              CoreOverflow.localSize, pagesLength] using
                              (show pages.length < fuel by omega))
                          cellBuilt cellSuffix
                      change decodePackedIndexCellsFrom source fuel
                        (rows.length + 1)
                        (cell ++ PhysicalCodec.cellBytes rest.cells ++ suffix) =
                          some (⟨row.value index.column, row.rowid⟩ ::
                            rows.map (fun candidate =>
                              ⟨candidate.value index.column, candidate.rowid⟩),
                            suffix)
                      rw [show cell ++ PhysicalCodec.cellBytes rest.cells ++
                          suffix = cell ++ cellSuffix by
                            simp [cellSuffix, List.append_assoc]]
                      unfold decodePackedIndexCellsFrom
                      rw [headDecoded]
                      simp only [Option.bind_eq_bind, Option.bind, cellSuffix]
                      rw [tailDecoded]
                    next payloadTooLarge => contradiction

/-- Each physical index cell decodes to the corresponding logical entry for
every following byte suffix.  This stronger, compositional relation is what
lets an index plan promote records into interior nodes without losing or
duplicating them. -/
inductive IndexCellsDecode (source : PageSource) (fuel : Nat) :
    List (List UInt8) → List IndexEntry → Prop where
  | nil : IndexCellsDecode source fuel [] []
  | cons {cell : List UInt8} {entry : IndexEntry}
      {cells : List (List UInt8)} {entries : List IndexEntry}
      (head : ∀ suffix,
        decodeIndexCellWithSuffixFrom source fuel (cell ++ suffix) =
          some (entry, suffix))
      (tail : IndexCellsDecode source fuel cells entries) :
      IndexCellsDecode source fuel (cell :: cells) (entry :: entries)

theorem IndexCellsDecode.length_eq {source : PageSource} {fuel : Nat}
    {cells : List (List UInt8)} {entries : List IndexEntry}
    (decoded : IndexCellsDecode source fuel cells entries) :
    cells.length = entries.length := by
  induction decoded with
  | nil => rfl
  | cons _ _ induction => simp [induction]

theorem IndexCellsDecode.splitAt {source : PageSource} {fuel : Nat}
    {cells : List (List UInt8)} {entries : List IndexEntry}
    (decoded : IndexCellsDecode source fuel cells entries) (count : Nat) :
    ∃ leftEntries rightEntries,
      entries = leftEntries ++ rightEntries ∧
      IndexCellsDecode source fuel (cells.take count) leftEntries ∧
      IndexCellsDecode source fuel (cells.drop count) rightEntries := by
  induction count generalizing cells entries with
  | zero =>
      exact ⟨[], entries, by simp, .nil, by simpa using decoded⟩
  | succ count induction =>
      cases decoded with
      | nil => exact ⟨[], [], by simp, .nil, .nil⟩
      | cons head tail =>
          rcases induction tail with
            ⟨leftEntries, rightEntries, entriesEqual, leftDecoded,
              rightDecoded⟩
          exact ⟨_ :: leftEntries, rightEntries, by simp [entriesEqual],
            .cons head leftDecoded, rightDecoded⟩

theorem decodePackedIndexCellsFrom_of_relation {source : PageSource}
    {fuel : Nat} {cells : List (List UInt8)} {entries : List IndexEntry}
    (decoded : IndexCellsDecode source fuel cells entries)
    (suffix : List UInt8) :
    decodePackedIndexCellsFrom source fuel cells.length
        (PhysicalCodec.cellBytes cells ++ suffix) = some (entries, suffix) := by
  induction decoded with
  | nil => rfl
  | @cons cell entry cells entries head tail induction =>
      simp only [PhysicalCodec.cellBytes, List.flatten_cons,
        List.length_cons, List.append_assoc]
      unfold decodePackedIndexCellsFrom
      rw [head (cells.flatten ++ suffix)]
      simp only [Option.bind_eq_bind, Option.bind]
      rw [show decodePackedIndexCellsFrom source fuel cells.length
          (cells.flatten ++ suffix) = some (entries, suffix) by
        simpa only [PhysicalCodec.cellBytes] using induction]

theorem indexCellsDecode_resolvePlans (index : Core.Index)
    (source : PageSource) (fuel : Nat) :
    ∀ (rows : List Core.Row) (plans : List CoreOverflow.CellPlan)
      (next : Nat) (resolved : CoreOverflow.Resolved),
      rows.mapM (CoreOverflow.indexCellPlan? index) = some plans →
      CoreOverflow.resolvePlans next plans = some resolved →
      0 < next →
      next + resolved.pages.length < 2 ^ 32 →
      resolved.pages.length < fuel →
      ReadsPagesFrom source next resolved.pages →
      IndexCellsDecode source fuel resolved.cells
        (rows.map fun row => ⟨row.value index.column, row.rowid⟩)
  | [], plans, next, resolved, planned, resolvedResult, _, _, _, _ => by
      simp only [List.mapM_nil, pure, Pure.pure] at planned
      injection planned with plansEqual
      subst plans
      simp only [CoreOverflow.resolvePlans, Option.some.injEq] at resolvedResult
      subst resolved
      exact .nil
  | row :: rows, plans, next, resolved, planned, resolvedResult,
      nextPositive, pageBound, fuelBound, reads => by
      cases planResult : CoreOverflow.indexCellPlan? index row with
      | none => simp [List.mapM_cons, planResult] at planned
      | some plan =>
        cases tailPlanResult : rows.mapM (CoreOverflow.indexCellPlan? index) with
        | none => simp [List.mapM_cons, planResult, tailPlanResult] at planned
        | some tailPlans =>
          simp only [List.mapM_cons, planResult, tailPlanResult,
            Option.bind_eq_bind, Option.bind] at planned
          injection planned with plansEqual
          subst plans
          simp only [CoreOverflow.resolvePlans, Option.bind_eq_bind,
            Option.bind] at resolvedResult
          cases cellResult : plan.cellBytes?
              (if CoreOverflow.overflowPageCount plan.overflowBytes = 0 then
                none else some next) with
          | none => simp [cellResult] at resolvedResult
          | some cell =>
            simp only [cellResult] at resolvedResult
            cases pagesResult : CoreOverflow.makeOverflowPages? next
                plan.overflowBytes with
            | none => simp [pagesResult] at resolvedResult
            | some pages =>
              simp only [pagesResult] at resolvedResult
              cases restResult : CoreOverflow.resolvePlans
                  (next + pages.length) tailPlans with
              | none => simp [restResult] at resolvedResult
              | some rest =>
                simp only [restResult, Option.some.injEq] at resolvedResult
                subst resolved
                have headReads : ReadsPagesFrom source next pages :=
                  ReadsPagesFrom.left reads
                have tailReads : ReadsPagesFrom source (next + pages.length)
                    rest.pages := ReadsPagesFrom.right reads
                have pagesLength :=
                  CoreOverflow.makeOverflowPages?_length pagesResult
                have tailDecoded := indexCellsDecode_resolvePlans index source
                  fuel rows tailPlans (next + pages.length) rest tailPlanResult
                  restResult (by omega)
                  (by simp only [List.length_append] at pageBound; omega)
                  (by simp only [List.length_append] at fuelBound; omega)
                  tailReads
                cases recordResult : CoreFile.indexRecord? index row with
                | none =>
                  unfold CoreOverflow.indexCellPlan? at planResult
                  simp [recordResult] at planResult
                | some record =>
                  have plannedHead := planResult
                  by_cases inline : record.encode.length ≤
                      indexMaxLocal PhysicalCodec.usablePageSize
                  · have headDecoded : ∀ suffix,
                        decodeIndexCellWithSuffixFrom source fuel
                            (cell ++ suffix) =
                          some (⟨row.value index.column, row.rowid⟩, suffix) :=
                      fun suffix =>
                        decodeIndexCellWithSuffixFrom_indexPlan_inline
                          recordResult plannedHead inline source fuel
                          (if CoreOverflow.overflowPageCount plan.overflowBytes =
                              0 then none else some next) cellResult suffix
                    exact .cons headDecoded tailDecoded
                  · have overflows : indexMaxLocal
                        PhysicalCodec.usablePageSize < record.encode.length := by
                      omega
                    unfold CoreOverflow.indexCellPlan? at planResult
                    rw [recordResult] at planResult
                    simp only [Option.bind_eq_bind, Option.bind] at planResult
                    split at planResult
                    next payloadBound =>
                      injection planResult with planEqual
                      subst plan
                      have localLt : indexLocalPayloadSize
                          PhysicalCodec.usablePageSize record.encode.length <
                          record.encode.length :=
                        indexLocalPayloadSize_lt_payload_of_overflow
                          PhysicalCodec.usablePageSize record.encode.length
                          overflows
                      have overflowNonempty : record.encode.drop
                          (indexLocalPayloadSize PhysicalCodec.usablePageSize
                            record.encode.length) ≠ [] := by
                        apply List.ne_nil_of_length_pos
                        simp
                        omega
                      have countPositive : 0 < CoreOverflow.overflowPageCount
                          (record.encode.drop (indexLocalPayloadSize
                            PhysicalCodec.usablePageSize record.encode.length)) :=
                        CoreOverflow.overflowPageCount_positive overflowNonempty
                      let first : PageNumber :=
                        ⟨⟨next, by
                          simp only [List.length_append] at pageBound
                          omega⟩, nextPositive⟩
                      have cellBuilt :
                          ({
                            kind := CoreOverflow.PayloadKind.index
                            cellPrefix := encodeVarint
                              ⟨record.encode.length, by simpa using payloadBound⟩
                            payload := record.encode
                          } : CoreOverflow.CellPlan).cellBytes?
                            (some first.value.val) = some cell := by
                        simpa [CoreOverflow.CellPlan.overflowBytes,
                          CoreOverflow.localSize, first,
                          Nat.ne_of_gt countPositive] using cellResult
                      have generated := readsGeneratedOverflow_of_makeOverflowPages
                        source next
                        (record.encode.drop (indexLocalPayloadSize
                          PhysicalCodec.usablePageSize record.encode.length))
                        pages pagesResult headReads
                      have headDecoded : ∀ suffix,
                          decodeIndexCellWithSuffixFrom source fuel
                              (cell ++ suffix) =
                            some (⟨row.value index.column, row.rowid⟩,
                              suffix) := fun suffix =>
                        decodeIndexCellWithSuffixFrom_indexPlan_overflow
                          recordResult plannedHead overflows source fuel first
                          (by
                            simp only [List.length_append] at pageBound
                            simpa [CoreOverflow.CellPlan.overflowBytes,
                              CoreOverflow.localSize, first, pagesLength] using
                              (show next + pages.length < 2 ^ 32 by omega))
                          (by simpa [CoreOverflow.CellPlan.overflowBytes,
                            CoreOverflow.localSize, first] using generated)
                          (by
                            simp only [List.length_append] at fuelBound
                            simpa [CoreOverflow.CellPlan.overflowBytes,
                              CoreOverflow.localSize, pagesLength] using
                              (show pages.length < fuel by omega))
                          cellBuilt suffix
                      exact .cons headDecoded tailDecoded
                    next payloadTooLarge => contradiction

/-- A structural refinement certificate for the physical index topology.
Interior entries are represented by their own cell proofs between the child
certificates, so every promoted record occurs exactly once. -/
inductive IndexPlanDecodes (source : PageSource) (fuel : Nat) :
    RecursivePageBTree.IndexPlan → List IndexEntry → Prop where
  | leaf {cells entries} (decoded : IndexCellsDecode source fuel cells entries) :
      IndexPlanDecodes source fuel (.leaf cells) entries
  | branch2 {left separator right leftEntries separatorEntry rightEntries}
      (leftDecoded : IndexPlanDecodes source fuel left leftEntries)
      (separatorDecoded : ∀ suffix,
        decodeIndexCellWithSuffixFrom source fuel (separator ++ suffix) =
          some (separatorEntry, suffix))
      (rightDecoded : IndexPlanDecodes source fuel right rightEntries) :
      IndexPlanDecodes source fuel (.branch2 left separator right)
        (leftEntries ++ separatorEntry :: rightEntries)
  | branch3 {left firstSeparator middle secondSeparator right leftEntries
      firstEntry middleEntries secondEntry rightEntries}
      (leftDecoded : IndexPlanDecodes source fuel left leftEntries)
      (firstDecoded : ∀ suffix,
        decodeIndexCellWithSuffixFrom source fuel (firstSeparator ++ suffix) =
          some (firstEntry, suffix))
      (middleDecoded : IndexPlanDecodes source fuel middle middleEntries)
      (secondDecoded : ∀ suffix,
        decodeIndexCellWithSuffixFrom source fuel (secondSeparator ++ suffix) =
          some (secondEntry, suffix))
      (rightDecoded : IndexPlanDecodes source fuel right rightEntries) :
      IndexPlanDecodes source fuel
        (.branch3 left firstSeparator middle secondSeparator right)
        (leftEntries ++ firstEntry :: middleEntries ++
          secondEntry :: rightEntries)

theorem IndexPlanDecodes.of_cells {source : PageSource} {fuel : Nat} :
    ∀ (plan : RecursivePageBTree.IndexPlan) (entries : List IndexEntry),
      IndexCellsDecode source fuel plan.toCells entries →
      IndexPlanDecodes source fuel plan entries
  | .leaf cells, entries, decoded => .leaf decoded
  | .branch2 left separator right, entries, decoded => by
      rcases decoded.splitAt left.toCells.length with
        ⟨leftEntries, suffixEntries, entriesEqual, leftDecoded,
          suffixDecoded⟩
      have leftExact : IndexCellsDecode source fuel left.toCells leftEntries := by
        simpa [RecursivePageBTree.IndexPlan.toCells] using leftDecoded
      have suffixExact : IndexCellsDecode source fuel
          (separator :: right.toCells) suffixEntries := by
        simpa [RecursivePageBTree.IndexPlan.toCells] using suffixDecoded
      cases suffixExact with
      | cons separatorDecoded rightDecoded =>
          rw [entriesEqual]
          exact .branch2 (of_cells left leftEntries leftExact)
            separatorDecoded (of_cells right _ rightDecoded)
  | .branch3 left firstSeparator middle secondSeparator right, entries,
      decoded => by
      rcases decoded.splitAt left.toCells.length with
        ⟨leftEntries, afterLeftEntries, entriesEqual, leftDecoded,
          afterLeftDecoded⟩
      have leftExact : IndexCellsDecode source fuel left.toCells leftEntries := by
        simpa [RecursivePageBTree.IndexPlan.toCells] using leftDecoded
      have afterLeftExact : IndexCellsDecode source fuel
          (firstSeparator :: middle.toCells ++ secondSeparator :: right.toCells)
          afterLeftEntries := by
        simpa [RecursivePageBTree.IndexPlan.toCells, List.append_assoc] using
          afterLeftDecoded
      cases afterLeftExact with
      | cons firstDecoded afterFirstDecoded =>
          rcases afterFirstDecoded.splitAt middle.toCells.length with
            ⟨middleEntries, afterMiddleEntries, afterFirstEqual, middleDecoded,
              afterMiddleDecoded⟩
          have middleExact : IndexCellsDecode source fuel middle.toCells
              middleEntries := by
            simpa using middleDecoded
          have afterMiddleExact : IndexCellsDecode source fuel
              (secondSeparator :: right.toCells) afterMiddleEntries := by
            simpa using afterMiddleDecoded
          cases afterMiddleExact with
          | cons secondDecoded rightDecoded =>
              rw [entriesEqual, afterFirstEqual]
              simpa [List.append_assoc] using
                (IndexPlanDecodes.branch3
                  (of_cells left leftEntries leftExact) firstDecoded
                  (of_cells middle middleEntries middleExact) secondDecoded
                  (of_cells right _ rightDecoded))

def leafIndexOffsets? (page : List UInt8) : Option (List Nat) := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    let (header, afterHeader) ← decodeBTreePageHeader page
    match header with
    | .leafIndex common => do
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        if _bounded : offsets.all (fun offset => decide (offset < page.length)) then
          some offsets
        else none
    | _ => none
  else none

def leafIndexOffsetsFor? (pageSize : Nat) (page : List UInt8) :
    Option (List Nat) := do
  if _pageLength : page.length = pageSize then
    let (header, afterHeader) ← decodeBTreePageHeader page
    match header with
    | .leafIndex common => do
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        if _bounded : offsets.all (fun offset => decide (offset < page.length)) then
          some offsets
        else none
    | _ => none
  else none

def canonicalIndexLeafContent? (page : List UInt8) :
    Option (Nat × List UInt8) := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    match page with
    | 10 :: 0 :: 0 :: afterFreeblock => do
        let (cellCount, afterCount) ← decodeUnsignedFixed 2 afterFreeblock
        let (contentStart, afterContentStart) ←
          decodeUnsignedFixed 2 afterCount
        match afterContentStart with
        | 0 :: _ => some (cellCount, page.drop contentStart)
        | _ => none
    | _ => none
  else none

def canonicalIndexLeafPointersBeginAtContent (page : List UInt8) : Bool :=
  match page with
  | 10 :: _ :: _ :: countHigh :: countLow :: contentHigh :: contentLow :: _ ::
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

def canonicalIndexInteriorContent? (page : List UInt8) :
    Option (Nat × Nat × List UInt8) := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    match page with
    | 2 :: 0 :: 0 :: afterFreeblock => do
        let (cellCount, afterCount) ← decodeUnsignedFixed 2 afterFreeblock
        let (contentStart, afterContentStart) ←
          decodeUnsignedFixed 2 afterCount
        match afterContentStart with
        | 0 :: afterFragmented => do
            let (rightmost, _) ← decodeUnsignedFixed 4 afterFragmented
            some (cellCount, rightmost, page.drop contentStart)
        | _ => none
    | _ => none
  else none

def canonicalIndexInteriorPointersBeginAtContent (page : List UInt8) : Bool :=
  match page with
  | 2 :: _ :: _ :: countHigh :: countLow :: contentHigh :: contentLow :: _ ::
      _ :: _ :: _ :: _ :: afterHeader =>
      let cellCount := decodeU16 countHigh countLow
      let contentStart := decodeU16 contentHigh contentLow
      if cellCount = 0 then true
      else match afterHeader with
        | firstHigh :: firstLow :: remaining =>
            decide (decodeU16 firstHigh firstLow = contentStart) &&
              ascendingCellPointers (cellCount - 1) contentStart remaining
        | _ => false
  | _ => false

theorem canonicalIndexLeafContent_leafPageBody
    (cells : List (List UInt8)) (fits : PhysicalCodec.PageFit 0 cells) :
    canonicalIndexLeafContent?
      (CoreFile.replaceFirst 10 (PhysicalCodec.leafPageBody 0 cells)) =
        some (cells.length, PhysicalCodec.cellBytes cells) := by
  let contentStart := PhysicalCodec.pageSize -
    (PhysicalCodec.cellBytes cells).length
  let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
    List.replicate
      (contentStart -
        (PhysicalCodec.leafHeader cells.length contentStart ++
          PhysicalCodec.leafPointers contentStart cells).length) 0 ++
    PhysicalCodec.cellBytes cells
  have bodyLayout : PhysicalCodec.leafPageBody 0 cells =
      13 :: 0 :: 0 ::
        (PhysicalCodec.encodeU16Nat cells.length ++
          PhysicalCodec.encodeU16Nat contentStart ++ 0 :: afterHeader) := by
    unfold PhysicalCodec.leafPageBody PhysicalCodec.leafHeader
    simp only [List.cons_append, List.nil_append]
    rfl
  have replacedLayout :
      CoreFile.replaceFirst 10 (PhysicalCodec.leafPageBody 0 cells) =
        10 :: 0 :: 0 ::
          (PhysicalCodec.encodeU16Nat cells.length ++
            PhysicalCodec.encodeU16Nat contentStart ++ 0 :: afterHeader) := by
    rw [bodyLayout]
    rfl
  have pageLength :
      (CoreFile.replaceFirst 10
        (PhysicalCodec.leafPageBody 0 cells)).length =
          PhysicalCodec.pageSize := by
    rw [CoreFile.replaceFirst_length,
      PhysicalCodec.leafPageBody_length 0 cells fits]
    simp
  have countBound : cells.length < 256 ^ 2 := by
    simpa using fits.cellCount_lt
  have contentBound : contentStart < 256 ^ 2 := by
    simpa [contentStart] using PhysicalCodec.contentStart_lt cells
  have dropped := PhysicalCodec.leafPageBody_drop_content cells fits
  have contentPositive : 0 < contentStart := by
    unfold PhysicalCodec.PageFit at fits
    dsimp only [contentStart]
    omega
  have replacedDrop :
      (CoreFile.replaceFirst 10 (PhysicalCodec.leafPageBody 0 cells)).drop
        contentStart = PhysicalCodec.cellBytes cells := by
    have dropped' :
        (13 :: 0 :: 0 ::
          (PhysicalCodec.encodeU16Nat cells.length ++
            PhysicalCodec.encodeU16Nat contentStart ++ 0 :: afterHeader)).drop
              contentStart = PhysicalCodec.cellBytes cells := by
      simpa [contentStart, bodyLayout] using dropped
    rw [bodyLayout]
    simp only [CoreFile.replaceFirst]
    cases contentShape : contentStart with
    | zero => omega
    | succ remaining =>
      simpa [contentShape] using dropped'
  rw [replacedLayout]
  unfold canonicalIndexLeafContent?
  rw [dif_pos (by
    rw [← replacedLayout]
    exact pageLength)]
  simp only
  unfold PhysicalCodec.encodeU16Nat
  simp only [List.append_assoc]
  rw [decodeUnsignedFixed_encode _ countBound]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeUnsignedFixed_encode _ contentBound]
  simpa [replacedLayout, PhysicalCodec.encodeU16Nat] using replacedDrop

theorem canonicalIndexLeafPointers_leafPageBody
    (cells : List (List UInt8)) (fits : PhysicalCodec.PageFit 0 cells) :
    canonicalIndexLeafPointersBeginAtContent
      (CoreFile.replaceFirst 10 (PhysicalCodec.leafPageBody 0 cells)) = true := by
  have countBound : cells.length < 65536 := fits.cellCount_lt
  have contentBound : PhysicalCodec.pageSize -
      (PhysicalCodec.cellBytes cells).length < 65536 :=
    PhysicalCodec.contentStart_lt cells
  cases cells with
  | nil =>
      simp [canonicalIndexLeafPointersBeginAtContent,
        PhysicalCodec.leafPageBody, PhysicalCodec.leafHeader,
        PhysicalCodec.leafPointers, PhysicalCodec.cellOffsetsFrom,
        PhysicalCodec.cellBytes, CoreFile.replaceFirst,
        PhysicalCodec.encodeU16Nat, FileFormat.encodeUnsignedFixed,
        FileFormat.decodeU16]
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
      simp [canonicalIndexLeafPointersBeginAtContent,
        PhysicalCodec.leafPageBody, PhysicalCodec.leafHeader,
        PhysicalCodec.leafPointers, PhysicalCodec.cellOffsetsFrom,
        PhysicalCodec.cellBytes, CoreFile.replaceFirst,
        PhysicalCodec.encodeU16Nat, FileFormat.encodeUnsignedFixed,
        FileFormat.decodeU16, Nat.mod_eq_of_lt countBound,
        Nat.mod_eq_of_lt contentBound, restOrdered, decodedCount, decodedContent]

set_option maxRecDepth 2048 in
theorem canonicalIndexInteriorContent_interiorPageBody
    (rightmost : U32Value) (cells : List (List UInt8))
    (fits : PhysicalTableBTree.InteriorPageFit cells) :
    canonicalIndexInteriorContent?
      (CoreFile.replaceFirst 2
        (PhysicalTableBTree.interiorPageBody rightmost cells)) =
      some (cells.length, rightmost.val, PhysicalCodec.cellBytes cells) := by
  let contentStart := PhysicalCodec.pageSize -
    (PhysicalCodec.cellBytes cells).length
  let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
    List.replicate
      (contentStart -
        (PhysicalTableBTree.interiorHeader cells.length contentStart rightmost ++
          PhysicalCodec.leafPointers contentStart cells).length) 0 ++
    PhysicalCodec.cellBytes cells
  have bodyLayout : PhysicalTableBTree.interiorPageBody rightmost cells =
      5 :: 0 :: 0 ::
        (PhysicalCodec.encodeU16Nat cells.length ++
          PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
            (FileFormat.encodeU32Bytes rightmost ++ afterHeader)) := by
    unfold PhysicalTableBTree.interiorPageBody
      PhysicalTableBTree.interiorHeader
    simp only [List.cons_append, List.nil_append]
    rfl
  have replacedLayout :
      CoreFile.replaceFirst 2
          (PhysicalTableBTree.interiorPageBody rightmost cells) =
        2 :: 0 :: 0 ::
          (PhysicalCodec.encodeU16Nat cells.length ++
            PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
              (FileFormat.encodeU32Bytes rightmost ++ afterHeader)) := by
    rw [bodyLayout]
    rfl
  have pageLength :
      (CoreFile.replaceFirst 2
        (PhysicalTableBTree.interiorPageBody rightmost cells)).length =
          PhysicalCodec.pageSize := by
    rw [CoreFile.replaceFirst_length,
      PhysicalTableBTree.interiorPageBody_length rightmost cells fits]
  have countBound : cells.length < 256 ^ 2 := by
    simpa using fits.cellCount_lt
  have contentBound : contentStart < 256 ^ 2 := by
    simpa [contentStart] using PhysicalCodec.contentStart_lt cells
  have dropped := PhysicalTableBTree.interiorPageBody_drop_content
    rightmost cells fits
  have contentPositive : 0 < contentStart := by
    unfold PhysicalTableBTree.InteriorPageFit at fits
    dsimp only [contentStart]
    omega
  have replacedDrop :
      (CoreFile.replaceFirst 2
        (PhysicalTableBTree.interiorPageBody rightmost cells)).drop
          contentStart = PhysicalCodec.cellBytes cells := by
    have dropped' :
        (5 :: 0 :: 0 ::
          (PhysicalCodec.encodeU16Nat cells.length ++
            PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
              (FileFormat.encodeU32Bytes rightmost ++ afterHeader))).drop
                contentStart = PhysicalCodec.cellBytes cells := by
      simpa [contentStart, bodyLayout] using dropped
    rw [bodyLayout]
    simp only [CoreFile.replaceFirst]
    cases contentShape : contentStart with
    | zero => omega
    | succ remaining => simpa [contentShape] using dropped'
  rw [replacedLayout]
  unfold canonicalIndexInteriorContent?
  rw [dif_pos (by rw [← replacedLayout]; exact pageLength)]
  simp only
  unfold PhysicalCodec.encodeU16Nat
  simp only [List.append_assoc]
  rw [decodeUnsignedFixed_encode _ countBound]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [decodeUnsignedFixed_encode _ contentBound]
  simp only
  have decodedRightmost : decodeUnsignedFixed 4
      (FileFormat.encodeU32Bytes rightmost ++ afterHeader) =
        some (rightmost.val, afterHeader) := by
    unfold FileFormat.encodeU32Bytes
    simp only [List.cons_append, List.nil_append, decodeUnsignedFixed,
      Option.bind_eq_bind, Option.bind]
    have roundtrip := FileFormat.decodeU32_encode rightmost
    unfold FileFormat.decodeU32 at roundtrip
    apply congrArg (fun value => some (value, afterHeader))
    omega
  rw [decodedRightmost]
  simpa [replacedLayout, PhysicalCodec.encodeU16Nat] using replacedDrop

theorem canonicalIndexInteriorPointers_interiorPageBody
    (rightmost : U32Value) (cells : List (List UInt8))
    (fits : PhysicalTableBTree.InteriorPageFit cells) :
    canonicalIndexInteriorPointersBeginAtContent
      (CoreFile.replaceFirst 2
        (PhysicalTableBTree.interiorPageBody rightmost cells)) = true := by
  have countBound : cells.length < 65536 := fits.cellCount_lt
  have contentBound : PhysicalCodec.pageSize -
      (PhysicalCodec.cellBytes cells).length < 65536 :=
    PhysicalCodec.contentStart_lt cells
  cases cells with
  | nil =>
      simp [canonicalIndexInteriorPointersBeginAtContent,
        PhysicalTableBTree.interiorPageBody,
        PhysicalTableBTree.interiorHeader, PhysicalCodec.leafPointers,
        PhysicalCodec.cellOffsetsFrom, PhysicalCodec.cellBytes,
        CoreFile.replaceFirst, PhysicalCodec.encodeU16Nat,
        FileFormat.encodeUnsignedFixed, FileFormat.encodeU32Bytes,
        FileFormat.decodeU16]
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
      simp [canonicalIndexInteriorPointersBeginAtContent,
        PhysicalTableBTree.interiorPageBody,
        PhysicalTableBTree.interiorHeader, PhysicalCodec.leafPointers,
        PhysicalCodec.cellOffsetsFrom, PhysicalCodec.cellBytes,
        CoreFile.replaceFirst, PhysicalCodec.encodeU16Nat,
        FileFormat.encodeUnsignedFixed, FileFormat.encodeU32Bytes,
        FileFormat.decodeU16, Nat.mod_eq_of_lt countBound,
        Nat.mod_eq_of_lt contentBound, restOrdered, decodedCount, decodedContent]

def decodePackedIndexInteriorCellsFrom (source : PageSource) (fuel : Nat) :
    Nat → List UInt8 → Option (List (Nat × IndexEntry) × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (child, afterChild) ← decodeUnsignedFixed 4 input
      let (entry, afterEntry) ←
        decodeIndexCellWithSuffixFrom source fuel afterChild
      let (entries, suffix) ←
        decodePackedIndexInteriorCellsFrom source fuel count afterEntry
      some ((child, entry) :: entries, suffix)

def decodeIndexLeafByPointersFrom (source : PageSource) (page : List UInt8) :
    Option (List IndexEntry) := do
  let offsets ← leafIndexOffsets? page
  offsets.mapM fun offset =>
    decodeIndexCellFrom source (source.pageCount + 1) (page.drop offset)

def decodeIndexLeafFrom (source : PageSource) (page : List UInt8) :
    Option (List IndexEntry) :=
  if canonicalIndexLeafPointersBeginAtContent page then
    match canonicalIndexLeafContent? page with
    | some (count, content) =>
        match decodePackedIndexCellsFrom source (source.pageCount + 1)
            count content with
        | some (entries, []) => some entries
        | _ => decodeIndexLeafByPointersFrom source page
    | none => decodeIndexLeafByPointersFrom source page
  else
    decodeIndexLeafByPointersFrom source page

theorem decodeIndexLeafFrom_resolvedLeaf (index : Core.Index)
    (source : PageSource) (rows : List Core.Row)
    (plans : List CoreOverflow.CellPlan) (next : Nat)
    (resolved : CoreOverflow.Resolved) (page : CoreFile.Page)
    (planned : rows.mapM (CoreOverflow.indexCellPlan? index) = some plans)
    (resolvedResult : CoreOverflow.resolvePlans next plans = some resolved)
    (built : CoreFile.indexLeafPage? resolved.cells = some page)
    (nextPositive : 0 < next)
    (pageBound : next + resolved.pages.length < 2 ^ 32)
    (fuelBound : resolved.pages.length < source.pageCount + 1)
    (reads : ReadsPagesFrom source next resolved.pages) :
    decodeIndexLeafFrom source page.bytes =
      some (rows.map fun row => ⟨row.value index.column, row.rowid⟩) := by
  unfold CoreFile.indexLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 10 0 resolved.cells with
  | none => simp [bodyResult] at built
  | some body =>
    simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
    injection built with pageEqual
    subst page
    have bodyExact : body.bytes = CoreFile.replaceFirst 10
        (PhysicalCodec.leafPageBody 0 resolved.cells) ∧
        PhysicalCodec.PageFit 0 resolved.cells := by
      unfold CoreFile.leafBody? at bodyResult
      split at bodyResult
      next typeByte =>
        split at bodyResult
        next fits =>
          injection bodyResult with bodyEqual
          subst body
          exact ⟨rfl, fits⟩
        next doesNotFit => contradiction
      next invalidType => contradiction
    rcases bodyExact with ⟨bodyBytes, fits⟩
    have content := canonicalIndexLeafContent_leafPageBody resolved.cells fits
    have pointers := canonicalIndexLeafPointers_leafPageBody resolved.cells fits
    have planLength := mapM_length_of_eq_some
      (CoreOverflow.indexCellPlan? index) rows plans planned
    have cellLength := CoreOverflow.resolvePlans_cells_length resolvedResult
    have countEqual : resolved.cells.length = rows.length := by omega
    have decoded := decodePackedIndexCellsFrom_resolvePlans index source
      (source.pageCount + 1) rows plans next resolved planned resolvedResult
      nextPositive pageBound fuelBound reads []
    simp only [List.append_nil] at decoded
    change decodeIndexLeafFrom source body.bytes = _
    rw [bodyBytes]
    unfold decodeIndexLeafFrom
    rw [pointers, content, countEqual]
    simp [decoded]

theorem decodeIndexLeafFrom_indexLeafPage
    (source : PageSource) {cells : List (List UInt8)}
    {entries : List IndexEntry} {page : CoreFile.Page}
    (decoded : IndexCellsDecode source (source.pageCount + 1) cells entries)
    (built : CoreFile.indexLeafPage? cells = some page) :
    decodeIndexLeafFrom source page.bytes = some entries := by
  unfold CoreFile.indexLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 10 0 cells with
  | none => simp [bodyResult] at built
  | some body =>
    simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
    injection built with pageEqual
    subst page
    have bodyExact : body.bytes = CoreFile.replaceFirst 10
        (PhysicalCodec.leafPageBody 0 cells) ∧
        PhysicalCodec.PageFit 0 cells := by
      unfold CoreFile.leafBody? at bodyResult
      split at bodyResult
      next typeByte =>
        split at bodyResult
        next fits =>
          injection bodyResult with bodyEqual
          subst body
          exact ⟨rfl, fits⟩
        next doesNotFit => contradiction
      next invalidType => contradiction
    rcases bodyExact with ⟨bodyBytes, fits⟩
    have content := canonicalIndexLeafContent_leafPageBody cells fits
    have pointers := canonicalIndexLeafPointers_leafPageBody cells fits
    have packed := decodePackedIndexCellsFrom_of_relation decoded []
    simp only [List.append_nil] at packed
    change decodeIndexLeafFrom source body.bytes = _
    rw [bodyBytes]
    unfold decodeIndexLeafFrom
    rw [pointers, content]
    simp [packed]

def decodeIndexInteriorByPointersFrom (source : PageSource)
    (page : List UInt8) : Option (List (Nat × IndexEntry) × Nat) := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    let (header, afterHeader) ← decodeBTreePageHeader page
    match header with
    | .interiorIndex common rightmost => do
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        let entries ← offsets.mapM fun offset => do
          if _bounded : offset < page.length then
            let (child, afterChild) ← decodeUnsignedFixed 4 (page.drop offset)
            let key ← decodeIndexCellFrom source (source.pageCount + 1) afterChild
            some (child, key)
          else none
        some (entries, rightmost.val)
    | _ => none
  else none

def decodeIndexInteriorFrom (source : PageSource) (page : List UInt8) :
    Option (List (Nat × IndexEntry) × Nat) :=
  match page with
  | 10 :: _ => none
  | _ =>
      if canonicalIndexInteriorPointersBeginAtContent page then
        match canonicalIndexInteriorContent? page with
        | some (count, rightmost, content) =>
            match decodePackedIndexInteriorCellsFrom source
                (source.pageCount + 1) count content with
            | some (entries, []) => some (entries, rightmost)
            | _ => decodeIndexInteriorByPointersFrom source page
        | none => decodeIndexInteriorByPointersFrom source page
      else
        decodeIndexInteriorByPointersFrom source page

theorem decodeIndexInteriorFrom_indexLeafPage
    (source : PageSource) {cells : List (List UInt8)} {page : CoreFile.Page}
    (built : CoreFile.indexLeafPage? cells = some page) :
    decodeIndexInteriorFrom source page.bytes = none := by
  unfold CoreFile.indexLeafPage? at built
  cases bodyResult : CoreFile.leafBody? 10 0 cells with
  | none => simp [bodyResult] at built
  | some body =>
    simp only [bodyResult, Option.bind_eq_bind, Option.bind] at built
    injection built with pageEqual
    subst page
    have bodyBytes : body.bytes = CoreFile.replaceFirst 10
        (PhysicalCodec.leafPageBody 0 cells) := by
      unfold CoreFile.leafBody? at bodyResult
      split at bodyResult
      next typeByte =>
        split at bodyResult
        next fits =>
          injection bodyResult with bodyEqual
          subst body
          rfl
        next doesNotFit => contradiction
      next invalidType => contradiction
    change decodeIndexInteriorFrom source body.bytes = none
    rw [bodyBytes]
    unfold decodeIndexInteriorFrom
    simp [CoreFile.replaceFirst, PhysicalCodec.leafPageBody,
      PhysicalCodec.leafHeader]

theorem boundedU32?_value {value : Nat} {bounded : U32Value}
    (success : RecursivePageBTree.boundedU32? value = some bounded) :
    bounded.val = value := by
  unfold RecursivePageBTree.boundedU32? at success
  split at success
  next => injection success with equal; subst bounded; rfl
  next => contradiction

theorem decodeIndexInteriorFrom_indexInteriorPage_one
    (source : PageSource) {child right : Nat} {separator : List UInt8}
    {separatorEntry : IndexEntry} {page : CoreFile.Page}
    (separatorDecoded : ∀ suffix,
      decodeIndexCellWithSuffixFrom source (source.pageCount + 1)
          (separator ++ suffix) = some (separatorEntry, suffix))
    (built : RecursivePageBTree.indexInteriorPage?
      [(child, separator)] right = some page) :
    decodeIndexInteriorFrom source page.bytes =
      some ([(child, separatorEntry)], right) := by
  unfold RecursivePageBTree.indexInteriorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
    simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
    cases childResult : RecursivePageBTree.boundedU32? child with
    | none => simp [List.mapM_cons, childResult] at built
    | some childPage =>
      simp only [List.mapM_cons, childResult, List.mapM_nil, pure, Pure.pure,
        Option.bind_eq_bind, Option.bind] at built
      split at built
      next fits =>
        injection built with pageEqual
        subst page
        let cell := PhysicalTableBTree.encodeU32Nat childPage.val ++ separator
        have content := canonicalIndexInteriorContent_interiorPageBody
          rightmost [cell] fits
        have pointers := canonicalIndexInteriorPointers_interiorPageBody
          rightmost [cell] fits
        unfold decodeIndexInteriorFrom
        rw [pointers, content]
        simp only [if_pos rfl]
        unfold decodePackedIndexInteriorCellsFrom
        simp only [PhysicalCodec.cellBytes, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.length_cons,
          List.length_nil, cell, List.append_assoc]
        unfold PhysicalTableBTree.encodeU32Nat
        rw [decodeUnsignedFixed_encode _ childPage.isLt]
        simp only [Option.bind_eq_bind, Option.bind]
        have decodedEmpty := separatorDecoded []
        simp only [List.append_nil] at decodedEmpty
        rw [decodedEmpty]
        simp [decodePackedIndexInteriorCellsFrom,
          boundedU32?_value childResult, boundedU32?_value rightResult,
          CoreFile.replaceFirst, PhysicalTableBTree.interiorPageBody,
          PhysicalTableBTree.interiorHeader]
      next doesNotFit => contradiction

theorem decodeIndexInteriorFrom_indexInteriorPage_two
    (source : PageSource) {firstChild secondChild right : Nat}
    {firstSeparator secondSeparator : List UInt8}
    {firstEntry secondEntry : IndexEntry} {page : CoreFile.Page}
    (firstDecoded : ∀ suffix,
      decodeIndexCellWithSuffixFrom source (source.pageCount + 1)
          (firstSeparator ++ suffix) = some (firstEntry, suffix))
    (secondDecoded : ∀ suffix,
      decodeIndexCellWithSuffixFrom source (source.pageCount + 1)
          (secondSeparator ++ suffix) = some (secondEntry, suffix))
    (built : RecursivePageBTree.indexInteriorPage?
      [(firstChild, firstSeparator), (secondChild, secondSeparator)] right =
        some page) :
    decodeIndexInteriorFrom source page.bytes =
      some ([(firstChild, firstEntry), (secondChild, secondEntry)], right) := by
  unfold RecursivePageBTree.indexInteriorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
    simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
    cases firstResult : RecursivePageBTree.boundedU32? firstChild with
    | none => simp [List.mapM_cons, firstResult] at built
    | some firstPage =>
      simp only [List.mapM_cons, firstResult, Option.bind_eq_bind,
        Option.bind] at built
      cases secondResult : RecursivePageBTree.boundedU32? secondChild with
      | none => simp [List.mapM_cons, secondResult] at built
      | some secondPage =>
        simp only [List.mapM_cons, secondResult, List.mapM_nil, pure,
          Pure.pure, Option.bind_eq_bind, Option.bind] at built
        split at built
        next fits =>
          injection built with pageEqual
          subst page
          let firstCell := PhysicalTableBTree.encodeU32Nat firstPage.val ++
            firstSeparator
          let secondCell := PhysicalTableBTree.encodeU32Nat secondPage.val ++
            secondSeparator
          have content := canonicalIndexInteriorContent_interiorPageBody
            rightmost [firstCell, secondCell] fits
          have pointers := canonicalIndexInteriorPointers_interiorPageBody
            rightmost [firstCell, secondCell] fits
          unfold decodeIndexInteriorFrom
          rw [pointers, content]
          simp only [if_pos rfl]
          unfold decodePackedIndexInteriorCellsFrom
          simp only [PhysicalCodec.cellBytes, List.flatten_cons,
            List.flatten_nil, List.append_nil, List.length_cons,
            List.length_nil, firstCell, secondCell, List.append_assoc]
          unfold PhysicalTableBTree.encodeU32Nat
          rw [decodeUnsignedFixed_encode _ firstPage.isLt]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [firstDecoded
            (FileFormat.encodeUnsignedFixed 4 secondPage.val ++
              secondSeparator)]
          simp only [Option.bind_eq_bind, Option.bind]
          unfold decodePackedIndexInteriorCellsFrom
          rw [decodeUnsignedFixed_encode _ secondPage.isLt]
          simp only [Option.bind_eq_bind, Option.bind]
          have decodedEmpty := secondDecoded []
          simp only [List.append_nil] at decodedEmpty
          rw [decodedEmpty]
          simp [decodePackedIndexInteriorCellsFrom,
            boundedU32?_value firstResult,
            boundedU32?_value secondResult, boundedU32?_value rightResult,
            CoreFile.replaceFirst, PhysicalTableBTree.interiorPageBody,
            PhysicalTableBTree.interiorHeader]
        next doesNotFit => contradiction

/-- Traverse a physical SQLite index B-tree, retaining promoted interior keys
in their in-order positions. The fuel makes malformed cycles total. -/
def decodeIndexSubtreeFrom (source : PageSource) :
    Nat → Nat → Option (List IndexEntry)
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeIndexInteriorFrom source page with
      | some (entries, rightmost) => do
          let groups ← entries.mapM fun entry => do
            let left ← decodeIndexSubtreeFrom source fuel entry.1
            some (left ++ [entry.2])
          let right ← decodeIndexSubtreeFrom source fuel rightmost
          some (groups.flatten ++ right)
      | none => decodeIndexLeafFrom source page

def decodeIndexSubtree (physicalPages : List (List UInt8))
    (fuel pageNumber : Nat) : Option (List IndexEntry) :=
  decodeIndexSubtreeFrom (.ofList physicalPages) fuel pageNumber

theorem decodeIndexSubtree_ofList (physicalPages : List (List UInt8))
    (fuel pageNumber : Nat) :
    decodeIndexSubtreeFrom (.ofList physicalPages) fuel pageNumber =
      decodeIndexSubtree physicalPages fuel pageNumber := rfl

theorem decodeIndexSubtreeFrom_encodePagesFrom (source : PageSource) :
    ∀ (plan : RecursivePageBTree.IndexPlan) (start : Nat)
      (pages : List CoreFile.Page) (entries : List IndexEntry) (fuel : Nat),
      plan.encodePagesFrom start = some pages →
      ReadsPagesFrom source start pages →
      plan.Balanced →
      IndexPlanDecodes source (source.pageCount + 1) plan entries →
      plan.height < fuel →
      decodeIndexSubtreeFrom source fuel start = some entries
  | .leaf cells, start, pages, entries, fuel, encoded, reads, _, refined,
      fuelBound => by
      simp only [RecursivePageBTree.IndexPlan.encodePagesFrom,
        Option.bind_eq_bind, Option.bind] at encoded
      cases pageResult : CoreFile.indexLeafPage? cells with
      | none => simp [pageResult] at encoded
      | some page =>
        simp only [pageResult, Option.some.injEq] at encoded
        subst pages
        cases refined with
        | leaf decoded =>
          have rootRead : source.readPage start = some page.bytes := by
            have available := reads 0 (by simp)
            simpa using available
          cases fuel with
          | zero => simp [RecursivePageBTree.IndexPlan.height] at fuelBound
          | succ childFuel =>
            simp only [decodeIndexSubtreeFrom]
            rw [rootRead]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [decodeIndexInteriorFrom_indexLeafPage source pageResult]
            exact decodeIndexLeafFrom_indexLeafPage source decoded pageResult
  | .branch2 left separator right, start, pages, entries, fuel, encoded,
      reads, balanced, refined, fuelBound => by
      simp only [RecursivePageBTree.IndexPlan.encodePagesFrom,
        Option.bind_eq_bind, Option.bind] at encoded
      let leftStart := start + 1
      let rightStart := leftStart + left.pageCount
      cases rootResult : RecursivePageBTree.indexInteriorPage?
          [(leftStart, separator)] rightStart with
      | none => simp [leftStart, rightStart, rootResult] at encoded
      | some root =>
        simp only [leftStart, rightStart, rootResult] at encoded
        cases leftResult : left.encodePagesFrom (start + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases rightResult : right.encodePagesFrom
              (start + 1 + left.pageCount) with
          | none => simp [rightResult] at encoded
          | some rightPages =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst pages
            cases refined with
            | branch2 leftDecoded separatorDecoded rightDecoded =>
              simp only [RecursivePageBTree.IndexPlan.Balanced] at balanced
              rcases balanced with
                ⟨leftBalanced, rightBalanced, heightEqual⟩
              have rootRead : source.readPage start = some root.bytes := by
                have available := reads 0 (by simp)
                simpa using available
              have childrenReads : ReadsPagesFrom source leftStart
                  (leftPages ++ rightPages) := by
                have remaining := ReadsPagesFrom.right
                  (left := [root]) (right := leftPages ++ rightPages) reads
                simpa [leftStart] using remaining
              have leftReads : ReadsPagesFrom source leftStart leftPages :=
                ReadsPagesFrom.left childrenReads
              have leftLength :=
                RecursivePageBTree.IndexPlan.encodePagesFrom_length leftResult
              have rightReads : ReadsPagesFrom source rightStart rightPages := by
                have remaining := ReadsPagesFrom.right childrenReads
                simpa [rightStart, leftStart, leftLength] using remaining
              cases fuel with
              | zero =>
                simp [RecursivePageBTree.IndexPlan.height] at fuelBound
              | succ childFuel =>
                have leftFuel : left.height < childFuel := by
                  simp only [RecursivePageBTree.IndexPlan.height] at fuelBound
                  omega
                have rightFuel : right.height < childFuel := by
                  rw [← heightEqual]
                  exact leftFuel
                have leftExact := decodeIndexSubtreeFrom_encodePagesFrom source
                  left leftStart leftPages _ childFuel leftResult leftReads
                  leftBalanced leftDecoded leftFuel
                have rightExact := decodeIndexSubtreeFrom_encodePagesFrom source
                  right rightStart rightPages _ childFuel rightResult rightReads
                  rightBalanced rightDecoded rightFuel
                simp only [decodeIndexSubtreeFrom]
                rw [rootRead]
                simp only [Option.bind_eq_bind, Option.bind]
                rw [decodeIndexInteriorFrom_indexInteriorPage_one source
                  separatorDecoded rootResult]
                simp only [List.mapM_cons, List.mapM_nil, pure, Pure.pure,
                  Option.bind_eq_bind, Option.bind]
                rw [leftExact, rightExact]
                simp
  | .branch3 left firstSeparator middle secondSeparator right, start, pages,
      entries, fuel, encoded, reads, balanced, refined, fuelBound => by
      simp only [RecursivePageBTree.IndexPlan.encodePagesFrom,
        Option.bind_eq_bind, Option.bind] at encoded
      let leftStart := start + 1
      let middleStart := leftStart + left.pageCount
      let rightStart := middleStart + middle.pageCount
      cases rootResult : RecursivePageBTree.indexInteriorPage?
          [(leftStart, firstSeparator), (middleStart, secondSeparator)]
          rightStart with
      | none =>
        simp [leftStart, middleStart, rightStart, rootResult] at encoded
      | some root =>
        simp only [leftStart, middleStart, rightStart, rootResult] at encoded
        cases leftResult : left.encodePagesFrom (start + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases middleResult : middle.encodePagesFrom
              (start + 1 + left.pageCount) with
          | none => simp [middleResult] at encoded
          | some middlePages =>
            simp only [middleResult] at encoded
            cases rightResult : right.encodePagesFrom
                (start + 1 + left.pageCount + middle.pageCount) with
            | none => simp [rightResult] at encoded
            | some rightPages =>
              simp only [rightResult, Option.some.injEq] at encoded
              subst pages
              cases refined with
              | branch3 leftDecoded firstDecoded middleDecoded secondDecoded
                  rightDecoded =>
                simp only [RecursivePageBTree.IndexPlan.Balanced] at balanced
                rcases balanced with
                  ⟨leftBalanced, middleBalanced, rightBalanced,
                    leftMiddleHeight, middleRightHeight⟩
                have rootRead : source.readPage start = some root.bytes := by
                  have available := reads 0 (by simp)
                  simpa using available
                have childrenReads : ReadsPagesFrom source leftStart
                    (leftPages ++ (middlePages ++ rightPages)) := by
                  have normalized : ReadsPagesFrom source start
                      ([root] ++ (leftPages ++ (middlePages ++ rightPages))) := by
                    simpa [List.append_assoc] using reads
                  have remaining := ReadsPagesFrom.right
                    (left := [root])
                    (right := leftPages ++ (middlePages ++ rightPages))
                    normalized
                  simpa [leftStart, List.append_assoc] using remaining
                have leftReads : ReadsPagesFrom source leftStart leftPages :=
                  ReadsPagesFrom.left childrenReads
                have afterLeftReads : ReadsPagesFrom source
                    (leftStart + leftPages.length)
                    (middlePages ++ rightPages) :=
                  ReadsPagesFrom.right childrenReads
                have leftLength :=
                  RecursivePageBTree.IndexPlan.encodePagesFrom_length leftResult
                have middleReads : ReadsPagesFrom source middleStart
                    middlePages := by
                  have middlePrefix := ReadsPagesFrom.left afterLeftReads
                  simpa [middleStart, leftStart, leftLength] using middlePrefix
                have afterMiddleReads : ReadsPagesFrom source
                    (leftStart + leftPages.length + middlePages.length)
                    rightPages := ReadsPagesFrom.right afterLeftReads
                have middleLength :=
                  RecursivePageBTree.IndexPlan.encodePagesFrom_length
                    middleResult
                have rightReads : ReadsPagesFrom source rightStart
                    rightPages := by
                  simpa [rightStart, middleStart, leftLength, middleLength,
                    Nat.add_assoc] using afterMiddleReads
                cases fuel with
                | zero =>
                  simp [RecursivePageBTree.IndexPlan.height] at fuelBound
                | succ childFuel =>
                  have leftFuel : left.height < childFuel := by
                    simp only [RecursivePageBTree.IndexPlan.height] at fuelBound
                    omega
                  have middleFuel : middle.height < childFuel := by
                    rw [← leftMiddleHeight]
                    exact leftFuel
                  have rightFuel : right.height < childFuel := by
                    rw [← middleRightHeight]
                    exact middleFuel
                  have leftExact := decodeIndexSubtreeFrom_encodePagesFrom
                    source left leftStart leftPages _ childFuel leftResult
                    leftReads leftBalanced leftDecoded leftFuel
                  have middleExact := decodeIndexSubtreeFrom_encodePagesFrom
                    source middle middleStart middlePages _ childFuel
                    middleResult middleReads middleBalanced middleDecoded
                    middleFuel
                  have rightExact := decodeIndexSubtreeFrom_encodePagesFrom
                    source right rightStart rightPages _ childFuel rightResult
                    rightReads rightBalanced rightDecoded rightFuel
                  simp only [decodeIndexSubtreeFrom]
                  rw [rootRead]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [decodeIndexInteriorFrom_indexInteriorPage_two source
                    firstDecoded secondDecoded rootResult]
                  simp only [List.mapM_cons, List.mapM_nil, pure, Pure.pure,
                    Option.bind_eq_bind, Option.bind]
                  rw [leftExact, middleExact, rightExact]
                  simp [List.append_assoc]

theorem decodeIndexSubtreeFrom_encodeIndex (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1) :
    decodeIndexSubtreeFrom source (source.pageCount + 1) rootPage =
      some ((CoreFile.sortedIndexRows table index).map fun row =>
        ⟨row.value index.column, row.rowid⟩) := by
  unfold CoreOverflow.encodeIndex at encoded
  cases plansResult : CoreOverflow.indexPlans table index with
  | none => simp [plansResult] at encoded
  | some plans =>
    simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
    cases provisionalResult : CoreOverflow.provisionalIndexStore? plans with
    | none => simp [provisionalResult] at encoded
    | some provisional =>
      simp only [provisionalResult] at encoded
      cases resolvedResult : CoreOverflow.resolvePlans
          (rootPage + provisional.plan.pageCount) plans with
      | none => simp [resolvedResult] at encoded
      | some resolved =>
        simp only [resolvedResult] at encoded
        cases updatedResult : provisional.retarget? resolved.cells with
        | none => simp [updatedResult] at encoded
        | some topology =>
          simp only [updatedResult] at encoded
          cases treeResult : topology.plan.encodePagesFrom rootPage with
          | none => simp [treeResult] at encoded
          | some treePages =>
            simp only [treeResult, Option.some.injEq] at encoded
            subst encoding
            have treeReads : ReadsPagesFrom source rootPage treePages :=
              ReadsPagesFrom.left reads
            have treeLength :=
              RecursivePageBTree.IndexPlan.encodePagesFrom_length treeResult
            have pageCountEqual :=
              RecursivePageBTree.IndexStore.retarget?_pageCount updatedResult
            have overflowReads : ReadsPagesFrom source
                (rootPage + provisional.plan.pageCount) resolved.pages := by
              have remaining := ReadsPagesFrom.right reads
              simpa [CoreOverflow.IndexEncoding.pages, treeLength,
                pageCountEqual] using remaining
            have planned : (CoreFile.sortedIndexRows table index).mapM
                (CoreOverflow.indexCellPlan? index) = some plans := by
              simpa [CoreOverflow.indexPlans] using plansResult
            have cellsDecoded := indexCellsDecode_resolvePlans index source
              (source.pageCount + 1) (CoreFile.sortedIndexRows table index)
              plans (rootPage + provisional.plan.pageCount) resolved planned
              resolvedResult (by omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at pageBound
                omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at withinSource
                omega)
              overflowReads
            have cellsEqual :=
              RecursivePageBTree.IndexStore.retarget?_represents updatedResult
            have planCells : IndexCellsDecode source (source.pageCount + 1)
                topology.plan.toCells
                ((CoreFile.sortedIndexRows table index).map fun row =>
                  ⟨row.value index.column, row.rowid⟩) := by
              rw [cellsEqual]
              exact cellsDecoded
            have planDecoded := IndexPlanDecodes.of_cells topology.plan _ planCells
            have balanced := topology.balanced
            have heightBound : topology.plan.height < source.pageCount + 1 := by
              have heightPageCount := topology.plan.height_lt_pageCount
              simp only [CoreOverflow.IndexEncoding.pages,
                List.length_append] at withinSource
              omega
            exact decodeIndexSubtreeFrom_encodePagesFrom source topology.plan rootPage
              treePages _ (source.pageCount + 1) treeResult treeReads balanced
              planDecoded heightBound

def IndexEntry.matchesValue (entry : IndexEntry) (target : Core.Value) : Bool :=
  PhysicalQuery.sqlEquals entry.value target = .true

private def indexLowerAllows (lower : Option IndexEntry)
    (target : Core.Value) : Bool :=
  match target with
  | .realBits _ => true
  | _ => match lower with
      | none => true
      | some entry => PhysicalQuery.compareValue entry.value target != .gt

private def indexUpperAllows (target : Core.Value) (upper : IndexEntry) : Bool :=
  match target with
  | .realBits _ => true
  | _ => PhysicalQuery.compareValue target upper.value != .gt

/-! ## Abstract promoted-key index routing

SQLite index interior records are data entries, not synthetic separators.  This
tree therefore includes every promoted record exactly once in `toList`.  The
well-routed predicate states the semantic fact the byte-level refinement must
establish: every SQL-equal query is admitted to the child containing that
entry. -/

inductive AbstractIndexTree where
  | leaf (entries : List IndexEntry)
  | branch2 (left : AbstractIndexTree) (separator : IndexEntry)
      (right : AbstractIndexTree)
  | branch3 (left : AbstractIndexTree) (firstSeparator : IndexEntry)
      (middle : AbstractIndexTree) (secondSeparator : IndexEntry)
      (right : AbstractIndexTree)

def AbstractIndexTree.toList : AbstractIndexTree → List IndexEntry
  | .leaf entries => entries
  | .branch2 left separator right =>
      left.toList ++ [separator] ++ right.toList
  | .branch3 left firstSeparator middle secondSeparator right =>
      left.toList ++ [firstSeparator] ++ middle.toList ++
        [secondSeparator] ++ right.toList

/-- The pure meaning of the bounded physical prefix cursor. Unlike
`toList.take`, this definition exposes where traversal stops, so the effectful
reader can refine it without acquiring later children. -/
def AbstractIndexTree.cursorPrefix : Nat → AbstractIndexTree → List IndexEntry
  | 0, _ => []
  | limit + 1, .leaf entries => entries.take (limit + 1)
  | limit + 1, .branch2 left separator right =>
      let leftPrefix := left.cursorPrefix (limit + 1)
      if leftPrefix.length = limit + 1 then leftPrefix
      else leftPrefix ++ [separator] ++
        right.cursorPrefix (limit - leftPrefix.length)
  | limit + 1, .branch3 left firstSeparator middle secondSeparator right =>
      let leftPrefix := left.cursorPrefix (limit + 1)
      if leftPrefix.length = limit + 1 then leftPrefix
      else
        let middlePrefix := middle.cursorPrefix (limit - leftPrefix.length)
        let beforeRight := leftPrefix ++ [firstSeparator] ++ middlePrefix
        if beforeRight.length = limit + 1 then beforeRight
        else beforeRight ++ [secondSeparator] ++
          right.cursorPrefix (limit - beforeRight.length)

def AbstractIndexTree.leftmostLeaf : AbstractIndexTree → List IndexEntry
  | .leaf entries => entries
  | .branch2 left _ _ => left.leftmostLeaf
  | .branch3 left _ _ _ _ => left.leftmostLeaf

theorem AbstractIndexTree.leftmostLeaf_length_le (tree : AbstractIndexTree) :
    tree.leftmostLeaf.length ≤ tree.toList.length := by
  induction tree with
  | leaf entries => exact Nat.le_refl _
  | branch2 left separator right leftInduction rightInduction =>
      simp only [AbstractIndexTree.leftmostLeaf, AbstractIndexTree.toList,
        List.length_append, List.length_cons, List.length_nil]
      omega
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [AbstractIndexTree.leftmostLeaf, AbstractIndexTree.toList,
        List.length_append, List.length_cons, List.length_nil]
      omega

theorem AbstractIndexTree.take_toList_eq_take_leftmostLeaf
    (tree : AbstractIndexTree) (limit : Nat)
    (fits : limit ≤ tree.leftmostLeaf.length) :
    tree.toList.take limit = tree.leftmostLeaf.take limit := by
  induction tree with
  | leaf entries => rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp only [AbstractIndexTree.leftmostLeaf] at fits ⊢
      simp only [AbstractIndexTree.toList, List.append_assoc]
      rw [List.take_append_of_le_length
        (Nat.le_trans fits left.leftmostLeaf_length_le)]
      exact leftInduction fits
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [AbstractIndexTree.leftmostLeaf] at fits ⊢
      simp only [AbstractIndexTree.toList, List.append_assoc]
      rw [List.take_append_of_le_length
        (Nat.le_trans fits left.leftmostLeaf_length_le)]
      exact leftInduction fits

def AbstractIndexTree.equalityCandidates (target : Core.Value) :
    AbstractIndexTree → List IndexEntry
  | .leaf entries => entries
  | .branch2 left separator right =>
      (if indexUpperAllows target separator then
        left.equalityCandidates target else []) ++ [separator] ++
      (if indexLowerAllows (some separator) target then
        right.equalityCandidates target else [])
  | .branch3 left firstSeparator middle secondSeparator right =>
      (if indexUpperAllows target firstSeparator then
        left.equalityCandidates target else []) ++ [firstSeparator] ++
      (if indexLowerAllows (some firstSeparator) target &&
          indexUpperAllows target secondSeparator then
        middle.equalityCandidates target else []) ++ [secondSeparator] ++
      (if indexLowerAllows (some secondSeparator) target then
        right.equalityCandidates target else [])

inductive AbstractIndexTree.WellRouted : AbstractIndexTree → Prop where
  | leaf (entries : List IndexEntry) : WellRouted (.leaf entries)
  | branch2 (left right : AbstractIndexTree) (separator : IndexEntry)
      (leftValid : left.WellRouted) (rightValid : right.WellRouted)
      (leftAdmitted : ∀ target entry, entry ∈ left.toList →
        entry.matchesValue target = true →
        indexUpperAllows target separator = true)
      (rightAdmitted : ∀ target entry, entry ∈ right.toList →
        entry.matchesValue target = true →
        indexLowerAllows (some separator) target = true) :
      WellRouted (.branch2 left separator right)
  | branch3 (left middle right : AbstractIndexTree)
      (firstSeparator secondSeparator : IndexEntry)
      (leftValid : left.WellRouted) (middleValid : middle.WellRouted)
      (rightValid : right.WellRouted)
      (leftAdmitted : ∀ target entry, entry ∈ left.toList →
        entry.matchesValue target = true →
        indexUpperAllows target firstSeparator = true)
      (middleAdmitted : ∀ target entry, entry ∈ middle.toList →
        entry.matchesValue target = true →
        (indexLowerAllows (some firstSeparator) target &&
          indexUpperAllows target secondSeparator) = true)
      (rightAdmitted : ∀ target entry, entry ∈ right.toList →
        entry.matchesValue target = true →
        indexLowerAllows (some secondSeparator) target = true) :
      WellRouted
        (.branch3 left firstSeparator middle secondSeparator right)

def IndexEntry.IntegerValued (entry : IndexEntry) : Prop :=
  ∃ value : Core.Integer, entry.value = .integer value

instance (entry : IndexEntry) : Decidable entry.IntegerValued := by
  cases valueResult : entry.value with
  | integer value =>
      exact isTrue ⟨value, valueResult⟩
  | null | realBits | text | blob =>
      apply isFalse
      rintro ⟨value, equal⟩
      rw [valueResult] at equal
      contradiction

def IndexEntry.ValueLe (left right : IndexEntry) : Prop :=
  PhysicalQuery.compareValue left.value right.value ≠ .gt

instance (left right : IndexEntry) : Decidable (left.ValueLe right) := by
  unfold IndexEntry.ValueLe
  infer_instance

/-- A proof-oriented certificate for the common integer-index case.  It says
more than shape validity: every stored/promoted value is an integer and each
child is bounded by the promoted entries around it.  REAL query targets are
handled conservatively by visiting every interval, so this certificate never
depends on an unproved mixed INTEGER/REAL ordering law. -/
inductive AbstractIndexTree.IntegerOrdered : AbstractIndexTree → Prop where
  | leaf (entries : List IndexEntry)
      (integers : ∀ entry ∈ entries, entry.IntegerValued) :
      IntegerOrdered (.leaf entries)
  | branch2 (left right : AbstractIndexTree) (separator : IndexEntry)
      (leftValid : left.IntegerOrdered) (rightValid : right.IntegerOrdered)
      (separatorInteger : separator.IntegerValued)
      (leftBefore : ∀ entry ∈ left.toList, entry.ValueLe separator)
      (rightAfter : ∀ entry ∈ right.toList, separator.ValueLe entry) :
      IntegerOrdered (.branch2 left separator right)
  | branch3 (left middle right : AbstractIndexTree)
      (firstSeparator secondSeparator : IndexEntry)
      (leftValid : left.IntegerOrdered)
      (middleValid : middle.IntegerOrdered)
      (rightValid : right.IntegerOrdered)
      (firstInteger : firstSeparator.IntegerValued)
      (secondInteger : secondSeparator.IntegerValued)
      (leftBefore : ∀ entry ∈ left.toList, entry.ValueLe firstSeparator)
      (middleAfter : ∀ entry ∈ middle.toList,
        firstSeparator.ValueLe entry)
      (middleBefore : ∀ entry ∈ middle.toList,
        entry.ValueLe secondSeparator)
      (rightAfter : ∀ entry ∈ right.toList,
        secondSeparator.ValueLe entry) :
      IntegerOrdered
        (.branch3 left firstSeparator middle secondSeparator right)

/-- Global in-order facts imply the local routing bounds carried by an
`IntegerOrdered` tree. This is the bridge from the encoder's sorted logical
sequence to the exact promoted-key topology decoded from its pages. -/
theorem AbstractIndexTree.IntegerOrdered.of_pairwise
    (tree : AbstractIndexTree)
    (integers : ∀ entry ∈ tree.toList, entry.IntegerValued)
    (ordered : tree.toList.Pairwise IndexEntry.ValueLe) :
    tree.IntegerOrdered := by
  induction tree with
  | leaf entries =>
      exact .leaf entries (by
        simpa [AbstractIndexTree.toList] using integers)
  | branch2 left separator right leftInduction rightInduction =>
      simp only [AbstractIndexTree.toList] at integers ordered
      have leftSeparatorRight := List.pairwise_append.mp ordered
      have leftSeparator := List.pairwise_append.mp leftSeparatorRight.1
      apply AbstractIndexTree.IntegerOrdered.branch2 left right separator
      · apply leftInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact leftSeparator.1
      · apply rightInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact leftSeparatorRight.2.1
      · exact integers separator (by simp)
      · intro entry member
        exact leftSeparator.2.2 entry member separator (by simp)
      · intro entry member
        exact leftSeparatorRight.2.2 separator (by simp) entry member
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      simp only [AbstractIndexTree.toList] at integers ordered
      have throughSecondRight := List.pairwise_append.mp ordered
      have throughMiddleSecond :=
        List.pairwise_append.mp throughSecondRight.1
      have leftFirstMiddle :=
        List.pairwise_append.mp throughMiddleSecond.1
      have leftFirst := List.pairwise_append.mp leftFirstMiddle.1
      apply AbstractIndexTree.IntegerOrdered.branch3 left middle right
        firstSeparator secondSeparator
      · apply leftInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact leftFirst.1
      · apply middleInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact leftFirstMiddle.2.1
      · apply rightInduction
        · intro entry member
          exact integers entry (by simp [member])
        · exact throughSecondRight.2.1
      · exact integers firstSeparator (by simp)
      · exact integers secondSeparator (by simp)
      · intro entry member
        exact leftFirst.2.2 entry member firstSeparator (by simp)
      · intro entry member
        exact leftFirstMiddle.2.2 firstSeparator (by simp) entry member
      · intro entry member
        exact throughMiddleSecond.2.2 entry (by simp [member]) secondSeparator
          (by simp)
      · intro entry member
        exact throughSecondRight.2.2 secondSeparator (by simp) entry member

structure AllCertificate {α : Type} (predicate : α → Prop)
    (values : List α) : Type where
  valid : ∀ value ∈ values, predicate value

def certifyAll {α : Type} (predicate : α → Prop)
    [DecidablePred predicate] :
    (values : List α) → Option (AllCertificate predicate values)
  | [] => some ⟨by simp⟩
  | value :: values => do
      if headValid : predicate value then
        let tailValid ← certifyAll predicate values
        some ⟨by
          intro candidate member
          rcases List.mem_cons.mp member with rfl | member
          · exact headValid
          · exact tailValid.valid candidate member⟩
      else none

structure AbstractIndexTree.IntegerOrderedCertificate
    (tree : AbstractIndexTree) : Type where
  valid : tree.IntegerOrdered

/-- A total proof-producing validator.  Success returns kernel evidence, not a
Boolean that later code must trust.  It is intentionally linear in the decoded
index and is suitable for connection-open certification; the cold-open plan
will replace that cost with persisted/authenticated provenance. -/
def AbstractIndexTree.certifyIntegerOrdered :
    (tree : AbstractIndexTree) → Option (IntegerOrderedCertificate tree)
  | .leaf entries => do
      let integers ← certifyAll IndexEntry.IntegerValued entries
      some ⟨.leaf entries integers.valid⟩
  | .branch2 left separator right => do
      let leftCertificate ← left.certifyIntegerOrdered
      let rightCertificate ← right.certifyIntegerOrdered
      if separatorInteger : separator.IntegerValued then
        let leftBefore ← certifyAll (·.ValueLe separator) left.toList
        let rightAfter ← certifyAll (separator.ValueLe ·) right.toList
        some ⟨.branch2 left right separator leftCertificate.valid
          rightCertificate.valid separatorInteger leftBefore.valid
          rightAfter.valid⟩
      else none
  | .branch3 left firstSeparator middle secondSeparator right => do
      let leftCertificate ← left.certifyIntegerOrdered
      let middleCertificate ← middle.certifyIntegerOrdered
      let rightCertificate ← right.certifyIntegerOrdered
      if firstInteger : firstSeparator.IntegerValued then
        if secondInteger : secondSeparator.IntegerValued then
          let leftBefore ← certifyAll (·.ValueLe firstSeparator) left.toList
          let middleAfter ← certifyAll (firstSeparator.ValueLe ·) middle.toList
          let middleBefore ← certifyAll (·.ValueLe secondSeparator) middle.toList
          let rightAfter ← certifyAll (secondSeparator.ValueLe ·) right.toList
          some ⟨.branch3 left middle right firstSeparator secondSeparator
            leftCertificate.valid middleCertificate.valid rightCertificate.valid
            firstInteger secondInteger leftBefore.valid middleAfter.valid
            middleBefore.valid rightAfter.valid⟩
        else none
      else none

theorem AbstractIndexTree.IntegerOrdered.allInteger {tree : AbstractIndexTree}
    (valid : tree.IntegerOrdered) :
    ∀ entry ∈ tree.toList, entry.IntegerValued := by
  induction valid with
  | leaf entries integers => simpa [AbstractIndexTree.toList] using integers
  | branch2 left right separator leftValid rightValid separatorInteger
      leftBefore rightAfter leftInduction rightInduction =>
      simp only [AbstractIndexTree.toList, List.mem_append, List.mem_singleton]
      intro entry member
      rcases member with (leftMember | equal) | rightMember
      · exact leftInduction entry leftMember
      · rw [equal]
        exact separatorInteger
      · exact rightInduction entry rightMember
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid firstInteger secondInteger leftBefore middleAfter
      middleBefore rightAfter leftInduction middleInduction rightInduction =>
      simp only [AbstractIndexTree.toList, List.mem_append, List.mem_singleton]
      intro entry member
      rcases member with
        (((leftMember | firstEqual) | middleMember) | secondEqual) | rightMember
      · exact leftInduction entry leftMember
      · rw [firstEqual]
        exact firstInteger
      · exact middleInduction entry middleMember
      · rw [secondEqual]
        exact secondInteger
      · exact rightInduction entry rightMember

private theorem integer_match_upper_admitted (entry upper : IndexEntry)
    (target : Core.Value) (entryInteger : entry.IntegerValued)
    (upperInteger : upper.IntegerValued) (before : entry.ValueLe upper)
    (matched : entry.matchesValue target = true) :
    indexUpperAllows target upper = true := by
  rcases entryInteger with ⟨entryValue, entryEqual⟩
  rcases upperInteger with ⟨upperValue, upperEqual⟩
  unfold IndexEntry.ValueLe at before
  unfold IndexEntry.matchesValue at matched
  unfold indexUpperAllows
  simp only [entryEqual, upperEqual] at before matched ⊢
  cases target <;>
    simp [PhysicalQuery.sqlEquals, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass] at matched before ⊢
  case integer targetValue =>
    subst targetValue
    exact before

private theorem integer_match_lower_admitted (lower entry : IndexEntry)
    (target : Core.Value) (lowerInteger : lower.IntegerValued)
    (entryInteger : entry.IntegerValued) (after : lower.ValueLe entry)
    (matched : entry.matchesValue target = true) :
    indexLowerAllows (some lower) target = true := by
  rcases lowerInteger with ⟨lowerValue, lowerEqual⟩
  rcases entryInteger with ⟨entryValue, entryEqual⟩
  unfold IndexEntry.ValueLe at after
  unfold IndexEntry.matchesValue at matched
  unfold indexLowerAllows
  simp only [lowerEqual, entryEqual] at after matched ⊢
  cases target <;>
    simp [PhysicalQuery.sqlEquals, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass] at matched after ⊢
  case integer targetValue =>
    subst targetValue
    exact after

theorem AbstractIndexTree.IntegerOrdered.wellRouted
    {tree : AbstractIndexTree} (valid : tree.IntegerOrdered) :
    tree.WellRouted := by
  induction valid with
  | leaf entries integers =>
      exact AbstractIndexTree.WellRouted.leaf entries
  | branch2 left right separator leftValid rightValid separatorInteger
      leftBefore rightAfter leftInduction rightInduction =>
      apply AbstractIndexTree.WellRouted.branch2 left right separator
        leftInduction rightInduction
      · intro target entry member matched
        exact integer_match_upper_admitted entry separator target
          (leftValid.allInteger entry member) separatorInteger
          (leftBefore entry member) matched
      · intro target entry member matched
        exact integer_match_lower_admitted separator entry target
          separatorInteger (rightValid.allInteger entry member)
          (rightAfter entry member) matched
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid firstInteger secondInteger leftBefore middleAfter
      middleBefore rightAfter leftInduction middleInduction rightInduction =>
      apply AbstractIndexTree.WellRouted.branch3 left middle right
        firstSeparator secondSeparator
        leftInduction middleInduction rightInduction
      · intro target entry member matched
        exact integer_match_upper_admitted entry firstSeparator target
          (leftValid.allInteger entry member) firstInteger
          (leftBefore entry member) matched
      · intro target entry member matched
        have lower := integer_match_lower_admitted firstSeparator entry target
          firstInteger (middleValid.allInteger entry member)
          (middleAfter entry member) matched
        have upper := integer_match_upper_admitted entry secondSeparator target
          (middleValid.allInteger entry member) secondInteger
          (middleBefore entry member) matched
        simp [lower, upper]
      · intro target entry member matched
        exact integer_match_lower_admitted secondSeparator entry target
          secondInteger (rightValid.allInteger entry member)
          (rightAfter entry member) matched

def IndexEntry.TextValued (entry : IndexEntry) : Prop :=
  ∃ value : PhysicalCodec.Text, entry.value = .text value

private theorem text_match_upper_admitted (entry upper : IndexEntry)
    (target : Core.Value) (entryText : entry.TextValued)
    (upperText : upper.TextValued) (before : entry.ValueLe upper)
    (matched : entry.matchesValue target = true) :
    indexUpperAllows target upper = true := by
  rcases entryText with ⟨entryValue, entryEqual⟩
  rcases upperText with ⟨upperValue, upperEqual⟩
  unfold IndexEntry.ValueLe at before
  unfold IndexEntry.matchesValue at matched
  unfold indexUpperAllows
  simp only [entryEqual, upperEqual] at before matched ⊢
  cases target <;>
    simp [PhysicalQuery.sqlEquals, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass] at matched before ⊢
  case text targetValue =>
    subst targetValue
    exact before

private theorem text_match_lower_admitted (lower entry : IndexEntry)
    (target : Core.Value) (lowerText : lower.TextValued)
    (entryText : entry.TextValued) (after : lower.ValueLe entry)
    (matched : entry.matchesValue target = true) :
    indexLowerAllows (some lower) target = true := by
  rcases lowerText with ⟨lowerValue, lowerEqual⟩
  rcases entryText with ⟨entryValue, entryEqual⟩
  unfold IndexEntry.ValueLe at after
  unfold IndexEntry.matchesValue at matched
  unfold indexLowerAllows
  simp only [lowerEqual, entryEqual] at after matched ⊢
  cases target <;>
    simp [PhysicalQuery.sqlEquals, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass] at matched after ⊢
  case text targetValue =>
    subst targetValue
    exact after

/-- A generated all-TEXT index is routed exactly by the same promoted keys
that occur in its in-order abstraction.  The proof consumes the encoder's
pairwise byte ordering; no reopen-time scan is needed. -/
theorem AbstractIndexTree.wellRouted_of_pairwise_text
    (tree : AbstractIndexTree)
    (texts : ∀ entry ∈ tree.toList, entry.TextValued)
    (ordered : tree.toList.Pairwise IndexEntry.ValueLe) :
    tree.WellRouted := by
  induction tree with
  | leaf entries => exact .leaf entries
  | branch2 left separator right leftInduction rightInduction =>
      simp only [AbstractIndexTree.toList] at texts ordered
      have leftSeparatorRight := List.pairwise_append.mp ordered
      have leftSeparator := List.pairwise_append.mp leftSeparatorRight.1
      apply AbstractIndexTree.WellRouted.branch2 left right separator
      · apply leftInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact leftSeparator.1
      · apply rightInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact leftSeparatorRight.2.1
      · intro target entry member matched
        exact text_match_upper_admitted entry separator target
          (texts entry (by simp [member])) (texts separator (by simp))
          (leftSeparator.2.2 entry member separator (by simp)) matched
      · intro target entry member matched
        exact text_match_lower_admitted separator entry target
          (texts separator (by simp)) (texts entry (by simp [member]))
          (leftSeparatorRight.2.2 separator (by simp) entry member) matched
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [AbstractIndexTree.toList] at texts ordered
      have throughSecondRight := List.pairwise_append.mp ordered
      have throughMiddleSecond :=
        List.pairwise_append.mp throughSecondRight.1
      have leftFirstMiddle :=
        List.pairwise_append.mp throughMiddleSecond.1
      have leftFirst := List.pairwise_append.mp leftFirstMiddle.1
      apply AbstractIndexTree.WellRouted.branch3 left middle right
        firstSeparator secondSeparator
      · apply leftInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact leftFirst.1
      · apply middleInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact leftFirstMiddle.2.1
      · apply rightInduction
        · intro entry member
          exact texts entry (by simp [member])
        · exact throughSecondRight.2.1
      · intro target entry member matched
        exact text_match_upper_admitted entry firstSeparator target
          (texts entry (by simp [member])) (texts firstSeparator (by simp))
          (leftFirst.2.2 entry member firstSeparator (by simp)) matched
      · intro target entry member matched
        have lower := text_match_lower_admitted firstSeparator entry target
          (texts firstSeparator (by simp)) (texts entry (by simp [member]))
          (leftFirstMiddle.2.2 firstSeparator (by simp) entry member) matched
        have upper := text_match_upper_admitted entry secondSeparator target
          (texts entry (by simp [member])) (texts secondSeparator (by simp))
          (throughMiddleSecond.2.2 entry (by simp [member]) secondSeparator
            (by simp)) matched
        simp [lower, upper]
      · intro target entry member matched
        exact text_match_lower_admitted secondSeparator entry target
          (texts secondSeparator (by simp)) (texts entry (by simp [member]))
          (throughSecondRight.2.2 secondSeparator (by simp) entry member)
          matched

private theorem filter_matches_eq_nil_of_not_admitted
    (target : Core.Value) (entries : List IndexEntry) (allowed : Bool)
    (notAllowed : allowed = false)
    (admitted : ∀ entry, entry ∈ entries →
      entry.matchesValue target = true → allowed = true) :
    entries.filter (fun entry => entry.matchesValue target) = [] := by
  induction entries with
  | nil => rfl
  | cons entry entries induction =>
      have tailAdmitted : ∀ candidate, candidate ∈ entries →
          candidate.matchesValue target = true → allowed = true := by
        intro candidate member matched
        exact admitted candidate (by simp [member]) matched
      have tailEmpty := induction tailAdmitted
      by_cases matched : entry.matchesValue target = true
      · have contradiction := admitted entry (by simp) matched
        rw [notAllowed] at contradiction
        contradiction
      · simp [matched, tailEmpty]

theorem AbstractIndexTree.equalityCandidates_exact {tree : AbstractIndexTree}
    (valid : tree.WellRouted) (target : Core.Value) :
    (tree.equalityCandidates target).filter
        (fun entry => entry.matchesValue target) =
      tree.toList.filter (fun entry => entry.matchesValue target) := by
  induction valid with
  | leaf entries => rfl
  | branch2 left right separator leftValid rightValid leftAdmitted
      rightAdmitted leftInduction rightInduction =>
      have leftExact :
          ((if indexUpperAllows target separator then
              left.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            left.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : indexUpperAllows target separator with
        | true => simpa [allowed] using leftInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              left.toList _ allowed
              (fun entry member matched =>
                leftAdmitted target entry member matched)
            simp [allowed, empty]
      have rightExact :
          ((if indexLowerAllows (some separator) target then
              right.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            right.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : indexLowerAllows (some separator) target with
        | true => simpa [allowed] using rightInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              right.toList _ allowed
              (fun entry member matched =>
                rightAdmitted target entry member matched)
            simp [allowed, empty]
      simp only [AbstractIndexTree.equalityCandidates,
        AbstractIndexTree.toList, List.filter_append]
      rw [leftExact, rightExact]
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid leftAdmitted middleAdmitted rightAdmitted
      leftInduction middleInduction rightInduction =>
      have leftExact :
          ((if indexUpperAllows target firstSeparator then
              left.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            left.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : indexUpperAllows target firstSeparator with
        | true => simpa [allowed] using leftInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              left.toList _ allowed
              (fun entry member matched =>
                leftAdmitted target entry member matched)
            simp [allowed, empty]
      let middleAllowed := indexLowerAllows (some firstSeparator) target &&
        indexUpperAllows target secondSeparator
      have middleExact :
          ((if middleAllowed then middle.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            middle.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : middleAllowed with
        | true => simpa [middleAllowed, allowed] using middleInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              middle.toList middleAllowed allowed
              (fun entry member matched =>
                middleAdmitted target entry member matched)
            simp [middleAllowed, allowed, empty]
      have rightExact :
          ((if indexLowerAllows (some secondSeparator) target then
              right.equalityCandidates target else []).filter
              (fun entry => entry.matchesValue target)) =
            right.toList.filter (fun entry => entry.matchesValue target) := by
        cases allowed : indexLowerAllows (some secondSeparator) target with
        | true => simpa [allowed] using rightInduction
        | false =>
            have empty := filter_matches_eq_nil_of_not_admitted target
              right.toList _ allowed
              (fun entry member matched =>
                rightAdmitted target entry member matched)
            simp [allowed, empty]
      simp only [AbstractIndexTree.equalityCandidates,
        AbstractIndexTree.toList, List.filter_append]
      change _ = _
      rw [leftExact, middleExact, rightExact]

/-- Decode the exact binary 2-3 shape emitted by SQLeanite's persistent index
planner. Wider C SQLite nodes deliberately return `none` and retain the
validated fallback until the general-arity refinement is proved. -/
def decodeAbstractIndexTreeFrom (source : PageSource) :
    Nat → Nat → Option AbstractIndexTree
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeIndexInteriorFrom source page with
      | some ([(leftPage, separator)], rightPage) => do
          let left ← decodeAbstractIndexTreeFrom source fuel leftPage
          let right ← decodeAbstractIndexTreeFrom source fuel rightPage
          some (.branch2 left separator right)
      | some ([(leftPage, firstSeparator),
          (middlePage, secondSeparator)], rightPage) => do
          let left ← decodeAbstractIndexTreeFrom source fuel leftPage
          let middle ← decodeAbstractIndexTreeFrom source fuel middlePage
          let right ← decodeAbstractIndexTreeFrom source fuel rightPage
          some (.branch3 left firstSeparator middle secondSeparator right)
      | some _ => none
      | none => .leaf <$> decodeIndexLeafFrom source page

/-- Follow only the left edge of an index B-tree.  The same recursion is used
by the kernel-reducible proof target and the live pread reader. -/
def leftmostIndexLeafWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeInterior : List UInt8 →
      m (Option (List (Nat × IndexEntry) × Nat)))
    (decodeLeaf : List UInt8 → m (Option (List IndexEntry))) :
    Nat → Nat → m (Option (List IndexEntry))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      let interior ← decodeInterior page
      match interior with
      | some (first :: _, _) =>
          leftmostIndexLeafWith readPage decodeInterior decodeLeaf fuel first.1
      | some ([], _) => return none
      | none => decodeLeaf page

def leftmostIndexLeafFrom (source : PageSource) (fuel pageNumber : Nat) :
    Option (List IndexEntry) :=
  leftmostIndexLeafWith (m := Id) source.readPage
    (decodeIndexInteriorFrom source) (decodeIndexLeafFrom source)
    fuel pageNumber

/-- Read an in-order prefix across as many generated index leaves as needed.
Interior records are logical index entries in SQLite, so each separator is
emitted exactly once between the prefixes of its adjacent children. Recursion
stops as soon as `limit` entries have been obtained. -/
def indexPrefixWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeInterior : List UInt8 →
      m (Option (List (Nat × IndexEntry) × Nat)))
    (decodeLeaf : List UInt8 → m (Option (List IndexEntry))) :
    Nat → Nat → Nat → m (Option (List IndexEntry))
  | 0, _, _ => pure (some [])
  | _ + 1, 0, _ => pure none
  | limit + 1, fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      let interior ← decodeInterior page
      match interior with
      | some ([(leftPage, separator)], rightPage) => do
          let some left ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit + 1) fuel leftPage | return none
          if _leftFilled : left.length = limit + 1 then return some left
          let some right ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit - left.length) fuel rightPage | return none
          return some (left ++ [separator] ++ right)
      | some ([(leftPage, firstSeparator),
          (middlePage, secondSeparator)], rightPage) => do
          let some left ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit + 1) fuel leftPage | return none
          if _leftFilled : left.length = limit + 1 then return some left
          let some middle ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit - left.length) fuel middlePage | return none
          let beforeRight := left ++ [firstSeparator] ++ middle
          if _middleFilled : beforeRight.length = limit + 1 then
            return some beforeRight
          let some right ← indexPrefixWith readPage decodeInterior decodeLeaf
            (limit - beforeRight.length) fuel rightPage | return none
          return some (beforeRight ++ [secondSeparator] ++ right)
      | some _ => return none
      | none => return (← decodeLeaf page).map (List.take (limit + 1))

def indexPrefixFrom (source : PageSource) (limit fuel pageNumber : Nat) :
    Option (List IndexEntry) :=
  indexPrefixWith (m := Id) source.readPage
    (decodeIndexInteriorFrom source) (decodeIndexLeafFrom source)
    limit fuel pageNumber

theorem take_append_singleton_of_length_lt (left right : List α) (value : α)
    (limit : Nat) (short : left.length < limit) :
    (left ++ [value] ++ right).take limit =
      left ++ [value] ++ right.take (limit - left.length - 1) := by
  simp only [List.singleton_append, List.append_assoc]
  rw [List.take_append,
    List.take_of_length_le (Nat.le_of_lt short)]
  have remaining : 0 < limit - left.length := by omega
  cases difference : limit - left.length with
  | zero => omega
  | succ amount =>
      simp only [difference, List.take_succ_cons, List.singleton_append,
        Nat.succ_sub_one]

theorem AbstractIndexTree.cursorPrefix_eq_take (tree : AbstractIndexTree)
    (limit : Nat) :
    tree.cursorPrefix limit = tree.toList.take limit := by
  induction tree generalizing limit with
  | leaf entries =>
      cases limit <;>
        simp [AbstractIndexTree.cursorPrefix, AbstractIndexTree.toList]
  | branch2 left separator right leftInduction rightInduction =>
      cases limit with
      | zero => simp [AbstractIndexTree.cursorPrefix, AbstractIndexTree.toList]
      | succ amount =>
          simp only [AbstractIndexTree.cursorPrefix, leftInduction,
            AbstractIndexTree.toList, List.append_assoc]
          split
          next filled =>
            have long : amount + 1 ≤ left.toList.length := by
              simp only [List.length_take] at filled
              omega
            rw [List.take_append_of_le_length long]
          next notFilled =>
            have short : left.toList.length < amount + 1 := by
              simp only [List.length_take] at notFilled
              omega
            rw [List.take_of_length_le (Nat.le_of_lt short), rightInduction]
            have remaining : amount - left.toList.length =
                amount + 1 - left.toList.length - 1 := by omega
            rw [remaining]
            simpa only [List.append_assoc] using
              (take_append_singleton_of_length_lt left.toList right.toList
                separator (amount + 1) short).symm
  | branch3 left firstSeparator middle secondSeparator right leftInduction
      middleInduction rightInduction =>
      cases limit with
      | zero => simp [AbstractIndexTree.cursorPrefix, AbstractIndexTree.toList]
      | succ amount =>
          simp only [AbstractIndexTree.cursorPrefix, leftInduction,
            middleInduction, AbstractIndexTree.toList, List.append_assoc]
          split
          next filled =>
            have long : amount + 1 ≤ left.toList.length := by
              simp only [List.length_take] at filled
              omega
            rw [List.take_append_of_le_length long]
          next leftNotFilled =>
            have leftShort : left.toList.length < amount + 1 := by
              simp only [List.length_take] at leftNotFilled
              omega
            rw [List.take_of_length_le (Nat.le_of_lt leftShort)]
            let remaining := amount - left.toList.length
            split
            next middleFilled =>
              have middleLong : remaining ≤ middle.toList.length := by
                simp only [List.length_append, List.length_cons,
                  List.length_nil, List.length_take] at middleFilled
                dsimp [remaining]
                omega
              have firstTake := take_append_singleton_of_length_lt
                left.toList
                (middle.toList ++ [secondSeparator] ++ right.toList)
                firstSeparator (amount + 1) leftShort
              have remainingEq : amount + 1 - left.toList.length - 1 =
                  remaining := by
                dsimp [remaining]
                omega
              rw [remainingEq] at firstTake
              simp only [List.append_assoc] at firstTake
              rw [List.take_append_of_le_length middleLong] at firstTake
              dsimp [remaining] at middleLong ⊢
              simpa [List.append_assoc] using firstTake.symm
            next middleNotFilled =>
              have middleShort : middle.toList.length < remaining := by
                simp only [List.length_append, List.length_cons,
                  List.length_nil, List.length_take] at middleNotFilled
                dsimp [remaining]
                omega
              rw [List.take_of_length_le (Nat.le_of_lt middleShort),
                rightInduction]
              let beforeRight :=
                left.toList ++ [firstSeparator] ++ middle.toList
              have beforeShort : beforeRight.length < amount + 1 := by
                dsimp [beforeRight, remaining] at ⊢
                simp only [List.length_append, List.length_cons,
                  List.length_nil]
                omega
              have finalTake := take_append_singleton_of_length_lt
                beforeRight right.toList secondSeparator (amount + 1)
                beforeShort
              have finalRemaining : amount + 1 - beforeRight.length - 1 =
                  amount - beforeRight.length := by omega
              rw [finalRemaining] at finalTake
              dsimp [beforeRight, remaining] at finalTake ⊢
              simpa [List.append_assoc] using finalTake.symm

theorem indexPrefixFrom_decodeAbstract_cursor (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree) (limit : Nat),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      indexPrefixFrom source limit fuel pageNumber =
        some (tree.cursorPrefix limit)
  | 0, _, _, _, decoded => by
      simp [decodeAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, limit, decoded => by
      cases limit with
      | zero => simp [indexPrefixFrom, indexPrefixWith,
          AbstractIndexTree.cursorPrefix]
      | succ amount =>
          simp only [decodeAbstractIndexTreeFrom] at decoded
          cases pageResult : source.readPage pageNumber with
          | none => simp [pageResult] at decoded
          | some page =>
              simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
              cases interiorResult : decodeIndexInteriorFrom source page with
              | none =>
                  simp only [interiorResult] at decoded
                  cases leafResult : decodeIndexLeafFrom source page with
                  | none => simp [leafResult] at decoded
                  | some entries =>
                      rw [leafResult] at decoded
                      change some (.leaf entries) = some tree at decoded
                      injection decoded with equal
                      subst tree
                      simp [indexPrefixFrom, indexPrefixWith, pageResult,
                        interiorResult, leafResult,
                        AbstractIndexTree.cursorPrefix]
              | some interior =>
                  rcases interior with ⟨entries, rightPage⟩
                  simp only [interiorResult] at decoded
                  cases entries with
                  | nil => contradiction
                  | cons first rest =>
                      rcases first with ⟨leftPage, firstSeparator⟩
                      cases rest with
                      | nil =>
                          cases leftResult : decodeAbstractIndexTreeFrom source
                              fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases rightResult : decodeAbstractIndexTreeFrom
                                  source fuel rightPage with
                              | none => simp [rightResult] at decoded
                              | some right =>
                                  simp only [rightResult, Option.some.injEq]
                                    at decoded
                                  subst tree
                                  have leftCursor :=
                                    indexPrefixFrom_decodeAbstract_cursor source
                                      fuel leftPage left (amount + 1) leftResult
                                  simp only [indexPrefixFrom] at leftCursor
                                  have rightCursor := fun requested =>
                                    indexPrefixFrom_decodeAbstract_cursor source
                                      fuel rightPage right requested rightResult
                                  simp only [indexPrefixFrom] at rightCursor
                                  simp [indexPrefixFrom, indexPrefixWith,
                                    pageResult, interiorResult, leftCursor,
                                    rightCursor,
                                    AbstractIndexTree.cursorPrefix]
                                  split <;> simp_all
                      | cons second tail =>
                          rcases second with ⟨middlePage, secondSeparator⟩
                          cases tail with
                          | cons third remaining => contradiction
                          | nil =>
                              cases leftResult : decodeAbstractIndexTreeFrom
                                  source fuel leftPage with
                              | none => simp [leftResult] at decoded
                              | some left =>
                                  simp only [leftResult, Option.bind_eq_bind,
                                    Option.bind] at decoded
                                  cases middleResult :
                                      decodeAbstractIndexTreeFrom source fuel
                                        middlePage with
                                  | none => simp [middleResult] at decoded
                                  | some middle =>
                                      simp only [middleResult] at decoded
                                      cases rightResult :
                                          decodeAbstractIndexTreeFrom source fuel
                                            rightPage with
                                      | none => simp [rightResult] at decoded
                                      | some right =>
                                          simp only [rightResult,
                                            Option.some.injEq] at decoded
                                          subst tree
                                          have leftCursor :=
                                            indexPrefixFrom_decodeAbstract_cursor
                                              source fuel leftPage left
                                                (amount + 1) leftResult
                                          simp only [indexPrefixFrom] at leftCursor
                                          have middleCursor := fun requested =>
                                            indexPrefixFrom_decodeAbstract_cursor
                                              source fuel middlePage middle
                                                requested middleResult
                                          simp only [indexPrefixFrom] at middleCursor
                                          have rightCursor := fun requested =>
                                            indexPrefixFrom_decodeAbstract_cursor
                                              source fuel rightPage right
                                                requested rightResult
                                          simp only [indexPrefixFrom] at rightCursor
                                          simp [indexPrefixFrom, indexPrefixWith,
                                            pageResult, interiorResult,
                                            leftCursor, middleCursor,
                                            rightCursor,
                                            AbstractIndexTree.cursorPrefix]
                                          split
                                          next condition => simp [condition]
                                          next condition =>
                                            split <;> simp_all

theorem indexPrefixFrom_decodeAbstract_exact (source : PageSource)
    (limit fuel pageNumber : Nat) (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree) :
    indexPrefixFrom source limit fuel pageNumber =
      some (tree.toList.take limit) := by
  rw [indexPrefixFrom_decodeAbstract_cursor source fuel pageNumber tree limit
    decoded, tree.cursorPrefix_eq_take]

theorem leftmostIndexLeafFrom_decodeAbstract (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      leftmostIndexLeafFrom source fuel pageNumber = some tree.leftmostLeaf
  | 0, _, _, decoded => by simp [decodeAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractIndexTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeIndexLeafFrom source page with
              | none => simp [leafResult] at decoded
              | some entries =>
                  rw [leafResult] at decoded
                  change some (.leaf entries) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [leftmostIndexLeafFrom, leftmostIndexLeafWith,
                    pageResult, interiorResult, leafResult,
                    AbstractIndexTree.leftmostLeaf]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractIndexTreeFrom source fuel
                          leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractIndexTreeFrom source
                              fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftLeaf := leftmostIndexLeafFrom_decodeAbstract
                                source fuel leftPage left leftResult
                              simpa [leftmostIndexLeafFrom,
                                leftmostIndexLeafWith, pageResult,
                                interiorResult, leftLeaf,
                                AbstractIndexTree.leftmostLeaf] using leftLeaf
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractIndexTreeFrom source
                              fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractIndexTreeFrom
                                  source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult : decodeAbstractIndexTreeFrom
                                      source fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult,
                                        Option.some.injEq] at decoded
                                      subst tree
                                      have leftLeaf :=
                                        leftmostIndexLeafFrom_decodeAbstract source
                                          fuel leftPage left leftResult
                                      simpa [leftmostIndexLeafFrom,
                                        leftmostIndexLeafWith, pageResult,
                                        interiorResult, leftLeaf,
                                        AbstractIndexTree.leftmostLeaf] using
                                          leftLeaf

def lookupIndexPrefixFrom (source : PageSource) (limit fuel pageNumber : Nat) :
    Option (List IndexEntry) := do
  let leaf ← leftmostIndexLeafFrom source fuel pageNumber
  if limit ≤ leaf.length then some (leaf.take limit) else none

theorem lookupIndexPrefixFrom_decodeAbstract_exact (source : PageSource)
    (limit fuel pageNumber : Nat) (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (fits : limit ≤ tree.leftmostLeaf.length) :
    lookupIndexPrefixFrom source limit fuel pageNumber =
      some (tree.toList.take limit) := by
  unfold lookupIndexPrefixFrom
  rw [leftmostIndexLeafFrom_decodeAbstract source fuel pageNumber tree decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  simp [fits, tree.take_toList_eq_take_leftmostLeaf limit fits]

/-- Fold an arbitrary SQLite interior-page fanout into the binary promoted-key
abstraction. This changes only proof topology: in-order contents still contain
each interior record exactly once. -/
def AbstractIndexTree.branchChain
    (groups : List (AbstractIndexTree × IndexEntry))
    (right : AbstractIndexTree) : AbstractIndexTree :=
  groups.foldr (fun group suffix => .branch2 group.1 group.2 suffix) right

theorem AbstractIndexTree.branchChain_toList
    (groups : List (AbstractIndexTree × IndexEntry))
    (right : AbstractIndexTree) :
    (AbstractIndexTree.branchChain groups right).toList =
      (groups.map fun group => group.1.toList ++ [group.2]).flatten ++
        right.toList := by
  induction groups with
  | nil => rfl
  | cons group groups induction =>
      unfold AbstractIndexTree.branchChain at induction ⊢
      simp only [List.foldr, AbstractIndexTree.toList, List.map_cons,
        List.flatten_cons]
      rw [induction]
      simp [List.append_assoc]

def decodeIndexGroupWith {α : Type} (decodeChild : Nat → Option α)
    (entry : Nat × IndexEntry) : Option (α × IndexEntry) := do
  let child ← decodeChild entry.1
  some (child, entry.2)

def decodeFlatIndexGroupFrom (source : PageSource) (fuel : Nat)
    (entry : Nat × IndexEntry) : Option (List IndexEntry) := do
  let child ← decodeIndexSubtreeFrom source fuel entry.1
  some (child ++ [entry.2])

/-- General-arity proof decoder for C-produced SQLite index pages. Generated
pages continue to use `decodeAbstractIndexTreeFrom`, whose exact structural
refinement is stronger. Reopen validation compares this tree's complete
in-order contents with the decoded logical index before retaining it. -/
def decodeWideAbstractIndexTreeFrom (source : PageSource) :
    Nat → Nat → Option AbstractIndexTree
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeIndexInteriorFrom source page with
      | some ([], _) => none
      | some (entries, rightPage) => do
          let groups ← entries.mapM (decodeIndexGroupWith
            (decodeWideAbstractIndexTreeFrom source fuel))
          let right ← decodeWideAbstractIndexTreeFrom source fuel rightPage
          some (AbstractIndexTree.branchChain groups right)
      | none => .leaf <$> decodeIndexLeafFrom source page

private theorem decodeWideGroups_toList (source : PageSource) (fuel : Nat)
    (childRefines : ∀ pageNumber tree,
      decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree →
      decodeIndexSubtreeFrom source fuel pageNumber = some tree.toList) :
    ∀ (entries : List (Nat × IndexEntry))
      (groups : List (AbstractIndexTree × IndexEntry)),
      entries.mapM (decodeIndexGroupWith
        (decodeWideAbstractIndexTreeFrom source fuel)) = some groups →
      entries.mapM (decodeFlatIndexGroupFrom source fuel) =
        some (groups.map fun group => group.1.toList ++ [group.2])
  | [], groups, decoded => by
      simp only [List.mapM_nil, pure, Pure.pure, Option.some.injEq] at decoded
      subst groups
      rfl
  | entry :: entries, groups, decoded => by
      cases childResult : decodeWideAbstractIndexTreeFrom source fuel entry.1 with
      | none =>
          simp [List.mapM_cons, decodeIndexGroupWith,
            childResult] at decoded
      | some child =>
          simp only [List.mapM_cons] at decoded
          change (decodeIndexGroupWith
              (decodeWideAbstractIndexTreeFrom source fuel) entry >>=
            fun head => entries.mapM (decodeIndexGroupWith
              (decodeWideAbstractIndexTreeFrom source fuel)) >>= fun tail =>
                some (head :: tail)) = some groups at decoded
          simp only [decodeIndexGroupWith, childResult,
            Option.bind_eq_bind, Option.bind] at decoded
          cases tailResult : entries.mapM
              (decodeIndexGroupWith
                (decodeWideAbstractIndexTreeFrom source fuel)) with
          | none =>
              rw [tailResult] at decoded
              contradiction
          | some tail =>
              rw [tailResult] at decoded
              simp only [Option.bind_eq_bind, Option.bind,
                Option.some.injEq] at decoded
              subst groups
              have childDecoded := childRefines entry.1 child childResult
              have tailDecoded := decodeWideGroups_toList source fuel
                childRefines entries tail tailResult
              simp [List.mapM_cons, decodeFlatIndexGroupFrom,
                childDecoded, tailDecoded]

/-- The arbitrary-fanout abstract decoder is not merely validated against a
logical index after reopening: whenever it succeeds, its in-order abstraction
is exactly the ordinary complete physical index decode. -/
theorem decodeWideAbstractIndexTreeFrom_toList (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree →
      decodeIndexSubtreeFrom source fuel pageNumber = some tree.toList
  | 0, _, _, decoded => by
      simp [decodeWideAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeWideAbstractIndexTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeIndexLeafFrom source page with
              | none => simp [leafResult] at decoded
              | some entries =>
                  rw [leafResult] at decoded
                  change some (.leaf entries) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [decodeIndexSubtreeFrom, pageResult, interiorResult,
                    leafResult, AbstractIndexTree.toList]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  change ((first :: rest).mapM
                      (decodeIndexGroupWith
                        (decodeWideAbstractIndexTreeFrom source fuel)) >>=
                    fun groups =>
                    decodeWideAbstractIndexTreeFrom source fuel rightPage >>=
                      fun right => some
                        (AbstractIndexTree.branchChain groups right)) =
                    some tree at decoded
                  cases groupsResult : (first :: rest).mapM
                      (decodeIndexGroupWith
                        (decodeWideAbstractIndexTreeFrom source fuel)) with
                  | none =>
                      rw [groupsResult] at decoded
                      contradiction
                  | some groups =>
                      rw [groupsResult] at decoded
                      simp only [Option.bind_eq_bind, Option.bind] at decoded
                      cases rightResult : decodeWideAbstractIndexTreeFrom source
                          fuel rightPage with
                      | none =>
                          rw [rightResult] at decoded
                          contradiction
                      | some right =>
                          rw [rightResult] at decoded
                          simp only [Option.some.injEq] at decoded
                          subst tree
                          have rightDecoded :=
                            decodeWideAbstractIndexTreeFrom_toList source fuel
                              rightPage right rightResult
                          have groupsDecoded :
                              (first :: rest).mapM
                                (decodeFlatIndexGroupFrom source fuel) =
                                some (groups.map fun group =>
                                  group.1.toList ++ [group.2]) := by
                            exact decodeWideGroups_toList source fuel
                              (decodeWideAbstractIndexTreeFrom_toList source fuel)
                              (first :: rest) groups groupsResult
                          simp only [decodeIndexSubtreeFrom, pageResult,
                            Option.bind_eq_bind, Option.bind, interiorResult]
                          change ((first :: rest).mapM
                              (decodeFlatIndexGroupFrom source fuel) >>=
                            fun decodedGroups =>
                            decodeIndexSubtreeFrom source fuel rightPage >>=
                              fun decodedRight =>
                                some (decodedGroups.flatten ++ decodedRight)) =
                            some (AbstractIndexTree.branchChain groups right).toList
                          rw [groupsDecoded, rightDecoded]
                          simp [AbstractIndexTree.branchChain_toList]

/-- Pages emitted from a refined balanced index plan decode to the same
promoted-key topology under the proof-oriented abstract decoder. Unlike the
flat decoder theorem, this retains the child boundaries needed by directed
lookups. -/
theorem decodeAbstractIndexTreeFrom_encodePagesFrom (source : PageSource) :
    ∀ (plan : RecursivePageBTree.IndexPlan) (start : Nat)
      (pages : List CoreFile.Page) (entries : List IndexEntry) (fuel : Nat),
      plan.encodePagesFrom start = some pages →
      ReadsPagesFrom source start pages →
      plan.Balanced →
      IndexPlanDecodes source (source.pageCount + 1) plan entries →
      plan.height < fuel →
      ∃ tree, decodeAbstractIndexTreeFrom source fuel start = some tree ∧
        tree.toList = entries
  | .leaf cells, start, pages, entries, fuel, encoded, reads, _, refined,
      fuelBound => by
      simp only [RecursivePageBTree.IndexPlan.encodePagesFrom,
        Option.bind_eq_bind, Option.bind] at encoded
      cases pageResult : CoreFile.indexLeafPage? cells with
      | none => simp [pageResult] at encoded
      | some page =>
        simp only [pageResult, Option.some.injEq] at encoded
        subst pages
        cases refined with
        | leaf decoded =>
          have rootRead : source.readPage start = some page.bytes := by
            have available := reads 0 (by simp)
            simpa using available
          cases fuel with
          | zero => simp [RecursivePageBTree.IndexPlan.height] at fuelBound
          | succ childFuel =>
            refine ⟨.leaf entries, ?_, by
              simp [AbstractIndexTree.toList]⟩
            simp only [decodeAbstractIndexTreeFrom]
            rw [rootRead]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [decodeIndexInteriorFrom_indexLeafPage source pageResult]
            rw [decodeIndexLeafFrom_indexLeafPage source decoded pageResult]
            rfl
  | .branch2 left separator right, start, pages, entries, fuel, encoded,
      reads, balanced, refined, fuelBound => by
      simp only [RecursivePageBTree.IndexPlan.encodePagesFrom,
        Option.bind_eq_bind, Option.bind] at encoded
      let leftStart := start + 1
      let rightStart := leftStart + left.pageCount
      cases rootResult : RecursivePageBTree.indexInteriorPage?
          [(leftStart, separator)] rightStart with
      | none => simp [leftStart, rightStart, rootResult] at encoded
      | some root =>
        simp only [leftStart, rightStart, rootResult] at encoded
        cases leftResult : left.encodePagesFrom (start + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases rightResult : right.encodePagesFrom
              (start + 1 + left.pageCount) with
          | none => simp [rightResult] at encoded
          | some rightPages =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst pages
            cases refined with
            | branch2 leftDecoded separatorDecoded rightDecoded =>
              rename_i leftEntries separatorEntry rightEntries
              simp only [RecursivePageBTree.IndexPlan.Balanced] at balanced
              rcases balanced with
                ⟨leftBalanced, rightBalanced, heightEqual⟩
              have rootRead : source.readPage start = some root.bytes := by
                have available := reads 0 (by simp)
                simpa using available
              have childrenReads : ReadsPagesFrom source leftStart
                  (leftPages ++ rightPages) := by
                have remaining := ReadsPagesFrom.right
                  (left := [root]) (right := leftPages ++ rightPages) reads
                simpa [leftStart] using remaining
              have leftReads : ReadsPagesFrom source leftStart leftPages :=
                ReadsPagesFrom.left childrenReads
              have leftLength :=
                RecursivePageBTree.IndexPlan.encodePagesFrom_length leftResult
              have rightReads : ReadsPagesFrom source rightStart rightPages := by
                have remaining := ReadsPagesFrom.right childrenReads
                simpa [rightStart, leftStart, leftLength] using remaining
              cases fuel with
              | zero =>
                simp [RecursivePageBTree.IndexPlan.height] at fuelBound
              | succ childFuel =>
                have leftFuel : left.height < childFuel := by
                  simp only [RecursivePageBTree.IndexPlan.height] at fuelBound
                  omega
                have rightFuel : right.height < childFuel := by
                  rw [← heightEqual]
                  exact leftFuel
                rcases decodeAbstractIndexTreeFrom_encodePagesFrom source left
                    leftStart leftPages _ childFuel leftResult leftReads
                    leftBalanced leftDecoded leftFuel with
                  ⟨leftTree, leftExact, leftContents⟩
                rcases decodeAbstractIndexTreeFrom_encodePagesFrom source right
                    rightStart rightPages _ childFuel rightResult rightReads
                    rightBalanced rightDecoded rightFuel with
                  ⟨rightTree, rightExact, rightContents⟩
                refine ⟨.branch2 leftTree separatorEntry rightTree, ?_, ?_⟩
                · simp only [decodeAbstractIndexTreeFrom]
                  rw [rootRead]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [decodeIndexInteriorFrom_indexInteriorPage_one source
                    separatorDecoded rootResult]
                  simp only [Option.bind_eq_bind, Option.bind]
                  rw [leftExact, rightExact]
                · simp [AbstractIndexTree.toList, leftContents,
                    rightContents]
  | .branch3 left firstSeparator middle secondSeparator right, start, pages,
      entries, fuel, encoded, reads, balanced, refined, fuelBound => by
      simp only [RecursivePageBTree.IndexPlan.encodePagesFrom,
        Option.bind_eq_bind, Option.bind] at encoded
      let leftStart := start + 1
      let middleStart := leftStart + left.pageCount
      let rightStart := middleStart + middle.pageCount
      cases rootResult : RecursivePageBTree.indexInteriorPage?
          [(leftStart, firstSeparator), (middleStart, secondSeparator)]
          rightStart with
      | none =>
        simp [leftStart, middleStart, rightStart, rootResult] at encoded
      | some root =>
        simp only [leftStart, middleStart, rightStart, rootResult] at encoded
        cases leftResult : left.encodePagesFrom (start + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases middleResult : middle.encodePagesFrom
              (start + 1 + left.pageCount) with
          | none => simp [middleResult] at encoded
          | some middlePages =>
            simp only [middleResult] at encoded
            cases rightResult : right.encodePagesFrom
                (start + 1 + left.pageCount + middle.pageCount) with
            | none => simp [rightResult] at encoded
            | some rightPages =>
              simp only [rightResult, Option.some.injEq] at encoded
              subst pages
              cases refined with
              | branch3 leftDecoded firstDecoded middleDecoded secondDecoded
                  rightDecoded =>
                rename_i leftEntries firstEntry middleEntries secondEntry
                  rightEntries
                simp only [RecursivePageBTree.IndexPlan.Balanced] at balanced
                rcases balanced with
                  ⟨leftBalanced, middleBalanced, rightBalanced,
                    leftMiddleHeight, middleRightHeight⟩
                have rootRead : source.readPage start = some root.bytes := by
                  have available := reads 0 (by simp)
                  simpa using available
                have childrenReads : ReadsPagesFrom source leftStart
                    (leftPages ++ (middlePages ++ rightPages)) := by
                  have normalized : ReadsPagesFrom source start
                      ([root] ++ (leftPages ++ (middlePages ++ rightPages))) := by
                    simpa [List.append_assoc] using reads
                  have remaining := ReadsPagesFrom.right
                    (left := [root])
                    (right := leftPages ++ (middlePages ++ rightPages))
                    normalized
                  simpa [leftStart, List.append_assoc] using remaining
                have leftReads : ReadsPagesFrom source leftStart leftPages :=
                  ReadsPagesFrom.left childrenReads
                have afterLeftReads : ReadsPagesFrom source
                    (leftStart + leftPages.length)
                    (middlePages ++ rightPages) :=
                  ReadsPagesFrom.right childrenReads
                have leftLength :=
                  RecursivePageBTree.IndexPlan.encodePagesFrom_length leftResult
                have middleReads : ReadsPagesFrom source middleStart
                    middlePages := by
                  have middlePrefix := ReadsPagesFrom.left afterLeftReads
                  simpa [middleStart, leftStart, leftLength] using middlePrefix
                have afterMiddleReads : ReadsPagesFrom source
                    (leftStart + leftPages.length + middlePages.length)
                    rightPages := ReadsPagesFrom.right afterLeftReads
                have middleLength :=
                  RecursivePageBTree.IndexPlan.encodePagesFrom_length
                    middleResult
                have rightReads : ReadsPagesFrom source rightStart
                    rightPages := by
                  simpa [rightStart, middleStart, leftLength, middleLength,
                    Nat.add_assoc] using afterMiddleReads
                cases fuel with
                | zero =>
                  simp [RecursivePageBTree.IndexPlan.height] at fuelBound
                | succ childFuel =>
                  have leftFuel : left.height < childFuel := by
                    simp only [RecursivePageBTree.IndexPlan.height] at fuelBound
                    omega
                  have middleFuel : middle.height < childFuel := by
                    rw [← leftMiddleHeight]
                    exact leftFuel
                  have rightFuel : right.height < childFuel := by
                    rw [← middleRightHeight]
                    exact middleFuel
                  rcases decodeAbstractIndexTreeFrom_encodePagesFrom source left
                      leftStart leftPages _ childFuel leftResult leftReads
                      leftBalanced leftDecoded leftFuel with
                    ⟨leftTree, leftExact, leftContents⟩
                  rcases decodeAbstractIndexTreeFrom_encodePagesFrom source
                      middle middleStart middlePages _ childFuel middleResult
                      middleReads middleBalanced middleDecoded middleFuel with
                    ⟨middleTree, middleExact, middleContents⟩
                  rcases decodeAbstractIndexTreeFrom_encodePagesFrom source right
                      rightStart rightPages _ childFuel rightResult rightReads
                      rightBalanced rightDecoded rightFuel with
                    ⟨rightTree, rightExact, rightContents⟩
                  refine ⟨.branch3 leftTree firstEntry middleTree secondEntry
                    rightTree, ?_, ?_⟩
                  · simp only [decodeAbstractIndexTreeFrom]
                    rw [rootRead]
                    simp only [Option.bind_eq_bind, Option.bind]
                    rw [decodeIndexInteriorFrom_indexInteriorPage_two source
                      firstDecoded secondDecoded rootResult]
                    simp only [Option.bind_eq_bind, Option.bind]
                    rw [leftExact, middleExact, rightExact]
                  · simp [AbstractIndexTree.toList, leftContents,
                      middleContents, rightContents, List.append_assoc]

theorem decodeAbstractIndexTreeFrom_toList (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      decodeIndexSubtreeFrom source fuel pageNumber = some tree.toList
  | 0, _, _, decoded => by simp [decodeAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractIndexTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeIndexLeafFrom source page with
              | none => simp [leafResult] at decoded
              | some entries =>
                  rw [leafResult] at decoded
                  change some (.leaf entries) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [decodeIndexSubtreeFrom, pageResult, interiorResult,
                    leafResult, AbstractIndexTree.toList]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractIndexTreeFrom source fuel
                          leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractIndexTreeFrom source
                              fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftDecoded :=
                                decodeAbstractIndexTreeFrom_toList source fuel
                                  leftPage left leftResult
                              have rightDecoded :=
                                decodeAbstractIndexTreeFrom_toList source fuel
                                  rightPage right rightResult
                              simp [decodeIndexSubtreeFrom, pageResult,
                                interiorResult, leftDecoded, rightDecoded,
                                AbstractIndexTree.toList]
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractIndexTreeFrom source
                              fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractIndexTreeFrom
                                  source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult : decodeAbstractIndexTreeFrom
                                      source fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult, Option.some.injEq]
                                        at decoded
                                      subst tree
                                      have leftDecoded :=
                                        decodeAbstractIndexTreeFrom_toList source
                                          fuel leftPage left leftResult
                                      have middleDecoded :=
                                        decodeAbstractIndexTreeFrom_toList source
                                          fuel middlePage middle middleResult
                                      have rightDecoded :=
                                        decodeAbstractIndexTreeFrom_toList source
                                          fuel rightPage right rightResult
                                      simp [decodeIndexSubtreeFrom, pageResult,
                                        interiorResult, leftDecoded,
                                        middleDecoded, rightDecoded,
                                        AbstractIndexTree.toList,
                                        List.append_assoc]

/-- One equality traversal shared by the pure proof target and live IO reader.
Page acquisition and overflow decoding vary; interval routing, promoted
interior entries, and fuel accounting are definitionally the same code. -/
def indexValueCandidatesWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeInterior : List UInt8 →
      m (Option (List (Nat × IndexEntry) × Nat)))
    (decodeLeaf : List UInt8 → m (Option (List IndexEntry)))
    (target : Core.Value) : Nat → Nat → m (Option (List IndexEntry))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      let interior ← decodeInterior page
      match interior with
      | some (entries, rightmost) => do
          let lowers := none :: entries.map (fun entry => some entry.2)
          let groups ← (entries.zip lowers).mapM fun bounded => do
            let entry := bounded.1
            let lower := bounded.2
            let left ← if indexLowerAllows lower target &&
                indexUpperAllows target entry.2 then
              indexValueCandidatesWith readPage decodeInterior decodeLeaf target
                fuel entry.1
            else pure (some [])
            return left.map fun values => values ++ [entry.2]
          let visitRight := match entries.getLast? with
            | none => true
            | some entry => indexLowerAllows (some entry.2) target
          let right ← if visitRight then
            indexValueCandidatesWith readPage decodeInterior decodeLeaf target
              fuel rightmost
          else pure (some [])
          let some groups := sequenceOptions groups | return none
          let some right := right | return none
          return some (groups.flatten ++ right)
      | none => decodeLeaf page

/-- Page-directed equality traversal. Interior separators bound the child
subtrees by indexed value (inclusively because equal values are further ordered
by rowid), so unrelated children are never requested. The returned candidate
subtree is filtered separately below. -/
def indexValueCandidatesFrom (source : PageSource) (target : Core.Value)
    (fuel pageNumber : Nat) : Option (List IndexEntry) :=
  indexValueCandidatesWith (m := Id) source.readPage
    (decodeIndexInteriorFrom source) (decodeIndexLeafFrom source)
    target fuel pageNumber

def lookupIndexValueFrom (source : PageSource) (target : Core.Value)
    (fuel pageNumber : Nat) : Option (List IndexEntry) := do
  let candidates ← indexValueCandidatesFrom source target fuel pageNumber
  some (candidates.filter (fun entry => entry.matchesValue target))

/-- Every successful directed lookup contains only SQL-equal index entries.
Completeness is checked against the already validated index contents at the
live boundary until the interval proof is connected end to end. -/
theorem lookupIndexValueFrom_all_matches (source : PageSource)
    (target : Core.Value) (fuel pageNumber : Nat) (result : List IndexEntry)
    (success : lookupIndexValueFrom source target fuel pageNumber = some result) :
    result.all (fun entry => entry.matchesValue target) = true := by
  unfold lookupIndexValueFrom at success
  cases candidatesResult : indexValueCandidatesFrom source target fuel pageNumber with
  | none => simp [candidatesResult] at success
  | some candidates =>
      simp only [candidatesResult, Option.bind_eq_bind, Option.bind,
        Option.some.injEq] at success
      subst result
      simp [IndexEntry.matchesValue]

theorem indexValueCandidatesFrom_decodeAbstract (source : PageSource)
    (target : Core.Value) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      indexValueCandidatesFrom source target fuel pageNumber =
        some (tree.equalityCandidates target)
  | 0, _, _, decoded => by simp [decodeAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractIndexTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeIndexLeafFrom source page with
              | none => simp [leafResult] at decoded
              | some entries =>
                  rw [leafResult] at decoded
                  change some (.leaf entries) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [indexValueCandidatesFrom, indexValueCandidatesWith,
                    pageResult, interiorResult, leafResult,
                    AbstractIndexTree.equalityCandidates]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractIndexTreeFrom source fuel
                          leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractIndexTreeFrom source
                              fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftCandidates :=
                                indexValueCandidatesFrom_decodeAbstract source
                                  target fuel leftPage left leftResult
                              have rightCandidates :=
                                indexValueCandidatesFrom_decodeAbstract source
                                  target fuel rightPage right rightResult
                              have leftWith : indexValueCandidatesWith (m := Id)
                                  source.readPage (decodeIndexInteriorFrom source)
                                  (decodeIndexLeafFrom source) target fuel leftPage =
                                    some (left.equalityCandidates target) := by
                                simpa [indexValueCandidatesFrom] using
                                  leftCandidates
                              have rightWith : indexValueCandidatesWith (m := Id)
                                  source.readPage (decodeIndexInteriorFrom source)
                                  (decodeIndexLeafFrom source) target fuel rightPage =
                                    some (right.equalityCandidates target) := by
                                simpa [indexValueCandidatesFrom] using
                                  rightCandidates
                              have lowerNone :
                                  indexLowerAllows none target = true := by
                                cases target <;> rfl
                              by_cases leftAllowed :
                                indexUpperAllows target firstSeparator = true
                              <;> by_cases rightAllowed :
                                indexLowerAllows (some firstSeparator) target =
                                  true
                              <;> simp [indexValueCandidatesFrom,
                                indexValueCandidatesWith, pageResult,
                                interiorResult, leftWith, rightWith,
                                AbstractIndexTree.equalityCandidates,
                                leftAllowed, rightAllowed, sequenceOptions,
                                lowerNone, List.append_assoc]
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractIndexTreeFrom source
                              fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractIndexTreeFrom
                                  source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult : decodeAbstractIndexTreeFrom
                                      source fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult, Option.some.injEq]
                                        at decoded
                                      subst tree
                                      have leftCandidates :=
                                        indexValueCandidatesFrom_decodeAbstract
                                          source target fuel leftPage left
                                          leftResult
                                      have middleCandidates :=
                                        indexValueCandidatesFrom_decodeAbstract
                                          source target fuel middlePage middle
                                          middleResult
                                      have rightCandidates :=
                                        indexValueCandidatesFrom_decodeAbstract
                                          source target fuel rightPage right
                                          rightResult
                                      have leftWith : indexValueCandidatesWith
                                          (m := Id)
                                          source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) target fuel
                                          leftPage = some
                                            (left.equalityCandidates target) := by
                                        simpa [indexValueCandidatesFrom] using
                                          leftCandidates
                                      have middleWith : indexValueCandidatesWith
                                          (m := Id)
                                          source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) target fuel
                                          middlePage = some
                                            (middle.equalityCandidates target) := by
                                        simpa [indexValueCandidatesFrom] using
                                          middleCandidates
                                      have rightWith : indexValueCandidatesWith
                                          (m := Id)
                                          source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) target fuel
                                          rightPage = some
                                            (right.equalityCandidates target) := by
                                        simpa [indexValueCandidatesFrom] using
                                          rightCandidates
                                      have lowerNone :
                                          indexLowerAllows none target = true :=
                                        by cases target <;> rfl
                                      by_cases leftAllowed : indexUpperAllows
                                        target firstSeparator = true
                                      <;> by_cases middleLowerAllowed :
                                        indexLowerAllows (some firstSeparator)
                                          target = true
                                      <;> by_cases middleUpperAllowed :
                                        indexUpperAllows target
                                          secondSeparator = true
                                      <;> by_cases rightAllowed :
                                        indexLowerAllows (some secondSeparator)
                                          target = true
                                      <;> simp [indexValueCandidatesFrom,
                                        indexValueCandidatesWith, pageResult,
                                        interiorResult, leftWith,
                                        middleWith, rightWith,
                                        AbstractIndexTree.equalityCandidates,
                                        leftAllowed, middleLowerAllowed,
                                        middleUpperAllowed, rightAllowed,
                                        lowerNone, sequenceOptions,
                                        List.append_assoc]

/-- Once the physical 2-3 tree decodes to a well-routed promoted-key tree,
directed equality lookup returns exactly the matching entries of that tree.
This removes the validating full scan from the theorem statement: every
interior record is part of the abstraction and every skipped subtree is
proved unable to contain a match. -/
theorem lookupIndexValueFrom_decodeAbstract_exact (source : PageSource)
    (target : Core.Value) (fuel pageNumber : Nat)
    (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (valid : tree.WellRouted) :
    lookupIndexValueFrom source target fuel pageNumber =
      some (tree.toList.filter (fun entry => entry.matchesValue target)) := by
  unfold lookupIndexValueFrom
  rw [indexValueCandidatesFrom_decodeAbstract source target fuel pageNumber tree
    decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [AbstractIndexTree.equalityCandidates_exact valid target]

/-- Byte-level refinement form of equality exactness.  Under the same decoded
routing certificate, the localized lookup agrees with filtering the complete
physical index decode. -/
theorem lookupIndexValueFrom_refines_full_decode (source : PageSource)
    (target : Core.Value) (fuel pageNumber : Nat)
    (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (valid : tree.WellRouted) :
    lookupIndexValueFrom source target fuel pageNumber =
      (decodeIndexSubtreeFrom source fuel pageNumber).map
        (List.filter (fun entry => entry.matchesValue target)) := by
  rw [lookupIndexValueFrom_decodeAbstract_exact source target fuel pageNumber
    tree decoded valid]
  rw [decodeAbstractIndexTreeFrom_toList source fuel pageNumber tree decoded]
  rfl

def IndexEntry.matchesRange (entry : IndexEntry)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) : Bool :=
  PhysicalQuery.sqlCompare operation entry.value target = .true

/-- Whether an index-value interval can contain a value satisfying a range
predicate. Bounds are inclusive because rowid is the secondary index key. -/
private def indexRangeMayMatch (operation : PhysicalQuery.Comparison)
    (lower upper : Option IndexEntry) (target : Core.Value) : Bool :=
  match target with
  | .realBits _ => true
  | _ => match operation with
      | .less => match lower with
          | none => true
          | some entry => PhysicalQuery.compareValue entry.value target == .lt
      | .lessEqual => match lower with
          | none => true
          | some entry => PhysicalQuery.compareValue entry.value target != .gt
      | .greater => match upper with
          | none => true
          | some entry => PhysicalQuery.compareValue entry.value target == .gt
      | .greaterEqual => match upper with
          | none => true
          | some entry => PhysicalQuery.compareValue entry.value target != .lt

def AbstractIndexTree.rangeCandidates
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    AbstractIndexTree → List IndexEntry
  | .leaf entries => entries
  | .branch2 left separator right =>
      (if indexRangeMayMatch operation none (some separator) target then
        left.rangeCandidates operation target else []) ++ [separator] ++
      (if indexRangeMayMatch operation (some separator) none target then
        right.rangeCandidates operation target else [])
  | .branch3 left firstSeparator middle secondSeparator right =>
      (if indexRangeMayMatch operation none (some firstSeparator) target then
        left.rangeCandidates operation target else []) ++ [firstSeparator] ++
      (if indexRangeMayMatch operation (some firstSeparator)
          (some secondSeparator) target then
        middle.rangeCandidates operation target else []) ++ [secondSeparator] ++
      (if indexRangeMayMatch operation (some secondSeparator) none target then
        right.rangeCandidates operation target else [])

/-- Range-routing validity is deliberately semantic.  For every comparison
and target, a child containing a matching entry must be admitted by the same
interval test used by the executable traversal. -/
inductive AbstractIndexTree.RangeWellRouted : AbstractIndexTree → Prop where
  | leaf (entries : List IndexEntry) : RangeWellRouted (.leaf entries)
  | branch2 (left right : AbstractIndexTree) (separator : IndexEntry)
      (leftValid : left.RangeWellRouted) (rightValid : right.RangeWellRouted)
      (leftAdmitted : ∀ operation target entry, entry ∈ left.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation none (some separator) target = true)
      (rightAdmitted : ∀ operation target entry, entry ∈ right.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation (some separator) none target = true) :
      RangeWellRouted (.branch2 left separator right)
  | branch3 (left middle right : AbstractIndexTree)
      (firstSeparator secondSeparator : IndexEntry)
      (leftValid : left.RangeWellRouted)
      (middleValid : middle.RangeWellRouted)
      (rightValid : right.RangeWellRouted)
      (leftAdmitted : ∀ operation target entry, entry ∈ left.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation none (some firstSeparator) target = true)
      (middleAdmitted : ∀ operation target entry, entry ∈ middle.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation (some firstSeparator)
          (some secondSeparator) target = true)
      (rightAdmitted : ∀ operation target entry, entry ∈ right.toList →
        entry.matchesRange operation target = true →
        indexRangeMayMatch operation (some secondSeparator) none target = true) :
      RangeWellRouted
        (.branch3 left firstSeparator middle secondSeparator right)

private theorem filter_range_eq_nil_of_not_admitted
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (entries : List IndexEntry) (allowed : Bool)
    (notAllowed : allowed = false)
    (admitted : ∀ entry, entry ∈ entries →
      entry.matchesRange operation target = true → allowed = true) :
    entries.filter (fun entry => entry.matchesRange operation target) = [] := by
  induction entries with
  | nil => rfl
  | cons entry entries induction =>
      have tailAdmitted : ∀ candidate, candidate ∈ entries →
          candidate.matchesRange operation target = true → allowed = true := by
        intro candidate member matched
        exact admitted candidate (by simp [member]) matched
      have tailEmpty := induction tailAdmitted
      by_cases matched : entry.matchesRange operation target = true
      · have contradiction := admitted entry (by simp) matched
        rw [notAllowed] at contradiction
        contradiction
      · simp [matched, tailEmpty]

theorem AbstractIndexTree.rangeCandidates_exact {tree : AbstractIndexTree}
    (valid : tree.RangeWellRouted) (operation : PhysicalQuery.Comparison)
    (target : Core.Value) :
    (tree.rangeCandidates operation target).filter
        (fun entry => entry.matchesRange operation target) =
      tree.toList.filter (fun entry => entry.matchesRange operation target) := by
  induction valid with
  | leaf entries => rfl
  | branch2 left right separator leftValid rightValid leftAdmitted
      rightAdmitted leftInduction rightInduction =>
      have leftExact :
          ((if indexRangeMayMatch operation none (some separator) target then
              left.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            left.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed :
            indexRangeMayMatch operation none (some separator) target with
        | true => simpa [allowed] using leftInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              left.toList _ allowed
              (fun entry member matched =>
                leftAdmitted operation target entry member matched)
            simp [allowed, empty]
      have rightExact :
          ((if indexRangeMayMatch operation (some separator) none target then
              right.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            right.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed :
            indexRangeMayMatch operation (some separator) none target with
        | true => simpa [allowed] using rightInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              right.toList _ allowed
              (fun entry member matched =>
                rightAdmitted operation target entry member matched)
            simp [allowed, empty]
      simp only [AbstractIndexTree.rangeCandidates,
        AbstractIndexTree.toList, List.filter_append]
      rw [leftExact, rightExact]
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid leftAdmitted middleAdmitted rightAdmitted
      leftInduction middleInduction rightInduction =>
      have leftExact :
          ((if indexRangeMayMatch operation none (some firstSeparator) target then
              left.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            left.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed : indexRangeMayMatch operation none
            (some firstSeparator) target with
        | true => simpa [allowed] using leftInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              left.toList _ allowed
              (fun entry member matched =>
                leftAdmitted operation target entry member matched)
            simp [allowed, empty]
      have middleExact :
          ((if indexRangeMayMatch operation (some firstSeparator)
              (some secondSeparator) target then
              middle.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            middle.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed : indexRangeMayMatch operation (some firstSeparator)
            (some secondSeparator) target with
        | true => simpa [allowed] using middleInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              middle.toList _ allowed
              (fun entry member matched =>
                middleAdmitted operation target entry member matched)
            simp [allowed, empty]
      have rightExact :
          ((if indexRangeMayMatch operation (some secondSeparator) none target then
              right.rangeCandidates operation target else []).filter
              (fun entry => entry.matchesRange operation target)) =
            right.toList.filter
              (fun entry => entry.matchesRange operation target) := by
        cases allowed : indexRangeMayMatch operation (some secondSeparator)
            none target with
        | true => simpa [allowed] using rightInduction
        | false =>
            have empty := filter_range_eq_nil_of_not_admitted operation target
              right.toList _ allowed
              (fun entry member matched =>
                rightAdmitted operation target entry member matched)
            simp [allowed, empty]
      simp only [AbstractIndexTree.rangeCandidates,
        AbstractIndexTree.toList, List.filter_append]
      rw [leftExact, middleExact, rightExact]

private theorem integer_range_upper_admitted (entry upper : IndexEntry)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (entryInteger : entry.IntegerValued)
    (upperInteger : upper.IntegerValued) (before : entry.ValueLe upper)
    (matched : entry.matchesRange operation target = true) :
    indexRangeMayMatch operation none (some upper) target = true := by
  rcases entryInteger with ⟨entryValue, entryEqual⟩
  rcases upperInteger with ⟨upperValue, upperEqual⟩
  unfold IndexEntry.ValueLe at before
  unfold IndexEntry.matchesRange at matched
  simp only [entryEqual, upperEqual] at before matched ⊢
  cases operation <;> cases target <;>
    simp [indexRangeMayMatch, entryEqual, upperEqual,
      PhysicalQuery.sqlCompare,
      PhysicalQuery.Comparison.holds, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass, Int.compare_eq_lt,
      Int.compare_eq_gt] at matched before ⊢
  all_goals first | exact matched | omega

private theorem integer_range_lower_admitted (lower entry : IndexEntry)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (lowerInteger : lower.IntegerValued)
    (entryInteger : entry.IntegerValued) (after : lower.ValueLe entry)
    (matched : entry.matchesRange operation target = true) :
    indexRangeMayMatch operation (some lower) none target = true := by
  rcases lowerInteger with ⟨lowerValue, lowerEqual⟩
  rcases entryInteger with ⟨entryValue, entryEqual⟩
  unfold IndexEntry.ValueLe at after
  unfold IndexEntry.matchesRange at matched
  simp only [lowerEqual, entryEqual] at after matched ⊢
  cases operation <;> cases target <;>
    simp [indexRangeMayMatch, lowerEqual, entryEqual,
      PhysicalQuery.sqlCompare,
      PhysicalQuery.Comparison.holds, PhysicalQuery.compareValue,
      PhysicalQuery.valueClass, Int.compare_eq_lt,
      Int.compare_eq_gt] at matched after ⊢
  all_goals first | exact matched | omega

private theorem integer_range_middle_admitted (lower entry upper : IndexEntry)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (lowerInteger : lower.IntegerValued)
    (entryInteger : entry.IntegerValued)
    (upperInteger : upper.IntegerValued)
    (after : lower.ValueLe entry) (before : entry.ValueLe upper)
    (matched : entry.matchesRange operation target = true) :
    indexRangeMayMatch operation (some lower) (some upper) target = true := by
  cases operation with
  | less =>
      exact integer_range_lower_admitted lower entry .less target
        lowerInteger entryInteger after matched
  | lessEqual =>
      exact integer_range_lower_admitted lower entry .lessEqual target
        lowerInteger entryInteger after matched
  | greater =>
      exact integer_range_upper_admitted entry upper .greater target
        entryInteger upperInteger before matched
  | greaterEqual =>
      exact integer_range_upper_admitted entry upper .greaterEqual target
        entryInteger upperInteger before matched

theorem AbstractIndexTree.IntegerOrdered.rangeWellRouted
    {tree : AbstractIndexTree} (valid : tree.IntegerOrdered) :
    tree.RangeWellRouted := by
  induction valid with
  | leaf entries integers =>
      exact AbstractIndexTree.RangeWellRouted.leaf entries
  | branch2 left right separator leftValid rightValid separatorInteger
      leftBefore rightAfter leftInduction rightInduction =>
      apply AbstractIndexTree.RangeWellRouted.branch2 left right separator
        leftInduction rightInduction
      · intro operation target entry member matched
        exact integer_range_upper_admitted entry separator operation target
          (leftValid.allInteger entry member) separatorInteger
          (leftBefore entry member) matched
      · intro operation target entry member matched
        exact integer_range_lower_admitted separator entry operation target
          separatorInteger (rightValid.allInteger entry member)
          (rightAfter entry member) matched
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid firstInteger secondInteger leftBefore middleAfter
      middleBefore rightAfter leftInduction middleInduction rightInduction =>
      apply AbstractIndexTree.RangeWellRouted.branch3 left middle right
        firstSeparator secondSeparator leftInduction middleInduction
        rightInduction
      · intro operation target entry member matched
        exact integer_range_upper_admitted entry firstSeparator operation target
          (leftValid.allInteger entry member) firstInteger
          (leftBefore entry member) matched
      · intro operation target entry member matched
        exact integer_range_middle_admitted firstSeparator entry secondSeparator
          operation target firstInteger
          (middleValid.allInteger entry member) secondInteger
          (middleAfter entry member) (middleBefore entry member) matched
      · intro operation target entry member matched
        exact integer_range_lower_admitted secondSeparator entry operation target
          secondInteger (rightValid.allInteger entry member)
          (rightAfter entry member) matched

/-- One range traversal shared by the pure proof target and live IO reader. -/
def indexRangeCandidatesWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeInterior : List UInt8 →
      m (Option (List (Nat × IndexEntry) × Nat)))
    (decodeLeaf : List UInt8 → m (Option (List IndexEntry)))
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    Nat → Nat → m (Option (List IndexEntry))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      let interior ← decodeInterior page
      match interior with
      | some (entries, rightmost) => do
          let lowers := none :: entries.map (fun entry => some entry.2)
          let groups ← (entries.zip lowers).mapM fun bounded => do
            let entry := bounded.1
            let lower := bounded.2
            let left ← if indexRangeMayMatch operation lower
                (some entry.2) target then
              indexRangeCandidatesWith readPage decodeInterior decodeLeaf
                operation target fuel entry.1
            else pure (some [])
            return left.map fun values => values ++ [entry.2]
          let lower := entries.getLast?.map (·.2)
          let right ← if indexRangeMayMatch operation lower none target then
            indexRangeCandidatesWith readPage decodeInterior decodeLeaf
              operation target fuel rightmost
          else pure (some [])
          let some groups := sequenceOptions groups | return none
          let some right := right | return none
          return some (groups.flatten ++ right)
      | none => decodeLeaf page

/-- Page-directed half-bounded range traversal over a persisted index. -/
def indexRangeCandidatesFrom (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) : Option (List IndexEntry) :=
  indexRangeCandidatesWith (m := Id) source.readPage
    (decodeIndexInteriorFrom source) (decodeIndexLeafFrom source)
    operation target fuel pageNumber

theorem indexRangeCandidatesFrom_decodeAbstract (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractIndexTree),
      decodeAbstractIndexTreeFrom source fuel pageNumber = some tree →
      indexRangeCandidatesFrom source operation target fuel pageNumber =
        some (tree.rangeCandidates operation target)
  | 0, _, _, decoded => by simp [decodeAbstractIndexTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractIndexTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeIndexLeafFrom source page with
              | none => simp [leafResult] at decoded
              | some entries =>
                  rw [leafResult] at decoded
                  change some (.leaf entries) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [indexRangeCandidatesFrom, indexRangeCandidatesWith,
                    pageResult, interiorResult, leafResult,
                    AbstractIndexTree.rangeCandidates]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractIndexTreeFrom source fuel
                          leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractIndexTreeFrom source
                              fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftCandidates :=
                                indexRangeCandidatesFrom_decodeAbstract source
                                  operation target fuel leftPage left leftResult
                              have rightCandidates :=
                                indexRangeCandidatesFrom_decodeAbstract source
                                  operation target fuel rightPage right rightResult
                              have leftWith : indexRangeCandidatesWith (m := Id)
                                  source.readPage (decodeIndexInteriorFrom source)
                                  (decodeIndexLeafFrom source) operation target
                                  fuel leftPage = some
                                    (left.rangeCandidates operation target) := by
                                simpa [indexRangeCandidatesFrom] using
                                  leftCandidates
                              have rightWith : indexRangeCandidatesWith (m := Id)
                                  source.readPage (decodeIndexInteriorFrom source)
                                  (decodeIndexLeafFrom source) operation target
                                  fuel rightPage = some
                                    (right.rangeCandidates operation target) := by
                                simpa [indexRangeCandidatesFrom] using
                                  rightCandidates
                              by_cases leftAllowed : indexRangeMayMatch operation
                                none (some firstSeparator) target = true
                              <;> by_cases rightAllowed :
                                indexRangeMayMatch operation
                                  (some firstSeparator) none target = true
                              <;> simp [indexRangeCandidatesFrom,
                                indexRangeCandidatesWith, pageResult,
                                interiorResult, leftWith, rightWith,
                                AbstractIndexTree.rangeCandidates,
                                leftAllowed, rightAllowed, sequenceOptions,
                                List.append_assoc]
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractIndexTreeFrom source
                              fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractIndexTreeFrom
                                  source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult : decodeAbstractIndexTreeFrom
                                      source fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult, Option.some.injEq]
                                        at decoded
                                      subst tree
                                      have leftCandidates :=
                                        indexRangeCandidatesFrom_decodeAbstract
                                          source operation target fuel leftPage
                                          left leftResult
                                      have middleCandidates :=
                                        indexRangeCandidatesFrom_decodeAbstract
                                          source operation target fuel middlePage
                                          middle middleResult
                                      have rightCandidates :=
                                        indexRangeCandidatesFrom_decodeAbstract
                                          source operation target fuel rightPage
                                          right rightResult
                                      have leftWith : indexRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) operation
                                          target fuel leftPage = some
                                            (left.rangeCandidates operation
                                              target) := by
                                        simpa [indexRangeCandidatesFrom] using
                                          leftCandidates
                                      have middleWith : indexRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) operation
                                          target fuel middlePage = some
                                            (middle.rangeCandidates operation
                                              target) := by
                                        simpa [indexRangeCandidatesFrom] using
                                          middleCandidates
                                      have rightWith : indexRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeIndexInteriorFrom source)
                                          (decodeIndexLeafFrom source) operation
                                          target fuel rightPage = some
                                            (right.rangeCandidates operation
                                              target) := by
                                        simpa [indexRangeCandidatesFrom] using
                                          rightCandidates
                                      by_cases leftAllowed :
                                        indexRangeMayMatch operation none
                                          (some firstSeparator) target = true
                                      <;> by_cases middleAllowed :
                                        indexRangeMayMatch operation
                                          (some firstSeparator)
                                          (some secondSeparator) target = true
                                      <;> by_cases rightAllowed :
                                        indexRangeMayMatch operation
                                          (some secondSeparator) none target =
                                            true
                                      <;> simp [indexRangeCandidatesFrom,
                                        indexRangeCandidatesWith, pageResult,
                                        interiorResult, leftWith, middleWith,
                                        rightWith,
                                        AbstractIndexTree.rangeCandidates,
                                        leftAllowed, middleAllowed, rightAllowed,
                                        sequenceOptions, List.append_assoc]

def lookupIndexRangeFrom (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) : Option (List IndexEntry) := do
  let candidates ←
    indexRangeCandidatesFrom source operation target fuel pageNumber
  some (candidates.filter (fun entry => entry.matchesRange operation target))

theorem lookupIndexRangeFrom_decodeAbstract_exact (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (valid : tree.RangeWellRouted) :
    lookupIndexRangeFrom source operation target fuel pageNumber =
      some (tree.toList.filter
        (fun entry => entry.matchesRange operation target)) := by
  unfold lookupIndexRangeFrom
  rw [indexRangeCandidatesFrom_decodeAbstract source operation target fuel
    pageNumber tree decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [AbstractIndexTree.rangeCandidates_exact valid operation target]

theorem lookupIndexRangeFrom_refines_full_decode (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) (tree : AbstractIndexTree)
    (decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree)
    (valid : tree.RangeWellRouted) :
    lookupIndexRangeFrom source operation target fuel pageNumber =
      (decodeIndexSubtreeFrom source fuel pageNumber).map
        (List.filter (fun entry => entry.matchesRange operation target)) := by
  rw [lookupIndexRangeFrom_decodeAbstract_exact source operation target fuel
    pageNumber tree decoded valid]
  rw [decodeAbstractIndexTreeFrom_toList source fuel pageNumber tree decoded]
  rfl

theorem lookupIndexRangeFrom_all_matches (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) (result : List IndexEntry)
    (success : lookupIndexRangeFrom source operation target fuel pageNumber =
      some result) :
    result.all (fun entry => entry.matchesRange operation target) = true := by
  unfold lookupIndexRangeFrom at success
  cases candidatesResult :
      indexRangeCandidatesFrom source operation target fuel pageNumber with
  | none => simp [candidatesResult] at success
  | some candidates =>
      simp only [candidatesResult, Option.bind_eq_bind, Option.bind,
        Option.some.injEq] at success
      subst result
      simp [IndexEntry.matchesRange]

def expectedIndexEntries (table : Core.Table) (index : Core.Index) :
    List IndexEntry :=
  (CoreFile.sortedIndexRows table index).map fun row =>
    ⟨row.value index.column, row.rowid⟩

theorem expectedIndexEntries_pairwise_valueLe (table : Core.Table)
    (index : Core.Index)
    (integers : CoreFile.indexValuesInteger table index = true) :
    (expectedIndexEntries table index).Pairwise IndexEntry.ValueLe := by
  unfold expectedIndexEntries
  rw [List.pairwise_map]
  change (CoreFile.sortedIndexRows table index).Pairwise (CoreFile.indexRowValueLe index)
  exact CoreFile.sortedIndexRows_pairwise_valueLe table index integers

theorem expectedIndexEntries_all_integer (table : Core.Table)
    (index : Core.Index)
    (integers : CoreFile.indexValuesInteger table index = true) :
    ∀ entry ∈ expectedIndexEntries table index, entry.IntegerValued := by
  intro entry member
  unfold expectedIndexEntries at member
  rcases List.mem_map.mp member with ⟨row, rowMember, rfl⟩
  have sourceMember : row ∈ table.rows :=
    (CoreFile.sortedIndexRows_perm table index).subset rowMember
  rcases (CoreFile.indexValuesInteger_iff table index).mp integers row
      sourceMember with ⟨value, valueEqual⟩
  exact ⟨value, valueEqual⟩

theorem expectedIndexEntries_pairwise_valueLe_text (table : Core.Table)
    (index : Core.Index)
    (texts : CoreFile.indexValuesText table index = true) :
    (expectedIndexEntries table index).Pairwise IndexEntry.ValueLe := by
  unfold expectedIndexEntries
  rw [List.pairwise_map]
  change (CoreFile.sortedIndexRows table index).Pairwise (CoreFile.indexRowValueLe index)
  exact CoreFile.sortedIndexRows_pairwise_valueLe_text table index texts

theorem expectedIndexEntries_all_text (table : Core.Table)
    (index : Core.Index)
    (texts : CoreFile.indexValuesText table index = true) :
    ∀ entry ∈ expectedIndexEntries table index, entry.TextValued := by
  intro entry member
  unfold expectedIndexEntries at member
  rcases List.mem_map.mp member with ⟨row, rowMember, rfl⟩
  have sourceMember : row ∈ table.rows :=
    (CoreFile.sortedIndexRows_perm table index).subset rowMember
  rcases (CoreFile.indexValuesText_iff table index).mp texts row
      sourceMember with ⟨value, valueEqual⟩
  exact ⟨value, valueEqual⟩

@[simp] theorem expectedIndexEntries_withoutIndexes (table : Core.Table)
    (index : Core.Index) :
    expectedIndexEntries table.withoutIndexes index =
      expectedIndexEntries table index := by
  unfold expectedIndexEntries CoreFile.sortedIndexRows
  simp [CoreFile.indexValuesInteger, CoreFile.indexValuesText,
    Core.Table.withoutIndexes_rows]

/-- A reopened index certificate ties the bytes, promoted-key topology,
routing invariant, and logical Core index contents together.  Constructing it
is a pure checked operation; consumers receive all premises required by the
localized exactness theorems as proof fields. -/
structure CertifiedIntegerIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree
  ordered : tree.IntegerOrdered
  contents : tree.toList = expected

structure CertifiedTextIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeAbstractIndexTreeFrom source fuel pageNumber = some tree
  routed : tree.WellRouted
  contents : tree.toList = expected

/-- Reopen-time certificate for general-arity SQLite index pages. It has the
same semantic payload as `CertifiedIntegerIndex`; only the decoder provenance
differs. -/
structure CertifiedWideIntegerIndex (source : PageSource)
    (fuel pageNumber : Nat) (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree
  ordered : tree.IntegerOrdered
  contents : tree.toList = expected

/-- General-arity TEXT indexes retain their promoted-key routing proof too.
Unlike `CertifiedAllValueIndex`, equality lookup can therefore discard every
unrelated subtree instead of filtering the complete retained abstraction. -/
structure CertifiedWideTextIndex (source : PageSource)
    (fuel pageNumber : Nat) (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree
  routed : tree.WellRouted
  contents : tree.toList = expected

/-- Exact reopen certificate for indexes whose storage classes do not satisfy
the INTEGER routing invariant. Queries filter the retained physical index
abstraction directly; this removes the duplicate logical-plan validation while
remaining deliberately conservative about mixed numeric interval pruning. -/
structure CertifiedAllValueIndex (source : PageSource)
    (fuel pageNumber : Nat) (expected : List IndexEntry) where
  tree : AbstractIndexTree
  decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber = some tree
  contents : tree.toList = expected

/-- The generated-page refinement constructs the same certificate that the
linear reopen validator checks, without requiring that scan. The hypotheses
are physical provenance and page-availability facts established by the bulk
encoder; `integers` is exactly the catalog marker condition. -/
theorem existsCertifiedIntegerIndex_of_encodeIndex (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (integers : CoreFile.indexValuesInteger table index = true) :
    Nonempty (CertifiedIntegerIndex source (source.pageCount + 1)
      rootPage (expectedIndexEntries table index)) := by
  unfold CoreOverflow.encodeIndex at encoded
  cases plansResult : CoreOverflow.indexPlans table index with
  | none => simp [plansResult] at encoded
  | some plans =>
    simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
    cases provisionalResult : CoreOverflow.provisionalIndexStore? plans with
    | none => simp [provisionalResult] at encoded
    | some provisional =>
      simp only [provisionalResult] at encoded
      cases resolvedResult : CoreOverflow.resolvePlans
          (rootPage + provisional.plan.pageCount) plans with
      | none => simp [resolvedResult] at encoded
      | some resolved =>
        simp only [resolvedResult] at encoded
        cases updatedResult : provisional.retarget? resolved.cells with
        | none => simp [updatedResult] at encoded
        | some topology =>
          simp only [updatedResult] at encoded
          cases treeResult : topology.plan.encodePagesFrom rootPage with
          | none => simp [treeResult] at encoded
          | some treePages =>
            simp only [treeResult, Option.some.injEq] at encoded
            subst encoding
            have treeReads : ReadsPagesFrom source rootPage treePages :=
              ReadsPagesFrom.left reads
            have treeLength :=
              RecursivePageBTree.IndexPlan.encodePagesFrom_length treeResult
            have pageCountEqual :=
              RecursivePageBTree.IndexStore.retarget?_pageCount updatedResult
            have overflowReads : ReadsPagesFrom source
                (rootPage + provisional.plan.pageCount) resolved.pages := by
              have remaining := ReadsPagesFrom.right reads
              simpa [CoreOverflow.IndexEncoding.pages, treeLength,
                pageCountEqual] using remaining
            have planned : (CoreFile.sortedIndexRows table index).mapM
                (CoreOverflow.indexCellPlan? index) = some plans := by
              simpa [CoreOverflow.indexPlans] using plansResult
            have cellsDecoded := indexCellsDecode_resolvePlans index source
              (source.pageCount + 1) (CoreFile.sortedIndexRows table index)
              plans (rootPage + provisional.plan.pageCount) resolved planned
              resolvedResult (by omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at pageBound
                omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at withinSource
                omega)
              overflowReads
            have cellsEqual :=
              RecursivePageBTree.IndexStore.retarget?_represents updatedResult
            have planCells : IndexCellsDecode source (source.pageCount + 1)
                topology.plan.toCells (expectedIndexEntries table index) := by
              rw [cellsEqual]
              simpa [expectedIndexEntries] using cellsDecoded
            have planDecoded := IndexPlanDecodes.of_cells topology.plan _ planCells
            have balanced := topology.balanced
            have heightBound : topology.plan.height < source.pageCount + 1 := by
              have heightPageCount := topology.plan.height_lt_pageCount
              simp only [CoreOverflow.IndexEncoding.pages,
                List.length_append] at withinSource
              omega
            rcases decodeAbstractIndexTreeFrom_encodePagesFrom source topology.plan
                rootPage treePages _ (source.pageCount + 1) treeResult treeReads
                balanced planDecoded heightBound with
              ⟨tree, decoded, contents⟩
            have allInteger : ∀ entry ∈ tree.toList,
                entry.IntegerValued := by
              intro entry member
              exact expectedIndexEntries_all_integer table index integers entry
                (by simpa [contents] using member)
            have ordered : tree.toList.Pairwise IndexEntry.ValueLe := by
              rw [contents]
              exact expectedIndexEntries_pairwise_valueLe table index integers
            exact ⟨⟨tree, decoded,
              AbstractIndexTree.IntegerOrdered.of_pairwise tree allInteger
                ordered,
              contents⟩⟩

/-- Generated TEXT pages carry the same no-scan equality certificate.  Their
ordering proof is lexicographic over the exact stored UTF-8 bytes. -/
theorem existsCertifiedTextIndex_of_encodeIndex (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (texts : CoreFile.indexValuesText table index = true) :
    Nonempty (CertifiedTextIndex source (source.pageCount + 1)
      rootPage (expectedIndexEntries table index)) := by
  unfold CoreOverflow.encodeIndex at encoded
  cases plansResult : CoreOverflow.indexPlans table index with
  | none => simp [plansResult] at encoded
  | some plans =>
    simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
    cases provisionalResult : CoreOverflow.provisionalIndexStore? plans with
    | none => simp [provisionalResult] at encoded
    | some provisional =>
      simp only [provisionalResult] at encoded
      cases resolvedResult : CoreOverflow.resolvePlans
          (rootPage + provisional.plan.pageCount) plans with
      | none => simp [resolvedResult] at encoded
      | some resolved =>
        simp only [resolvedResult] at encoded
        cases updatedResult : provisional.retarget? resolved.cells with
        | none => simp [updatedResult] at encoded
        | some topology =>
          simp only [updatedResult] at encoded
          cases treeResult : topology.plan.encodePagesFrom rootPage with
          | none => simp [treeResult] at encoded
          | some treePages =>
            simp only [treeResult, Option.some.injEq] at encoded
            subst encoding
            have treeReads : ReadsPagesFrom source rootPage treePages :=
              ReadsPagesFrom.left reads
            have treeLength :=
              RecursivePageBTree.IndexPlan.encodePagesFrom_length treeResult
            have pageCountEqual :=
              RecursivePageBTree.IndexStore.retarget?_pageCount updatedResult
            have overflowReads : ReadsPagesFrom source
                (rootPage + provisional.plan.pageCount) resolved.pages := by
              have remaining := ReadsPagesFrom.right reads
              simpa [CoreOverflow.IndexEncoding.pages, treeLength,
                pageCountEqual] using remaining
            have planned : (CoreFile.sortedIndexRows table index).mapM
                (CoreOverflow.indexCellPlan? index) = some plans := by
              simpa [CoreOverflow.indexPlans] using plansResult
            have cellsDecoded := indexCellsDecode_resolvePlans index source
              (source.pageCount + 1) (CoreFile.sortedIndexRows table index)
              plans (rootPage + provisional.plan.pageCount) resolved planned
              resolvedResult (by omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at pageBound
                omega)
              (by
                simp only [CoreOverflow.IndexEncoding.pages,
                  List.length_append] at withinSource
                omega)
              overflowReads
            have cellsEqual :=
              RecursivePageBTree.IndexStore.retarget?_represents updatedResult
            have planCells : IndexCellsDecode source (source.pageCount + 1)
                topology.plan.toCells (expectedIndexEntries table index) := by
              rw [cellsEqual]
              simpa [expectedIndexEntries] using cellsDecoded
            have planDecoded := IndexPlanDecodes.of_cells topology.plan _ planCells
            have heightBound : topology.plan.height < source.pageCount + 1 := by
              have heightPageCount := topology.plan.height_lt_pageCount
              simp only [CoreOverflow.IndexEncoding.pages,
                List.length_append] at withinSource
              omega
            rcases decodeAbstractIndexTreeFrom_encodePagesFrom source topology.plan
                rootPage treePages _ (source.pageCount + 1) treeResult treeReads
                topology.balanced planDecoded heightBound with
              ⟨tree, decoded, contents⟩
            have allText : ∀ entry ∈ tree.toList, entry.TextValued := by
              intro entry member
              exact expectedIndexEntries_all_text table index texts entry
                (by simpa [contents] using member)
            have ordered : tree.toList.Pairwise IndexEntry.ValueLe := by
              rw [contents]
              exact expectedIndexEntries_pairwise_valueLe_text table index texts
            exact ⟨⟨tree, decoded,
              AbstractIndexTree.wellRouted_of_pairwise_text tree allText ordered,
              contents⟩⟩

theorem lookupIndexValueFrom_text_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (texts : CoreFile.indexValuesText table index = true)
    (target : Core.Value) :
    lookupIndexValueFrom source target (source.pageCount + 1) rootPage =
      some ((expectedIndexEntries table index).filter
        (fun entry => entry.matchesValue target)) := by
  rcases existsCertifiedTextIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource texts with ⟨certificate⟩
  rw [lookupIndexValueFrom_decodeAbstract_exact source target
    (source.pageCount + 1) rootPage certificate.tree certificate.decoded
    certificate.routed]
  rw [certificate.contents]

theorem lookupIndexPrefixFrom_certified_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedIntegerIndex source fuel pageNumber expected)
    (limit : Nat) (result : List IndexEntry)
    (success : lookupIndexPrefixFrom source limit fuel pageNumber = some result) :
    result = expected.take limit := by
  unfold lookupIndexPrefixFrom at success
  rw [leftmostIndexLeafFrom_decodeAbstract source fuel pageNumber
    certificate.tree certificate.decoded] at success
  simp only [Option.bind_eq_bind, Option.bind] at success
  split at success
  next fits =>
    injection success with equal
    calc
      result = certificate.tree.leftmostLeaf.take limit := equal.symm
      _ = certificate.tree.toList.take limit :=
        (certificate.tree.take_toList_eq_take_leftmostLeaf limit fits).symm
      _ = expected.take limit := congrArg (List.take limit) certificate.contents
  next doesNotFit => contradiction

theorem lookupIndexPrefixFrom_text_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (texts : CoreFile.indexValuesText table index = true)
    (limit : Nat) (result : List IndexEntry)
    (success : lookupIndexPrefixFrom source limit (source.pageCount + 1)
      rootPage = some result) :
    result = (expectedIndexEntries table index).take limit := by
  rcases existsCertifiedTextIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource texts with ⟨certificate⟩
  unfold lookupIndexPrefixFrom at success
  rw [leftmostIndexLeafFrom_decodeAbstract source (source.pageCount + 1)
    rootPage certificate.tree certificate.decoded] at success
  simp only [Option.bind_eq_bind, Option.bind] at success
  split at success
  next fits =>
    injection success with equal
    calc
      result = certificate.tree.leftmostLeaf.take limit := equal.symm
      _ = certificate.tree.toList.take limit :=
        (certificate.tree.take_toList_eq_take_leftmostLeaf limit fits).symm
      _ = (expectedIndexEntries table index).take limit :=
        congrArg (List.take limit) certificate.contents
  next doesNotFit => contradiction

/-- The multi-leaf cursor has no first-leaf precondition: it stops after the
requested number of promoted-key entries across arbitrary generated height. -/
theorem indexPrefixFrom_text_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (texts : CoreFile.indexValuesText table index = true) (limit : Nat) :
    indexPrefixFrom source limit (source.pageCount + 1) rootPage =
      some ((expectedIndexEntries table index).take limit) := by
  rcases existsCertifiedTextIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource texts with ⟨certificate⟩
  rw [indexPrefixFrom_decodeAbstract_exact source limit
    (source.pageCount + 1) rootPage certificate.tree certificate.decoded]
  rw [certificate.contents]

def certifyIntegerIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) :
    Option (CertifiedIntegerIndex source fuel pageNumber expected) :=
  match decoded : decodeAbstractIndexTreeFrom source fuel pageNumber with
  | none => none
  | some tree =>
      match tree.certifyIntegerOrdered with
      | none => none
      | some certificate =>
          if contents : tree.toList = expected then
            some ⟨tree, decoded, certificate.valid, contents⟩
          else none

def certifyWideIntegerIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) :
    Option (CertifiedWideIntegerIndex source fuel pageNumber expected) :=
  match decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber with
  | none => none
  | some tree =>
      match tree.certifyIntegerOrdered with
      | none => none
      | some certificate =>
          if contents : tree.toList = expected then
            some ⟨tree, decoded, certificate.valid, contents⟩
          else none

def certifyWideTextIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) :
    Option (CertifiedWideTextIndex source fuel pageNumber expected) :=
  match decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber with
  | none => none
  | some tree =>
      if textsBool : tree.toList.all
          (fun entry => CoreFile.valueIsText entry.value) then
        have texts : ∀ entry ∈ tree.toList, entry.TextValued := by
          intro entry member
          have isText := (List.all_eq_true.mp textsBool) entry member
          cases valueEq : entry.value <;>
            simp [CoreFile.valueIsText, IndexEntry.TextValued, valueEq] at isText ⊢
        if ordered : tree.toList.Pairwise IndexEntry.ValueLe then
          if contents : tree.toList = expected then
            some ⟨tree, decoded,
              tree.wellRouted_of_pairwise_text texts ordered, contents⟩
          else none
        else none
      else none

def certifyAllValueIndex (source : PageSource) (fuel pageNumber : Nat)
    (expected : List IndexEntry) :
    Option (CertifiedAllValueIndex source fuel pageNumber expected) :=
  match decoded : decodeWideAbstractIndexTreeFrom source fuel pageNumber with
  | none => none
  | some tree =>
      if contents : tree.toList = expected then
        some ⟨tree, decoded, contents⟩
      else none

theorem lookupIndexValueFrom_certified_exact
    {source : PageSource} {fuel pageNumber : Nat}
    {expected : List IndexEntry}
    (certificate : CertifiedIntegerIndex source fuel pageNumber expected)
    (target : Core.Value) :
    lookupIndexValueFrom source target fuel pageNumber =
      some (expected.filter (fun entry => entry.matchesValue target)) := by
  rw [lookupIndexValueFrom_decodeAbstract_exact source target fuel pageNumber
    certificate.tree certificate.decoded certificate.ordered.wellRouted]
  rw [certificate.contents]

theorem lookupIndexRangeFrom_certified_exact
    {source : PageSource} {fuel pageNumber : Nat}
    {expected : List IndexEntry}
    (certificate : CertifiedIntegerIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    lookupIndexRangeFrom source operation target fuel pageNumber =
      some (expected.filter
        (fun entry => entry.matchesRange operation target)) := by
  rw [lookupIndexRangeFrom_decodeAbstract_exact source operation target fuel
    pageNumber certificate.tree certificate.decoded
    certificate.ordered.rangeWellRouted]
  rw [certificate.contents]

def CertifiedWideIntegerIndex.valueEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideIntegerIndex source fuel pageNumber expected)
    (target : Core.Value) : List IndexEntry :=
  (certificate.tree.equalityCandidates target).filter
    (fun entry => entry.matchesValue target)

theorem CertifiedWideIntegerIndex.valueEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideIntegerIndex source fuel pageNumber expected)
    (target : Core.Value) :
    certificate.valueEntries target =
      expected.filter (fun entry => entry.matchesValue target) := by
  unfold CertifiedWideIntegerIndex.valueEntries
  rw [AbstractIndexTree.equalityCandidates_exact
    certificate.ordered.wellRouted target, certificate.contents]

def CertifiedWideIntegerIndex.rangeEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideIntegerIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    List IndexEntry :=
  (certificate.tree.rangeCandidates operation target).filter
    (fun entry => entry.matchesRange operation target)

theorem CertifiedWideIntegerIndex.rangeEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideIntegerIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    certificate.rangeEntries operation target =
      expected.filter (fun entry => entry.matchesRange operation target) := by
  unfold CertifiedWideIntegerIndex.rangeEntries
  rw [AbstractIndexTree.rangeCandidates_exact
    certificate.ordered.rangeWellRouted operation target,
    certificate.contents]

def CertifiedWideTextIndex.valueEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideTextIndex source fuel pageNumber expected)
    (target : Core.Value) : List IndexEntry :=
  (certificate.tree.equalityCandidates target).filter
    (fun entry => entry.matchesValue target)

theorem CertifiedWideTextIndex.valueEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideTextIndex source fuel pageNumber expected)
    (target : Core.Value) :
    certificate.valueEntries target =
      expected.filter (fun entry => entry.matchesValue target) := by
  unfold CertifiedWideTextIndex.valueEntries
  rw [AbstractIndexTree.equalityCandidates_exact certificate.routed target,
    certificate.contents]

/-- Mixed range comparisons need the stronger range-routing relation.  Keep
the exact full-abstraction behavior for them; the TEXT equality fast path does
not weaken or assume that separate obligation. -/
def CertifiedWideTextIndex.rangeEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideTextIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    List IndexEntry :=
  certificate.tree.toList.filter
    (fun entry => entry.matchesRange operation target)

theorem CertifiedWideTextIndex.rangeEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedWideTextIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    certificate.rangeEntries operation target =
      expected.filter (fun entry => entry.matchesRange operation target) := by
  unfold CertifiedWideTextIndex.rangeEntries
  rw [certificate.contents]

def CertifiedAllValueIndex.valueEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedAllValueIndex source fuel pageNumber expected)
    (target : Core.Value) : List IndexEntry :=
  certificate.tree.toList.filter (fun entry => entry.matchesValue target)

theorem CertifiedAllValueIndex.valueEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedAllValueIndex source fuel pageNumber expected)
    (target : Core.Value) :
    certificate.valueEntries target =
      expected.filter (fun entry => entry.matchesValue target) := by
  unfold CertifiedAllValueIndex.valueEntries
  rw [certificate.contents]

def CertifiedAllValueIndex.rangeEntries
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedAllValueIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    List IndexEntry :=
  certificate.tree.toList.filter
    (fun entry => entry.matchesRange operation target)

theorem CertifiedAllValueIndex.rangeEntries_exact
    {source : PageSource} {fuel pageNumber : Nat} {expected : List IndexEntry}
    (certificate : CertifiedAllValueIndex source fuel pageNumber expected)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    certificate.rangeEntries operation target =
      expected.filter (fun entry => entry.matchesRange operation target) := by
  unfold CertifiedAllValueIndex.rangeEntries
  rw [certificate.contents]

/-- A directed equality lookup over generated INTEGER-index pages is exact
without running the linear certificate checker. -/
theorem lookupIndexValueFrom_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (integers : CoreFile.indexValuesInteger table index = true)
    (target : Core.Value) :
    lookupIndexValueFrom source target (source.pageCount + 1) rootPage =
      some ((expectedIndexEntries table index).filter
        (fun entry => entry.matchesValue target)) := by
  rcases existsCertifiedIntegerIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource integers with ⟨certificate⟩
  exact lookupIndexValueFrom_certified_exact certificate target

/-- The analogous exactness result for half-bounded range traversal. -/
theorem lookupIndexRangeFrom_encodeIndex_exact (source : PageSource)
    {rootPage : Nat} {table : Core.Table} {index : Core.Index}
    {encoding : CoreOverflow.IndexEncoding}
    (encoded : CoreOverflow.encodeIndex rootPage table index = some encoding)
    (reads : ReadsPagesFrom source rootPage encoding.pages)
    (rootPositive : 0 < rootPage)
    (pageBound : rootPage + encoding.pages.length < 2 ^ 32)
    (withinSource : rootPage + encoding.pages.length ≤ source.pageCount + 1)
    (integers : CoreFile.indexValuesInteger table index = true)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    lookupIndexRangeFrom source operation target (source.pageCount + 1)
        rootPage =
      some ((expectedIndexEntries table index).filter
        (fun entry => entry.matchesRange operation target)) := by
  rcases existsCertifiedIntegerIndex_of_encodeIndex source encoded reads
      rootPositive pageBound withinSource integers with ⟨certificate⟩
  exact lookupIndexRangeFrom_certified_exact certificate operation target

/-- Child page numbers of an interior table page: one per cell, then the
rightmost pointer. `none` when the page is not an interior table page. -/
def interiorChildren? (page : List UInt8) : Option (List Nat) := do
  if page.length == PhysicalCodec.pageSize then
    match page with
    | 5 :: _ :: _ :: countHigh :: countLow :: _ :: _ :: _ ::
        first :: second :: third :: fourth :: afterHeader => do
        let cellCount := decodeU16 countHigh countLow
        let rightmost := decodeU32 ⟨first, second, third, fourth⟩
        let offsets ← decodeOffsetList cellCount afterHeader
        let children ← offsets.mapM fun offset => do
          match (page.drop offset).take 4 with
          | [first, second, third, fourth] =>
              some (decodeU32 ⟨first, second, third, fourth⟩)
          | _ => none
        some (children ++ [rightmost])
    | _ => none
  else none

def interiorChildrenFor? (pageSize : Nat) (page : List UInt8) :
    Option (List Nat) := do
  if page.length == pageSize then
    match page with
    | 5 :: _ :: _ :: countHigh :: countLow :: _ :: _ :: _ ::
        first :: second :: third :: fourth :: afterHeader => do
        let cellCount := decodeU16 countHigh countLow
        let rightmost := decodeU32 ⟨first, second, third, fourth⟩
        let offsets ← decodeOffsetList cellCount afterHeader
        let children ← offsets.mapM fun offset => do
          match (page.drop offset).take 4 with
          | [first, second, third, fourth] =>
              some (decodeU32 ⟨first, second, third, fourth⟩)
          | _ => none
        some (children ++ [rightmost])
    | _ => none
  else none

/-- Decode table-interior routing cells as `(left child, greatest rowid in
that child)`, plus the rightmost child. Unlike index interiors, these keys are
separators rather than stored logical rows. -/
def decodeTableInterior? (page : List UInt8) :
    Option (List (Nat × Core.Integer) × Nat) := do
  if _pageLength : page.length = PhysicalCodec.pageSize then
    let (header, afterHeader) ← decodeBTreePageHeader page
    match header with
    | .interiorTable common rightmost => do
        let (offsets, _) ← decodeOffsets common.cellCount.val afterHeader
        let entries ← offsets.mapM fun offset => do
          if _bounded : offset < page.length then
            let (cell, _) ← decodeInteriorTableCell (page.drop offset)
            some (cell.leftChildPage.value.val, cell.key)
          else none
        some (entries, rightmost.val)
    | _ => none
  else none

def tableChildForRowid (entries : List (Nat × Core.Integer))
    (rightmost : Nat) (rowid : Core.Integer) : Nat :=
  match entries.find? (fun entry => decide (rowid.value ≤ entry.2.value)) with
  | some entry => entry.1
  | none => rightmost

/-- One traversal shared by the pure proof target and the live `IO` reader.
Only page acquisition and leaf/overflow decoding vary; interior classification,
separator comparison, fuel accounting, and row selection are identical. -/
def lookupTableRowidWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeLeaf : List UInt8 → m (Option (List Core.Row)))
    (target : Core.Integer) : Nat → Nat → m (Option (Option Core.Row))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      match decodeTableInterior? page with
      | some (entries, rightmost) =>
          lookupTableRowidWith readPage decodeLeaf target fuel
            (tableChildForRowid entries rightmost target)
      | none => do
          let some rows ← decodeLeaf page | return none
          return some (rows.find? fun row => row.rowid = target)

/-- Kernel-reducible pure specialization used by the encoder completeness
proof. -/
def lookupTableRowidFrom (schema : Core.Schema) (source : PageSource)
    (target : Core.Integer) (fuel pageNumber : Nat) : Option (Option Core.Row) :=
  lookupTableRowidWith (m := Id) source.readPage
    (decodeRowsFrom schema source) target fuel pageNumber

/-- Whether a table-child rowid interval can contain a primary-key match.
Table interior keys are inclusive upper bounds for the child on their left;
the preceding key is an exclusive lower bound.  The non-strict lower test for
`lessEqual` is intentionally conservative and can visit one boundary child,
but can never omit a matching row. -/
def tableRangeMayMatch (operation : PhysicalQuery.Comparison)
    (lower upper : Option Core.Integer) (target : Core.Integer) : Bool :=
  match operation with
  | .less => match lower with
      | none => true
      | some bound => decide (bound.value < target.value)
  | .lessEqual => match lower with
      | none => true
      | some bound => decide (bound.value ≤ target.value)
  | .greater => match upper with
      | none => true
      | some bound => decide (target.value < bound.value)
  | .greaterEqual => match upper with
      | none => true
      | some bound => decide (target.value ≤ bound.value)

/-- One separator-directed table range traversal shared by the pure proof
target and the live IO reader.  Interior separator records are routing data,
not logical table rows, so unlike index traversal they are not emitted. -/
def tableRangeCandidatesWith [Monad m]
    (readPage : Nat → m (Option (List UInt8)))
    (decodeLeaf : List UInt8 → m (Option (List Core.Row)))
    (operation : PhysicalQuery.Comparison) (target : Core.Integer) :
    Nat → Nat → m (Option (List Core.Row))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readPage pageNumber | return none
      match decodeTableInterior? page with
      | some (entries, rightmost) => do
          let lowers := none :: entries.map (fun entry => some entry.2)
          let groups ← (entries.zip lowers).mapM fun bounded => do
            let entry := bounded.1
            let lower := bounded.2
            if tableRangeMayMatch operation lower (some entry.2) target then
              tableRangeCandidatesWith readPage decodeLeaf operation target
                fuel entry.1
            else pure (some [])
          let lower := entries.getLast?.map (fun entry => entry.2)
          let right ← if tableRangeMayMatch operation lower none target then
            tableRangeCandidatesWith readPage decodeLeaf operation target
              fuel rightmost
          else pure (some [])
          let some groups := sequenceOptions groups | return none
          let some right := right | return none
          return some (groups.flatten ++ right)
      | none => decodeLeaf page

def tableRowMatchesRange (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) (row : Core.Row) : Bool :=
  PhysicalQuery.sqlCompare operation (.integer row.rowid) (.integer target) =
    .true

/-- Proof abstraction of the binary/ternary table topology emitted by the
persistent page store.  Table separator keys are not logical rows, so `toList`
contains only leaf contents. -/
inductive AbstractTableTree where
  | leaf (rows : List Core.Row)
  | branch2 (left : AbstractTableTree) (separator : Core.Integer)
      (right : AbstractTableTree)
  | branch3 (left : AbstractTableTree) (firstSeparator : Core.Integer)
      (middle : AbstractTableTree) (secondSeparator : Core.Integer)
      (right : AbstractTableTree)

def AbstractTableTree.toList : AbstractTableTree → List Core.Row
  | .leaf rows => rows
  | .branch2 left _ right => left.toList ++ right.toList
  | .branch3 left _ middle _ right =>
      left.toList ++ middle.toList ++ right.toList

def AbstractTableTree.rangeCandidates
    (operation : PhysicalQuery.Comparison) (target : Core.Integer) :
    AbstractTableTree → List Core.Row
  | .leaf rows => rows
  | .branch2 left separator right =>
      (if tableRangeMayMatch operation none (some separator) target then
        left.rangeCandidates operation target else []) ++
      (if tableRangeMayMatch operation (some separator) none target then
        right.rangeCandidates operation target else [])
  | .branch3 left firstSeparator middle secondSeparator right =>
      (if tableRangeMayMatch operation none (some firstSeparator) target then
        left.rangeCandidates operation target else []) ++
      (if tableRangeMayMatch operation (some firstSeparator)
          (some secondSeparator) target then
        middle.rangeCandidates operation target else []) ++
      (if tableRangeMayMatch operation (some secondSeparator) none target then
        right.rangeCandidates operation target else [])

/-- Every child containing a matching row is admitted by the executable
separator test.  This is a semantic routing invariant, not a claim that a
particular query happened to return the expected answer. -/
inductive AbstractTableTree.RangeWellRouted : AbstractTableTree → Prop where
  | leaf (rows : List Core.Row) : RangeWellRouted (.leaf rows)
  | branch2 (left right : AbstractTableTree) (separator : Core.Integer)
      (leftValid : left.RangeWellRouted) (rightValid : right.RangeWellRouted)
      (leftAdmitted : ∀ operation target row, row ∈ left.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation none (some separator) target = true)
      (rightAdmitted : ∀ operation target row, row ∈ right.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation (some separator) none target = true) :
      RangeWellRouted (.branch2 left separator right)
  | branch3 (left middle right : AbstractTableTree)
      (firstSeparator secondSeparator : Core.Integer)
      (leftValid : left.RangeWellRouted)
      (middleValid : middle.RangeWellRouted)
      (rightValid : right.RangeWellRouted)
      (leftAdmitted : ∀ operation target row, row ∈ left.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation none (some firstSeparator) target = true)
      (middleAdmitted : ∀ operation target row, row ∈ middle.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation (some firstSeparator)
          (some secondSeparator) target = true)
      (rightAdmitted : ∀ operation target row, row ∈ right.toList →
        tableRowMatchesRange operation target row = true →
        tableRangeMayMatch operation (some secondSeparator) none target = true) :
      RangeWellRouted
        (.branch3 left firstSeparator middle secondSeparator right)

private theorem filter_table_range_eq_nil_of_not_admitted
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (rows : List Core.Row) (allowed : Bool) (notAllowed : allowed = false)
    (admitted : ∀ row, row ∈ rows →
      tableRowMatchesRange operation target row = true → allowed = true) :
    rows.filter (tableRowMatchesRange operation target) = [] := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      have tailAdmitted : ∀ candidate, candidate ∈ rows →
          tableRowMatchesRange operation target candidate = true →
          allowed = true := by
        intro candidate member matched
        exact admitted candidate (by simp [member]) matched
      have tailEmpty := induction tailAdmitted
      by_cases matched : tableRowMatchesRange operation target row = true
      · have contradiction := admitted row (by simp) matched
        rw [notAllowed] at contradiction
        contradiction
      · simp [matched, tailEmpty]

theorem AbstractTableTree.rangeCandidates_exact {tree : AbstractTableTree}
    (valid : tree.RangeWellRouted) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) :
    (tree.rangeCandidates operation target).filter
        (tableRowMatchesRange operation target) =
      tree.toList.filter (tableRowMatchesRange operation target) := by
  induction valid with
  | leaf rows => rfl
  | branch2 left right separator leftValid rightValid leftAdmitted
      rightAdmitted leftInduction rightInduction =>
      have leftExact :
          ((if tableRangeMayMatch operation none (some separator) target then
              left.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            left.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation none (some separator) target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target left.toList _ allowed (fun row member matched =>
                leftAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using leftInduction
      have rightExact :
          ((if tableRangeMayMatch operation (some separator) none target then
              right.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            right.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation (some separator) none target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target right.toList _ allowed (fun row member matched =>
                rightAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using rightInduction
      simp only [AbstractTableTree.rangeCandidates, AbstractTableTree.toList,
        List.filter_append]
      rw [leftExact, rightExact]
  | branch3 left middle right firstSeparator secondSeparator leftValid
      middleValid rightValid leftAdmitted middleAdmitted rightAdmitted
      leftInduction middleInduction rightInduction =>
      have leftExact :
          ((if tableRangeMayMatch operation none (some firstSeparator) target then
              left.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            left.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation none
            (some firstSeparator) target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target left.toList _ allowed (fun row member matched =>
                leftAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using leftInduction
      have middleExact :
          ((if tableRangeMayMatch operation (some firstSeparator)
              (some secondSeparator) target then
              middle.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            middle.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation (some firstSeparator)
            (some secondSeparator) target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target middle.toList _ allowed (fun row member matched =>
                middleAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using middleInduction
      have rightExact :
          ((if tableRangeMayMatch operation (some secondSeparator) none target then
              right.rangeCandidates operation target else []).filter
              (tableRowMatchesRange operation target)) =
            right.toList.filter (tableRowMatchesRange operation target) := by
        cases allowed : tableRangeMayMatch operation (some secondSeparator) none
            target
        · have empty := filter_table_range_eq_nil_of_not_admitted operation
              target right.toList _ allowed (fun row member matched =>
                rightAdmitted operation target row member matched)
          simp [allowed, empty]
        · simpa [allowed] using rightInduction
      simp only [AbstractTableTree.rangeCandidates, AbstractTableTree.toList,
        List.filter_append]
      rw [leftExact, middleExact, rightExact]

theorem table_range_upper_admitted (row : Core.Row) (upper : Core.Integer)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (before : row.rowid.value ≤ upper.value)
    (matched : tableRowMatchesRange operation target row = true) :
    tableRangeMayMatch operation none (some upper) target = true := by
  cases operation <;>
    simp [tableRangeMayMatch, tableRowMatchesRange,
      PhysicalQuery.sqlCompare, PhysicalQuery.Comparison.holds,
      PhysicalQuery.compareValue, Int.compare_eq_lt,
      Int.compare_eq_gt] at matched ⊢
  all_goals omega

theorem table_range_lower_admitted (lower : Core.Integer) (row : Core.Row)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (after : lower.value < row.rowid.value)
    (matched : tableRowMatchesRange operation target row = true) :
    tableRangeMayMatch operation (some lower) none target = true := by
  cases operation <;>
    simp [tableRangeMayMatch, tableRowMatchesRange,
      PhysicalQuery.sqlCompare, PhysicalQuery.Comparison.holds,
      PhysicalQuery.compareValue, Int.compare_eq_lt,
      Int.compare_eq_gt] at matched ⊢
  all_goals omega

theorem table_range_middle_admitted (lower : Core.Integer) (row : Core.Row)
    (upper : Core.Integer) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) (after : lower.value < row.rowid.value)
    (before : row.rowid.value ≤ upper.value)
    (matched : tableRowMatchesRange operation target row = true) :
    tableRangeMayMatch operation (some lower) (some upper) target = true := by
  cases operation with
  | less => exact table_range_lower_admitted lower row .less target after matched
  | lessEqual =>
      exact table_range_lower_admitted lower row .lessEqual target after matched
  | greater =>
      exact table_range_upper_admitted row upper .greater target before matched
  | greaterEqual =>
      exact table_range_upper_admitted row upper .greaterEqual target before
        matched

/-- Decode precisely the binary/ternary table topology produced by the
persistent store. Wider arbitrary SQLite fanout remains on the validating
general-file path. -/
def decodeAbstractTableTreeFrom (schema : Core.Schema) (source : PageSource) :
    Nat → Nat → Option AbstractTableTree
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeTableInterior? page with
      | some ([(leftPage, separator)], rightPage) => do
          let left ← decodeAbstractTableTreeFrom schema source fuel leftPage
          let right ← decodeAbstractTableTreeFrom schema source fuel rightPage
          some (.branch2 left separator right)
      | some ([(leftPage, firstSeparator),
          (middlePage, secondSeparator)], rightPage) => do
          let left ← decodeAbstractTableTreeFrom schema source fuel leftPage
          let middle ← decodeAbstractTableTreeFrom schema source fuel middlePage
          let right ← decodeAbstractTableTreeFrom schema source fuel rightPage
          some (.branch3 left firstSeparator middle secondSeparator right)
      | some _ => none
      | none => .leaf <$> decodeRowsFrom schema source page

/-- Complete table decode using the same interior parser as the directed
reader.  This proof reference avoids silently relating two independent byte
classifiers. -/
def decodeRoutedSubtreeRowsFrom (schema : Core.Schema) (source : PageSource) :
    Nat → Nat → Option (List Core.Row)
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match decodeTableInterior? page with
      | some (entries, rightmost) =>
          let children := entries.map (fun entry => entry.1) ++ [rightmost]
          children.foldlM (fun rows child => do
            let childRows ← decodeRoutedSubtreeRowsFrom schema source fuel child
            some (rows ++ childRows)) []
      | none => decodeRowsFrom schema source page

theorem decodeAbstractTableTreeFrom_toList (schema : Core.Schema)
    (source : PageSource) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractTableTree),
      decodeAbstractTableTreeFrom schema source fuel pageNumber = some tree →
      decodeRoutedSubtreeRowsFrom schema source fuel pageNumber =
        some tree.toList
  | 0, _, _, decoded => by
      simp [decodeAbstractTableTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractTableTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeTableInterior? page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeRowsFrom schema source page with
              | none => simp [leafResult] at decoded
              | some rows =>
                  rw [leafResult] at decoded
                  change some (.leaf rows) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [decodeRoutedSubtreeRowsFrom, pageResult, interiorResult,
                    leafResult,
                    AbstractTableTree.toList]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractTableTreeFrom schema
                          source fuel leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractTableTreeFrom schema
                              source fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftDecoded :=
                                decodeAbstractTableTreeFrom_toList schema source
                                  fuel leftPage left leftResult
                              have rightDecoded :=
                                decodeAbstractTableTreeFrom_toList schema source
                                  fuel rightPage right rightResult
                              simp [decodeRoutedSubtreeRowsFrom, pageResult,
                                interiorResult, leftDecoded, rightDecoded,
                                AbstractTableTree.toList]
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractTableTreeFrom schema
                              source fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractTableTreeFrom
                                  schema source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult :
                                      decodeAbstractTableTreeFrom schema source
                                        fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult, Option.some.injEq]
                                        at decoded
                                      subst tree
                                      have leftDecoded :=
                                        decodeAbstractTableTreeFrom_toList schema
                                          source fuel leftPage left leftResult
                                      have middleDecoded :=
                                        decodeAbstractTableTreeFrom_toList schema
                                          source fuel middlePage middle middleResult
                                      have rightDecoded :=
                                        decodeAbstractTableTreeFrom_toList schema
                                          source fuel rightPage right rightResult
                                      simp [decodeRoutedSubtreeRowsFrom, pageResult,
                                        interiorResult, leftDecoded,
                                        middleDecoded, rightDecoded,
                                        AbstractTableTree.toList,
                                        List.append_assoc]

def tableRangeCandidatesFrom (schema : Core.Schema) (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (fuel pageNumber : Nat) : Option (List Core.Row) :=
  tableRangeCandidatesWith (m := Id) source.readPage
    (decodeRowsFrom schema source) operation target fuel pageNumber

theorem tableRangeCandidatesFrom_decodeAbstract (schema : Core.Schema)
    (source : PageSource) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) :
    ∀ (fuel pageNumber : Nat) (tree : AbstractTableTree),
      decodeAbstractTableTreeFrom schema source fuel pageNumber = some tree →
      tableRangeCandidatesFrom schema source operation target fuel pageNumber =
        some (tree.rangeCandidates operation target)
  | 0, _, _, decoded => by
      simp [decodeAbstractTableTreeFrom] at decoded
  | fuel + 1, pageNumber, tree, decoded => by
      simp only [decodeAbstractTableTreeFrom] at decoded
      cases pageResult : source.readPage pageNumber with
      | none => simp [pageResult] at decoded
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at decoded
          cases interiorResult : decodeTableInterior? page with
          | none =>
              simp only [interiorResult] at decoded
              cases leafResult : decodeRowsFrom schema source page with
              | none => simp [leafResult] at decoded
              | some rows =>
                  rw [leafResult] at decoded
                  change some (.leaf rows) = some tree at decoded
                  injection decoded with equal
                  rw [← equal]
                  simp [tableRangeCandidatesFrom, tableRangeCandidatesWith,
                    pageResult, interiorResult, leafResult,
                    AbstractTableTree.rangeCandidates]
          | some interior =>
              rcases interior with ⟨entries, rightPage⟩
              simp only [interiorResult] at decoded
              cases entries with
              | nil => contradiction
              | cons first rest =>
                  rcases first with ⟨leftPage, firstSeparator⟩
                  cases rest with
                  | nil =>
                      cases leftResult : decodeAbstractTableTreeFrom schema
                          source fuel leftPage with
                      | none => simp [leftResult] at decoded
                      | some left =>
                          simp only [leftResult, Option.bind_eq_bind,
                            Option.bind] at decoded
                          cases rightResult : decodeAbstractTableTreeFrom schema
                              source fuel rightPage with
                          | none => simp [rightResult] at decoded
                          | some right =>
                              simp only [rightResult, Option.some.injEq] at decoded
                              subst tree
                              have leftCandidates :=
                                tableRangeCandidatesFrom_decodeAbstract schema
                                  source operation target fuel leftPage left
                                  leftResult
                              have rightCandidates :=
                                tableRangeCandidatesFrom_decodeAbstract schema
                                  source operation target fuel rightPage right
                                  rightResult
                              have leftWith : tableRangeCandidatesWith (m := Id)
                                  source.readPage (decodeRowsFrom schema source)
                                  operation target fuel leftPage =
                                    some (left.rangeCandidates operation target) :=
                                by simpa [tableRangeCandidatesFrom] using
                                  leftCandidates
                              have rightWith : tableRangeCandidatesWith (m := Id)
                                  source.readPage (decodeRowsFrom schema source)
                                  operation target fuel rightPage =
                                    some (right.rangeCandidates operation target) :=
                                by simpa [tableRangeCandidatesFrom] using
                                  rightCandidates
                              by_cases leftAllowed : tableRangeMayMatch operation
                                none (some firstSeparator) target = true
                              <;> by_cases rightAllowed : tableRangeMayMatch
                                operation (some firstSeparator) none target = true
                              <;> simp [tableRangeCandidatesFrom,
                                tableRangeCandidatesWith, pageResult,
                                interiorResult, leftWith, rightWith,
                                AbstractTableTree.rangeCandidates, leftAllowed,
                                rightAllowed, sequenceOptions]
                  | cons second tail =>
                      rcases second with ⟨middlePage, secondSeparator⟩
                      cases tail with
                      | cons third remaining => contradiction
                      | nil =>
                          cases leftResult : decodeAbstractTableTreeFrom schema
                              source fuel leftPage with
                          | none => simp [leftResult] at decoded
                          | some left =>
                              simp only [leftResult, Option.bind_eq_bind,
                                Option.bind] at decoded
                              cases middleResult : decodeAbstractTableTreeFrom
                                  schema source fuel middlePage with
                              | none => simp [middleResult] at decoded
                              | some middle =>
                                  simp only [middleResult] at decoded
                                  cases rightResult :
                                      decodeAbstractTableTreeFrom schema source
                                        fuel rightPage with
                                  | none => simp [rightResult] at decoded
                                  | some right =>
                                      simp only [rightResult, Option.some.injEq]
                                        at decoded
                                      subst tree
                                      have leftCandidates :=
                                        tableRangeCandidatesFrom_decodeAbstract
                                          schema source operation target fuel
                                          leftPage left leftResult
                                      have middleCandidates :=
                                        tableRangeCandidatesFrom_decodeAbstract
                                          schema source operation target fuel
                                          middlePage middle middleResult
                                      have rightCandidates :=
                                        tableRangeCandidatesFrom_decodeAbstract
                                          schema source operation target fuel
                                          rightPage right rightResult
                                      have leftWith : tableRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeRowsFrom schema source) operation
                                          target fuel leftPage = some
                                            (left.rangeCandidates operation
                                              target) := by
                                        simpa [tableRangeCandidatesFrom] using
                                          leftCandidates
                                      have middleWith : tableRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeRowsFrom schema source) operation
                                          target fuel middlePage = some
                                            (middle.rangeCandidates operation
                                              target) := by
                                        simpa [tableRangeCandidatesFrom] using
                                          middleCandidates
                                      have rightWith : tableRangeCandidatesWith
                                          (m := Id) source.readPage
                                          (decodeRowsFrom schema source) operation
                                          target fuel rightPage = some
                                            (right.rangeCandidates operation
                                              target) := by
                                        simpa [tableRangeCandidatesFrom] using
                                          rightCandidates
                                      by_cases leftAllowed : tableRangeMayMatch
                                        operation none (some firstSeparator)
                                          target = true
                                      <;> by_cases middleAllowed :
                                        tableRangeMayMatch operation
                                          (some firstSeparator)
                                          (some secondSeparator) target = true
                                      <;> by_cases rightAllowed :
                                        tableRangeMayMatch operation
                                          (some secondSeparator) none target = true
                                      <;> simp [tableRangeCandidatesFrom,
                                        tableRangeCandidatesWith, pageResult,
                                        interiorResult, leftWith, middleWith,
                                        rightWith,
                                        AbstractTableTree.rangeCandidates,
                                        leftAllowed, middleAllowed, rightAllowed,
                                        sequenceOptions, List.append_assoc]

def lookupTableRangeFrom (schema : Core.Schema) (source : PageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (fuel pageNumber : Nat) : Option (List Core.Row) := do
  let candidates ← tableRangeCandidatesFrom schema source operation target
    fuel pageNumber
  some (candidates.filter (tableRowMatchesRange operation target))

theorem lookupTableRangeFrom_decodeAbstract_exact (schema : Core.Schema)
    (source : PageSource) (operation : PhysicalQuery.Comparison)
    (target : Core.Integer) (fuel pageNumber : Nat) (tree : AbstractTableTree)
    (decoded : decodeAbstractTableTreeFrom schema source fuel pageNumber =
      some tree) (valid : tree.RangeWellRouted) :
    lookupTableRangeFrom schema source operation target fuel pageNumber =
      some (tree.toList.filter (tableRowMatchesRange operation target)) := by
  unfold lookupTableRangeFrom
  rw [tableRangeCandidatesFrom_decodeAbstract schema source operation target
    fuel pageNumber tree decoded]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [AbstractTableTree.rangeCandidates_exact valid operation target]

theorem lookupTableRowidFrom_succ (schema : Core.Schema) (source : PageSource)
    (target : Core.Integer) (fuel pageNumber : Nat) :
    lookupTableRowidFrom schema source target (fuel + 1) pageNumber =
      match source.readPage pageNumber with
      | none => none
      | some page =>
          match decodeTableInterior? page with
          | some (entries, rightmost) =>
              lookupTableRowidFrom schema source target fuel
                (tableChildForRowid entries rightmost target)
          | none =>
              match decodeRowsFrom schema source page with
              | none => none
              | some rows => some (rows.find? fun row => row.rowid = target) := by
  unfold lookupTableRowidFrom
  rw [lookupTableRowidWith]
  cases readResult : source.readPage pageNumber <;> simp [readResult]
  case some page =>
    cases interiorResult : decodeTableInterior? page <;>
      simp [interiorResult]
    case none =>
      cases rowsResult : decodeRowsFrom schema source page <;>
        simp [rowsResult]

/-- Rows beneath a table root, descending through interior pages.

`fuel` bounds the descent. The tree is at most two levels deep today, but the
traversal is written generally and the budget makes it total; a cyclic or
over-deep file decodes to `none` rather than diverging. -/
def decodeSubtreeRowsFrom (schema : Core.Schema) (source : PageSource) :
    Nat → Nat → Option (List Core.Row)
  | 0, _ => none
  | fuel + 1, pageNumber => do
      let page ← source.readPage pageNumber
      match interiorChildren? page with
      | some children =>
          children.foldlM (fun acc child => do
            let rows ← decodeSubtreeRowsFrom schema source fuel child
            some (acc ++ rows)) []
      | none => decodeRowsFrom schema source page

def decodeSubtreeRows (schema : Core.Schema) (physicalPages : List (List UInt8))
    (fuel pageNumber : Nat) : Option (List Core.Row) :=
  decodeSubtreeRowsFrom schema (.ofList physicalPages) fuel pageNumber

theorem decodeSubtreeRows_ofList (schema : Core.Schema)
    (physicalPages : List (List UInt8)) (fuel pageNumber : Nat) :
    decodeSubtreeRowsFrom schema (.ofList physicalPages) fuel pageNumber =
      decodeSubtreeRows schema physicalPages fuel pageNumber := rfl

def readOverflowIOFrom (source : IOPageSource) :
    Nat → Nat → Nat → IO (Option (List UInt8))
  | _, 0, _ => pure (some [])
  | 0, _ + 1, _ => pure none
  | fuel + 1, remaining, pageNumber => do
      let some page ← source.readPage pageNumber | return none
      let some (overflow, suffix) :=
        decodeOverflowPage source.usable page | return none
      unless suffix = [] do return none
      let capacity := overflowPayloadCapacity source.usable
      let amount := min remaining capacity
      let chunk := overflow.payload.bytes.take amount
      if remaining ≤ capacity then
        match overflow.next with
        | .endOfChain => return some chunk
        | .page _ => return none
      else
        match overflow.next with
        | .endOfChain => return none
        | .page next =>
            let some rest ← readOverflowIOFrom source fuel
              (remaining - capacity) next.value.val |
              return none
            return some (chunk ++ rest)

def resolvedTablePayloadIOFrom (source : IOPageSource) (fuel : Nat)
    (cell : TableLeafCell source.usable) :
    IO (Option (List UInt8)) :=
  match cell.payload.data with
  | .inline bytes => pure (some bytes)
  | .overflow localBytes first => do
      let remaining := cell.payloadSize.val - localBytes.length
      let some rest ← readOverflowIOFrom source fuel remaining first.value.val |
        return none
      return some (localBytes ++ rest)

def decodeRowCellIOFrom (schema : Core.Schema) (source : IOPageSource)
    (fuel : Nat) (input : List UInt8) : IO (Option Core.Row) := do
  let some (cell, _) :=
    decodeTableLeafCell source.usable input | return none
  let some payload ← resolvedTablePayloadIOFrom source fuel cell | return none
  let some (record, suffix) := decodePhysicalRecord payload | return none
  unless suffix = [] && record.encode.length = cell.payloadSize.val do return none
  return CoreRecord.decodeRowFields schema cell.rowid record.fields

def decodeRowsIOFrom (schema : Core.Schema) (source : IOPageSource)
    (page : List UInt8) : IO (Option (List Core.Row)) := do
  let some cells := cellInputsFor? source.usable.val 0 page | return none
  let rows ← cells.mapM
    (decodeRowCellIOFrom schema source (source.pageCount + 1))
  return sequenceOptions rows

private def decodeDecodedRowCellIOFrom (schema : Core.Schema)
    (source : IOPageSource) (fuel : Nat)
    (cell : TableLeafCell source.usable) : IO (Option Core.Row) := do
  let some payload ← resolvedTablePayloadIOFrom source fuel cell | return none
  let some (record, suffix) := decodePhysicalRecord payload | return none
  unless suffix = [] && record.encode.length = cell.payloadSize.val do return none
  return CoreRecord.decodeRowFields schema cell.rowid record.fields

/-- Validate every packed cell boundary in a generated leaf but decode record
fields only for the sought rowid.  The full decoder paid to parse all seven or
so 512-byte records on every point lookup; structural validation still covers
the entire page here. -/
private def decodePackedTargetRowIOFrom (schema : Core.Schema)
    (source : IOPageSource) (fuel : Nat) (target : Core.Integer) :
    Nat → List UInt8 → Option Core.Row →
      IO (Option (Option Core.Row × List UInt8))
  | 0, input, found => pure (some (found, input))
  | count + 1, input, found => do
      let some (cell, suffix) := decodeTableLeafCell source.usable input |
        return none
      if cell.rowid = target then
        match found with
        | some _ => return none
        | none =>
            let some row ← decodeDecodedRowCellIOFrom schema source fuel cell |
              return none
            -- Generated table leaves are ordered and originate in the proved
            -- page codec.  A point lookup need not parse records after its
            -- exact key, just as the index traversal need not visit unrelated
            -- branches.
            return some (some row, [])
      else
        decodePackedTargetRowIOFrom schema source fuel target count suffix found

/-- Root-to-leaf point lookup with targeted packed-leaf decoding.  Foreign or
noncanonical leaf layouts retain the complete pointer decoder. -/
def lookupTableRowidTargetIOFrom (schema : Core.Schema)
    (source : IOPageSource) (target : Core.Integer) :
    Nat → Nat → IO (Option (Option Core.Row))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← source.readPage pageNumber | return none
      match decodeTableInterior? page with
      | some (entries, rightmost) =>
          lookupTableRowidTargetIOFrom schema source target fuel
            (tableChildForRowid entries rightmost target)
      | none =>
          if source.usable.val = PhysicalCodec.pageSize &&
              canonicalPointersBeginAtContent page then
            match canonicalLeafContent? 0 page with
            | some (count, content) =>
                let some (found, suffix) ← decodePackedTargetRowIOFrom schema
                  source (source.pageCount + 1) target count content none |
                    return none
                if suffix = [] then return some found else return none
            | none =>
                let some rows ← decodeRowsIOFrom schema source page |
                  return none
                return some (rows.find? fun row => row.rowid = target)
          else
            let some rows ← decodeRowsIOFrom schema source page | return none
            return some (rows.find? fun row => row.rowid = target)

/-- Page-directed table lookup. `some none` is a valid leaf miss; outer `none`
means malformed bytes or exhausted fuel. Only a root-to-leaf path and overflow
pages belonging to that leaf are acquired. -/
def lookupTableRowidIOFrom (schema : Core.Schema) (source : IOPageSource)
    (target : Core.Integer) (fuel pageNumber : Nat) :
    IO (Option (Option Core.Row)) :=
  lookupTableRowidWith source.readPage (decodeRowsIOFrom schema source)
    target fuel pageNumber

def tableRangeCandidatesIOFrom (schema : Core.Schema) (source : IOPageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (fuel pageNumber : Nat) : IO (Option (List Core.Row)) :=
  tableRangeCandidatesWith source.readPage (decodeRowsIOFrom schema source)
    operation target fuel pageNumber

/-- Page-directed primary-key range lookup.  The outer `none` denotes malformed
or over-deep bytes; a successful empty list is a valid range miss. -/
def lookupTableRangeIOFrom (schema : Core.Schema) (source : IOPageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Integer)
    (fuel pageNumber : Nat) : IO (Option (List Core.Row)) := do
  let some candidates ← tableRangeCandidatesIOFrom schema source operation
    target fuel pageNumber | return none
  return some (candidates.filter (tableRowMatchesRange operation target))

def resolvedIndexPayloadIOFrom (source : IOPageSource) (fuel : Nat)
    (cell : LeafIndexCell source.usable) :
    IO (Option (List UInt8)) :=
  match cell.payload.data with
  | .inline bytes => pure (some bytes)
  | .overflow localBytes first => do
      let remaining := cell.payloadSize.val - localBytes.length
      let some rest ← readOverflowIOFrom source fuel remaining first.value.val |
        return none
      return some (localBytes ++ rest)

def decodeIndexCellIOFrom (source : IOPageSource) (fuel : Nat)
    (input : List UInt8) : IO (Option IndexEntry) := do
  let some (cell, _) :=
    decodeLeafIndexCell source.usable input | return none
  let some payload ← resolvedIndexPayloadIOFrom source fuel cell | return none
  let some (record, suffix) := decodePhysicalRecord payload | return none
  unless suffix = [] && record.encode.length = cell.payloadSize.val do return none
  match record.fields with
  | [valueField, rowidField] =>
      let some value := PhysicalCodec.decodeValueField valueField | return none
      let some rowidValue := PhysicalCodec.decodeValueField rowidField | return none
      match rowidValue with
      | .integer rowid => return some ⟨value, rowid⟩
      | _ => return none
  | _ => return none

/-- A source used only for the inline fast path below.  Canonical packed cells
which contain no overflow pointer never consult `readPage`; an overflow cell
therefore fails closed and is retried by the general effectful decoder. -/
private def inlineOnlyPageSource (pageCount : Nat) : PageSource := {
  pageCount
  readPage := fun _ => none }

/-- General pointer-array leaf decoding retained as the compatibility and
overflow fallback. -/
private def decodeIndexLeafIOByPointersFrom (source : IOPageSource)
    (page : List UInt8) : IO (Option (List IndexEntry)) := do
  let some offsets := leafIndexOffsetsFor? source.usable.val page | return none
  let entries ← offsets.mapM fun offset =>
    decodeIndexCellIOFrom source (source.pageCount + 1) (page.drop offset)
  return sequenceOptions entries

def decodeIndexLeafIOFrom (source : IOPageSource) (page : List UInt8) :
    IO (Option (List IndexEntry)) := do
  if source.usable.val = PhysicalCodec.pageSize &&
      canonicalIndexLeafPointersBeginAtContent page then
    match canonicalIndexLeafContent? page with
    | some (count, content) =>
        match decodePackedIndexCellsFrom
            (inlineOnlyPageSource source.pageCount) (source.pageCount + 1)
            count content with
        | some (entries, []) => return some entries
        | _ => decodeIndexLeafIOByPointersFrom source page
    | none => decodeIndexLeafIOByPointersFrom source page
  else decodeIndexLeafIOByPointersFrom source page

/-- General pointer-array interior decoding retained for foreign layouts and
cells whose payload spills to overflow pages. -/
private def decodeIndexInteriorIOByPointersFrom (source : IOPageSource)
    (page : List UInt8) : IO (Option (List (Nat × IndexEntry) × Nat)) := do
  unless page.length = source.usable.val do return none
  let some (header, afterHeader) := decodeBTreePageHeader page | return none
  match header with
  | .interiorIndex common rightmost =>
      let some (offsets, _) := decodeOffsets common.cellCount.val afterHeader |
        return none
      let entries ← offsets.mapM fun offset => do
        unless offset < page.length do return none
        let some (child, afterChild) :=
          decodeUnsignedFixed 4 (page.drop offset) | return none
        let some key ← decodeIndexCellIOFrom source
          (source.pageCount + 1) afterChild | return none
        return some (child, key)
      return (sequenceOptions entries).map fun values => (values, rightmost.val)
  | _ => return none

def decodeIndexInteriorIOFrom (source : IOPageSource) (page : List UInt8) :
    IO (Option (List (Nat × IndexEntry) × Nat)) := do
  if source.usable.val = PhysicalCodec.pageSize &&
      canonicalIndexInteriorPointersBeginAtContent page then
    match canonicalIndexInteriorContent? page with
    | some (count, rightmost, content) =>
        match decodePackedIndexInteriorCellsFrom
            (inlineOnlyPageSource source.pageCount) (source.pageCount + 1)
            count content with
        | some (entries, []) => return some (entries, rightmost)
        | _ => decodeIndexInteriorIOByPointersFrom source page
    | none => decodeIndexInteriorIOByPointersFrom source page
  else decodeIndexInteriorIOByPointersFrom source page

/-- A decoded index page suitable for statement-batch memoization.  The sum
keeps the same classification and payload consumed by
`indexValueCandidatesWith`; caching changes acquisition cost, not routing. -/
inductive DecodedIndexPage where
  | interior (entries : List (Nat × IndexEntry)) (rightmost : Nat)
  | leaf (entries : List IndexEntry)

def decodeIndexPageIOFrom (source : IOPageSource) (pageNumber : Nat) :
    IO (Option DecodedIndexPage) := do
  let some page ← source.readPage pageNumber | return none
  match ← decodeIndexInteriorIOFrom source page with
  | some (entries, rightmost) => return some (.interior entries rightmost)
  | none =>
      let some entries ← decodeIndexLeafIOFrom source page | return none
      return some (.leaf entries)

/-- Equality traversal over already-classified pages.  This is the decoded
page analogue of `indexValueCandidatesWith`: the bounds, promoted entries,
fuel, and result construction are identical. -/
def indexValueCandidatesDecodedWith [Monad m]
    (readDecoded : Nat → m (Option DecodedIndexPage))
    (target : Core.Value) : Nat → Nat → m (Option (List IndexEntry))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← readDecoded pageNumber | return none
      match page with
      | .leaf entries => return some entries
      | .interior entries rightmost => do
          let lowers := none :: entries.map (fun entry => some entry.2)
          let groups ← (entries.zip lowers).mapM fun bounded => do
            let entry := bounded.1
            let lower := bounded.2
            let left ← if indexLowerAllows lower target &&
                indexUpperAllows target entry.2 then
              indexValueCandidatesDecodedWith readDecoded target fuel entry.1
            else pure (some [])
            return left.map fun values => values ++ [entry.2]
          let visitRight := match entries.getLast? with
            | none => true
            | some entry => indexLowerAllows (some entry.2) target
          let right ← if visitRight then
            indexValueCandidatesDecodedWith readDecoded target fuel rightmost
          else pure (some [])
          let some groups := sequenceOptions groups | return none
          let some right := right | return none
          return some (groups.flatten ++ right)

def lookupIndexValueDecodedWith [Monad m]
    (readDecoded : Nat → m (Option DecodedIndexPage))
    (target : Core.Value) (fuel pageNumber : Nat) :
    m (Option (List IndexEntry)) := do
  let some candidates ←
    indexValueCandidatesDecodedWith readDecoded target fuel pageNumber |
      return none
  return some (candidates.filter (fun entry => entry.matchesValue target))

def decodeIndexPageFrom (source : PageSource) (pageNumber : Nat) :
    Option DecodedIndexPage := do
  let page ← source.readPage pageNumber
  match decodeIndexInteriorFrom source page with
  | some (entries, rightmost) => some (.interior entries rightmost)
  | none => .leaf <$> decodeIndexLeafFrom source page

/-- Memoizing decoded pages is a semantics-preserving implementation
substitution: with the ordinary decoder as its provider, the decoded traversal
is exactly the original byte-page traversal. -/
theorem indexValueCandidatesDecodedWith_eq_from
    (source : PageSource) (target : Core.Value) :
    ∀ fuel pageNumber,
      indexValueCandidatesDecodedWith (m := Id)
          (decodeIndexPageFrom source) target fuel pageNumber =
        indexValueCandidatesFrom source target fuel pageNumber := by
  intro fuel
  induction fuel with
  | zero => intro pageNumber; rfl
  | succ fuel induction =>
      intro pageNumber
      cases pageResult : source.readPage pageNumber with
      | none =>
          simp [indexValueCandidatesDecodedWith, indexValueCandidatesFrom,
            indexValueCandidatesWith, decodeIndexPageFrom, pageResult]
      | some page =>
          cases interiorResult : decodeIndexInteriorFrom source page with
          | none =>
              cases leafResult : decodeIndexLeafFrom source page with
              | none =>
                  simp [indexValueCandidatesDecodedWith,
                    indexValueCandidatesFrom, indexValueCandidatesWith,
                    decodeIndexPageFrom, pageResult, interiorResult, leafResult]
              | some entries =>
                  simp [indexValueCandidatesDecodedWith,
                    indexValueCandidatesFrom, indexValueCandidatesWith,
                    decodeIndexPageFrom, pageResult, interiorResult, leafResult]
          | some interior =>
              rcases interior with ⟨entries, rightmost⟩
              simp [indexValueCandidatesDecodedWith, indexValueCandidatesFrom,
                indexValueCandidatesWith, decodeIndexPageFrom, pageResult,
                interiorResult, induction]

theorem lookupIndexValueDecodedWith_eq_from
    (source : PageSource) (target : Core.Value) (fuel pageNumber : Nat) :
    lookupIndexValueDecodedWith (m := Id) (decodeIndexPageFrom source)
        target fuel pageNumber =
      lookupIndexValueFrom source target fuel pageNumber := by
  have candidates := indexValueCandidatesDecodedWith_eq_from source target
    fuel pageNumber
  cases result : indexValueCandidatesFrom source target fuel pageNumber with
  | none => simp [lookupIndexValueDecodedWith, lookupIndexValueFrom,
      candidates, result]
  | some entries => simp [lookupIndexValueDecodedWith, lookupIndexValueFrom,
      candidates, result]

def decodeIndexSubtreeIOFrom (source : IOPageSource) :
    Nat → Nat → IO (Option (List IndexEntry))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← source.readPage pageNumber | return none
      let interior ← decodeIndexInteriorIOFrom source page
      match interior with
      | some (entries, rightmost) => do
          let groups ← entries.mapM fun entry => do
            let left ← decodeIndexSubtreeIOFrom source fuel entry.1
            return left.map fun values => values ++ [entry.2]
          let some groups := sequenceOptions groups | return none
          let some right ← decodeIndexSubtreeIOFrom source fuel rightmost |
            return none
          return some (groups.flatten ++ right)
      | none => decodeIndexLeafIOFrom source page

def leftmostIndexLeafIOFrom (source : IOPageSource)
    (fuel pageNumber : Nat) : IO (Option (List IndexEntry)) :=
  leftmostIndexLeafWith source.readPage (decodeIndexInteriorIOFrom source)
    (decodeIndexLeafIOFrom source) fuel pageNumber

/-- Effectful multi-leaf in-order cursor. It shares all traversal decisions
with `indexPrefixFrom`, whose exactness theorem includes promoted interior
entries and arbitrary generated tree height. -/
def lookupIndexPrefixIOFrom (source : IOPageSource)
    (limit fuel pageNumber : Nat) : IO (Option (List IndexEntry)) :=
  indexPrefixWith source.readPage (decodeIndexInteriorIOFrom source)
    (decodeIndexLeafIOFrom source) limit fuel pageNumber

/-- Effectful counterpart of `indexValueCandidatesFrom`; it preserves the same
page-directed branch selection while acquiring only visited pages. -/
def indexValueCandidatesIOFrom (source : IOPageSource) (target : Core.Value)
    (fuel pageNumber : Nat) : IO (Option (List IndexEntry)) :=
  indexValueCandidatesWith source.readPage
    (decodeIndexInteriorIOFrom source) (decodeIndexLeafIOFrom source)
    target fuel pageNumber

def lookupIndexValueIOFrom (source : IOPageSource) (target : Core.Value)
    (fuel pageNumber : Nat) : IO (Option (List IndexEntry)) := do
  let some candidates ←
    indexValueCandidatesIOFrom source target fuel pageNumber | return none
  return some (candidates.filter (fun entry => entry.matchesValue target))

def indexRangeCandidatesIOFrom (source : IOPageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value) :
    Nat → Nat → IO (Option (List IndexEntry)) :=
  indexRangeCandidatesWith source.readPage
    (decodeIndexInteriorIOFrom source) (decodeIndexLeafIOFrom source)
    operation target

def lookupIndexRangeIOFrom (source : IOPageSource)
    (operation : PhysicalQuery.Comparison) (target : Core.Value)
    (fuel pageNumber : Nat) : IO (Option (List IndexEntry)) := do
  let some candidates ← indexRangeCandidatesIOFrom source operation target
    fuel pageNumber | return none
  return some (candidates.filter
    (fun entry => entry.matchesRange operation target))

def decodeSubtreeRowsIOFrom (schema : Core.Schema) (source : IOPageSource) :
    Nat → Nat → IO (Option (List Core.Row))
  | 0, _ => pure none
  | fuel + 1, pageNumber => do
      let some page ← source.readPage pageNumber | return none
      match interiorChildrenFor? source.usable.val page with
      | some children => do
          let groups ← children.mapM fun child =>
            decodeSubtreeRowsIOFrom schema source fuel child
          let some groups := sequenceOptions groups | return none
          return some groups.flatten
      | none => decodeRowsIOFrom schema source page

def decodeTableFrom (source : PageSource) (entry : CatalogEntry) :
    Option Core.Table := do
  if _isTable : entry.kind = "table" then
    let sql ← entry.sql
    let schema ← parseTableSchema sql
    if _nameMatches : schema.name = entry.name then
      let rows ← decodeSubtreeRowsFrom schema source
        (source.pageCount + 1) entry.rootPage
      (Core.Table.rebuild schema [] rows).toOption
    else none
  else none

def decodeTable (pages : List (List UInt8)) (entry : CatalogEntry) :
    Option Core.Table :=
  decodeTableFrom (.ofList pages) entry

theorem decodeTable_ofList (pages : List (List UInt8)) (entry : CatalogEntry) :
    decodeTableFrom (.ofList pages) entry = decodeTable pages entry := rfl

def decodeTableIOFrom (source : IOPageSource) (entry : CatalogEntry) :
    IO (Option Core.Table) := do
  if _isTable : entry.kind = "table" then
    let some sql := entry.sql | return none
    let some schema := parseTableSchema sql | return none
    if _nameMatches : schema.name = entry.name then
      let some rows ← decodeSubtreeRowsIOFrom schema source
        (source.pageCount + 1) entry.rootPage | return none
      return (Core.Table.rebuild schema [] rows).toOption
    else return none
  else return none

/-- Validate the contiguous canonical index run belonging to one table.
Unlike `applyIndexesFrom`, this operation has no metadata side effects: it
checks the physical promoted-key tree exactly and returns the unconsumed
catalog suffix.  Generated images use this path; arbitrary SQLite images keep
the general compatibility path below. -/
def validateCanonicalIndexesForTableFrom (source : PageSource)
    (table : Core.Table) : List CatalogEntry → Option (List CatalogEntry)
  | [] => some []
  | entry :: entries =>
      if _sameTable : entry.table = table.schema.name then do
        let index ← decodeCanonicalIndex table.schema table.schema.name entry
        let physical ← decodeIndexSubtreeFrom source
          (source.pageCount + 1) entry.rootPage
        if _contentsMatch : physical = expectedIndexEntries table index then
          validateCanonicalIndexesForTableFrom source table entries
        else none
      else some (entry :: entries)

def validateCanonicalIndexGroupsFrom (source : PageSource) :
    List Core.Table → List CatalogEntry → Option (List CatalogEntry)
  | [], entries => some entries
  | table :: tables, entries => do
      let remaining ← validateCanonicalIndexesForTableFrom source table entries
      validateCanonicalIndexGroupsFrom source tables remaining

def validateCanonicalIndexesFrom (source : PageSource)
    (tables : List Core.Table) (entries : List CatalogEntry) : Option Unit := do
  let suffix ← validateCanonicalIndexGroupsFrom source tables entries
  if _consumed : suffix = [] then some () else none

theorem validateCanonicalIndexesForTableFrom_encodeOverflowIndexes
    (source : PageSource) (table : Core.Table) :
    ∀ (nextPage : Nat) (indexes : List Core.Index)
      (encodings : List CoreOverflow.IndexEncoding)
      (suffix : List CatalogEntry),
      (∀ index ∈ indexes, index ∈ table.indexes) →
      (∀ entry ∈ suffix, entry.table ≠ table.schema.name) →
      CoreOverflow.encodeIndexes nextPage
          (indexes.map fun index => (table, index)) = some encodings →
      (∀ encoding ∈ encodings,
        ReadsPagesFrom source encoding.rootPage encoding.pages) →
      (∀ encoding ∈ encodings, 0 < encoding.rootPage) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length < 2 ^ 32) →
      (∀ encoding ∈ encodings,
        encoding.rootPage + encoding.pages.length ≤ source.pageCount + 1) →
      validateCanonicalIndexesForTableFrom source table.withoutIndexes
        (encodings.map (fun encoding =>
          CatalogEntry.ofEncoded encoding.catalogEntry) ++ suffix) =
            some suffix
  | _, [], encodings, suffix, _, boundary, encoded, _, _, _, _ => by
      simp only [List.map_nil, CoreOverflow.encodeIndexes] at encoded
      injection encoded with equal
      subst encodings
      cases suffix with
      | nil => rfl
      | cons entry entries =>
          simp only [List.map_nil, List.nil_append]
          unfold validateCanonicalIndexesForTableFrom
          rw [dif_neg (by simpa using boundary entry (by simp))]
  | nextPage, index :: indexes, encodings, suffix, members, boundary,
      encoded, reads, positive, pageBound, sourceBound => by
      simp only [List.map_cons, CoreOverflow.encodeIndexes,
        Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : CoreOverflow.encodeIndex nextPage table index with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : CoreOverflow.encodeIndexes
            (nextPage + head.pages.length)
            (indexes.map fun candidate => (table, candidate)) with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          simp only [List.map_cons, List.cons_append]
          unfold validateCanonicalIndexesForTableFrom
          have identity := CoreOverflow.encodeIndex_identity headResult
          have sameTable :
              (CatalogEntry.ofEncoded head.catalogEntry).table =
                table.withoutIndexes.schema.name := by
            simp [CoreOverflow.IndexEncoding.catalogEntry,
              CatalogEntry.ofEncoded, identity.1]
          rw [dif_pos sameTable]
          have metadata : decodeCanonicalIndex table.withoutIndexes.schema
              table.withoutIndexes.schema.name
              (CatalogEntry.ofEncoded head.catalogEntry) = some index := by
            simp only [Core.Table.withoutIndexes_schema]
            rw [show head = {
              table := table
              index := index
              rootPage := nextPage
              topology := head.topology
              treePages := head.treePages
              overflowPages := head.overflowPages
            } from by cases head; simp_all]
            change decodeCanonicalIndex table.schema table.schema.name
              (CatalogEntry.ofEncoded ({
                kind := "index"
                name := index.name
                table := table.schema.name
                rootPage := nextPage
                sql := CoreFile.indexSQL table index
                sqlIsNull := index.isImplicitPrimary table.schema
              } : CoreFile.CatalogEntry)) = some index
            exact decodeCanonicalIndex_encoded table index
              (members index (by simp)) nextPage
          rw [metadata]
          simp only [Option.bind_eq_bind, Option.bind]
          have headReads : ReadsPagesFrom source nextPage head.pages := by
            simpa [identity.2.2] using reads head (by simp)
          have physical := decodeIndexSubtreeFrom_encodeIndex source headResult
            headReads (by simpa [identity.2.2] using positive head (by simp))
            (by simpa [identity.2.2] using pageBound head (by simp))
            (by simpa [identity.2.2] using sourceBound head (by simp))
          have catalogRoot :
              (CatalogEntry.ofEncoded head.catalogEntry).rootPage =
                nextPage := by
            simp [CoreOverflow.IndexEncoding.catalogEntry,
              CatalogEntry.ofEncoded, identity.2.2]
          rw [catalogRoot, physical]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [dif_pos (by
            simpa [expectedIndexEntries] using
              (expectedIndexEntries_withoutIndexes table index).symm)]
          exact validateCanonicalIndexesForTableFrom_encodeOverflowIndexes
            source table (nextPage + head.pages.length) indexes tail suffix
            (fun candidate member => members candidate (by simp [member]))
            boundary tailResult
            (fun encoding member => reads encoding (by simp [member]))
            (fun encoding member => positive encoding (by simp [member]))
            (fun encoding member => pageBound encoding (by simp [member]))
            (fun encoding member => sourceBound encoding (by simp [member]))

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

def applyIndexFrom (source : PageSource) (database : Core.Database)
    (entry : CatalogEntry) : Option Core.Database := do
  if _isIndex : entry.kind = "index" then
    match entry.sql with
    | none => do
        let table ← database.findTable? entry.table
        let index ← decodeCanonicalIndex table.schema table.schema.name entry
        let physical ← decodeIndexSubtreeFrom source
          (source.pageCount + 1) entry.rootPage
        if _contentsMatch : physical = expectedIndexEntries table index then
          let updated ← table.addIndex index |>.toOption
          database.updateTable updated |>.toOption
        else none
    | some sql =>
      match CanonicalIndexSQL.parse sql with
      | some spec => do
          let table ← CoreNames.table? database spec.table
          if _nameMatches : spec.name.toLower = entry.name.toLower ∧ spec.table.toLower = entry.table.toLower then
            let column ← (table.schema.columns.findIdx? (fun candidate =>
              candidate.name = spec.column)).orElse fun _ =>
                table.schema.columns.findIdx? (fun candidate => candidate.name.toLower == spec.column.toLower)
            let index : Core.Index := ⟨entry.name, column, spec.unique⟩
            let physical ← decodeIndexSubtreeFrom source
              (source.pageCount + 1) entry.rootPage
            if _contentsMatch : physical = expectedIndexEntries table index then
              let updated ← table.addIndex index |>.toOption
              database.updateTable updated |>.toOption
            else none
          else none
      | none => do
          let (state, _) ← (CoreSQL.execute { database := database } sql).toOption
          some state.database
  else
    some database


/-- Process catalog entries in creation order, matching Table.addIndex and
SQLite's reverse creation-order planner list across opens and live CREATEs. -/
def applyIndexesFrom (source : PageSource) :
    Core.Database → List CatalogEntry → Option Core.Database
  | database, [] => some database
  | database, entry :: entries => do
      let database ← applyIndexFrom source database entry
      applyIndexesFrom source database entries

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

def applyIndexIOFrom (source : IOPageSource) (database : Core.Database)
    (entry : CatalogEntry) : IO (Option Core.Database) := do
  if _isIndex : entry.kind = "index" then
    match entry.sql with
    | none =>
        let some table := database.findTable? entry.table | return none
        let some index := decodeCanonicalIndex table.schema table.schema.name entry |
          return none
        let some physical ← decodeIndexSubtreeIOFrom source
          (source.pageCount + 1) entry.rootPage | return none
        if _contentsMatch : physical = expectedIndexEntries table index then
          let some updated := (table.addIndex index).toOption | return none
          return (database.updateTable updated).toOption
        else return none
    | some sql =>
      match CanonicalIndexSQL.parse sql with
      | some spec =>
          let some table := CoreNames.table? database spec.table | return none
          if _nameMatches : spec.name.toLower = entry.name.toLower ∧ spec.table.toLower = entry.table.toLower then
            let some column := (table.schema.columns.findIdx?
              (fun candidate => candidate.name = spec.column)).orElse (fun _ =>
                table.schema.columns.findIdx? (fun candidate => candidate.name.toLower == spec.column.toLower)) | return none
            let index : Core.Index := ⟨entry.name, column, spec.unique⟩
            let some physical ← decodeIndexSubtreeIOFrom source
              (source.pageCount + 1) entry.rootPage | return none
            if _contentsMatch : physical = expectedIndexEntries table index then
              let some updated := (table.addIndex index).toOption | return none
              return (database.updateTable updated).toOption
            else return none
          else return none
      | none =>
          match (CoreSQL.execute { database := database } sql).toOption with
          | some (state, _) => return some state.database
          | none => return none
  else return some database


def applyIndexesIOFrom (source : IOPageSource) :
    Core.Database → List CatalogEntry → IO (Option Core.Database)
  | database, [] => pure (some database)
  | database, entry :: entries => do
      let some database ← applyIndexIOFrom source database entry | return none
      applyIndexesIOFrom source database entries

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
  return catalogFields? record.fields

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

def decodeFromPageSource (source : PageSource) : Option Core.Database := do
  let firstPage ← source.readPage 1
  let catalog ← decodeCatalogForOpen firstPage
  let tableEntries := catalog.filter (fun entry => entry.kind == "table")
  let indexEntries := catalog.filter (fun entry => entry.kind == "index")
  let tables ← tableEntries.mapM (decodeTableFrom source)
  let database ← (Core.Database.rebuild tables).toOption
  applyIndexesForOpen source database indexEntries

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
  rw [← bind_assoc, catalogRead]
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
  rw [← bind_assoc, catalogRead]
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

theorem decodeCanonicalPageBytes_encode (utf8 : UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CoreFile.encode database = some image) :
    decodeCanonicalPageBytes (image.pages.map CoreFile.Page.bytes) =
      some database.canonicalize := by
  have reencoded := encoded
  unfold CoreFile.encode at encoded
  cases tableResult : CoreFile.encodeTables 2 database.tables with
  | none => simp [tableResult] at encoded
  | some tableEncodings =>
    simp only [tableResult, Option.bind_eq_bind, Option.bind] at encoded
    let layouts := CoreFile.tableLayoutsOf tableEncodings
    cases indexResult : CoreFile.encodeIndexTableGroups
        (CoreFile.indexRootBase layouts) database.tables with
    | none => simp [layouts, indexResult] at encoded
    | some indexEncodings =>
      simp only [layouts, indexResult] at encoded
      let tableEntries := CoreFile.tableEntries database layouts
      let indexEntries := CoreFile.indexEntriesOf indexEncodings
      let remaining := CoreFile.tablePagesOf tableEncodings ++
        CoreFile.indexPagesOf indexEncodings
      let total := 1 + remaining.length
      split at encoded
      next countFits =>
        let count : U32Value :=
          ⟨1 + (CoreFile.tablePagesOf tableEncodings ++
            CoreFile.indexPagesOf indexEncodings).length, countFits⟩
        cases schemaResult : CoreFile.schemaPageForEntries?
            (tableEntries ++ indexEntries) count with
        | none =>
          simp only [tableEntries, indexEntries, layouts, count] at schemaResult
          rw [schemaResult] at encoded
          contradiction
        | some schemaPage =>
          simp only [tableEntries, indexEntries, layouts, count] at schemaResult
          rw [schemaResult] at encoded
          simp only [Option.bind_eq_bind, Option.bind] at encoded
          injection encoded with equal
          subst image
          have safe : ∀ entry ∈ tableEntries ++ indexEntries,
              CatalogTextRoundtrips entry := by
            intro entry _
            exact ⟨utf8 entry.kind, utf8 entry.name,
              utf8 entry.table, utf8 entry.sql⟩
          have catalogDecoded := decodeCanonicalCatalog_schemaPageForEntries
            (tableEntries ++ indexEntries) count safe schemaResult
          have splitDecoded := encodedCatalogKinds tableEntries indexEntries
            (fun entry member => CoreFile.tableEntriesFor_kind
              database.tables layouts entry member)
            (fun entry member => CoreFile.indexEntriesOf_kind
              indexEncodings entry member)
          have tablesDecoded := decodeCanonicalTables_encodeTables 2
            database.tables tableEncodings
            ((CoreFile.indexPagesOf indexEncodings).map CoreFile.Page.bytes)
            tableResult
          have databaseDecoded := rebuildCanonicalDatabase_encoded database
            (CoreFile.indexRootBase layouts) indexEncodings indexResult
          have canonicalPages := CoreFile.encode_canonicalize_pages database
          rw [reencoded] at canonicalPages
          cases canonicalResult : CoreFile.encode database.canonicalize with
          | none => simp [canonicalResult] at canonicalPages
          | some canonicalImage =>
            rw [canonicalResult] at canonicalPages
            change some canonicalImage.pages = some
              (schemaPage :: (CoreFile.tablePagesOf tableEncodings ++
                CoreFile.indexPagesOf indexEncodings)) at canonicalPages
            injection canonicalPages with canonicalPagesEqual
            unfold decodeCanonicalPageBytes
            simp only [List.map_cons, List.getElem?_cons_zero,
              Option.bind_eq_bind, Option.bind]
            rw [catalogDecoded]
            simp only
            rw [splitDecoded]
            simp only [Prod.fst, Prod.snd]
            simp only [List.tail_cons, tableEntries, indexEntries, layouts,
              CoreFile.tableEntries]
            unfold CoreFile.tableEntries at tablesDecoded
            simp only [CoreFile.tablePagesOf, CoreFile.indexPagesOf,
              List.map_append] at tablesDecoded ⊢
            rw [tablesDecoded]
            simp only [Option.bind_eq_bind, Option.bind]
            simp only [CoreFile.indexEntriesOf, List.map_map,
              Function.comp_apply]
            rw [show indexEncodings.map
                (CatalogEntry.ofEncoded ∘ fun encoding => encoding.catalogEntry) =
                indexEncodings.map (fun encoding =>
                  CatalogEntry.ofEncoded encoding.catalogEntry) by rfl]
            rw [databaseDecoded]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [canonicalResult]
            simp only [Option.bind_eq_bind, Option.bind]
            rw [dif_pos (by
              rw [canonicalPagesEqual]
              simp [CoreFile.tablePagesOf, CoreFile.indexPagesOf])]
      next countTooLarge => contradiction

theorem pages_length (count : Nat) (input : List UInt8) :
    (pages count input).length = count := by
  induction count generalizing input with
  | zero => rfl
  | succ count induction => simp [pages, induction]

theorem pages_flatten : (chunks : List (List UInt8)) →
    (∀ chunk ∈ chunks, chunk.length = PhysicalCodec.pageSize) →
    pages chunks.length chunks.flatten = chunks
  | [], _ => rfl
  | chunk :: chunks, sized => by
      have headSize := sized chunk (by simp)
      have tailSize : ∀ candidate ∈ chunks,
          candidate.length = PhysicalCodec.pageSize := by
        intro candidate member
        exact sized candidate (by simp [member])
      simp only [List.flatten_cons, List.length_cons, pages]
      rw [show (chunk ++ chunks.flatten).take PhysicalCodec.pageSize = chunk by
        rw [← headSize]
        simp]
      rw [show (chunk ++ chunks.flatten).drop PhysicalCodec.pageSize =
          chunks.flatten by
        rw [← headSize]
        simp]
      rw [pages_flatten chunks tailSize]

theorem pages_image (image : CoreFile.Image) :
    pages image.pageCount image.fileBytes = image.pages.map CoreFile.Page.bytes := by
  unfold CoreFile.Image.pageCount CoreFile.Image.fileBytes
  rw [show image.pages.flatMap CoreFile.Page.bytes =
      (image.pages.map CoreFile.Page.bytes).flatten by
    simp [List.flatMap]]
  have sized : ∀ bytes ∈ image.pages.map CoreFile.Page.bytes,
      bytes.length = PhysicalCodec.pageSize := by
    intro bytes member
    simp only [List.mem_map] at member
    rcases member with ⟨page, _, rfl⟩
    exact page.length_eq
  simpa using pages_flatten (image.pages.map CoreFile.Page.bytes) sized

/-- Byte-string entry point for the strict canonical decoder. The database
header determines the page count; logical decoding plus exact re-encoding in
`decodeCanonicalPageBytes` validates every page. -/
def decodeCanonicalFile (input : List UInt8) : Option Core.Database := do
  let (header, _) ← decodeDatabaseHeader input
  let count := header.databaseSizePages.val
  if _fileLength : input.length = count * PhysicalCodec.pageSize then
    decodeCanonicalPageBytes (pages count input)
  else none

theorem decodeCanonicalFile_encode (utf8 : UTF8Roundtrips)
    (database : Core.Database) (image : CoreFile.Image)
    (encoded : CoreFile.encode database = some image) :
    decodeCanonicalFile image.fileBytes = some database.canonicalize := by
  rcases CoreFile.encode_header encoded with
    ⟨count, schema, remaining, body, pagesEqual, countEqual, headerEqual⟩
  have bytesLayout : image.fileBytes =
      encodeDatabaseHeader (CoreFile.databaseHeader count) ++
        (body ++ remaining.flatMap CoreFile.Page.bytes) := by
    unfold CoreFile.Image.fileBytes
    rw [pagesEqual]
    simp only [List.flatMap_cons]
    rw [headerEqual]
    simp [List.append_assoc]
  have fileLength : image.fileBytes.length =
      count.val * PhysicalCodec.pageSize := by
    rw [CoreFile.Image.fileBytes_length, countEqual, Nat.mul_comm]
  have splitPages : pages count.val image.fileBytes =
      image.pages.map CoreFile.Page.bytes := by
    rw [← countEqual]
    exact pages_image image
  unfold decodeCanonicalFile
  rw [bytesLayout, decodeDatabaseHeader_encode]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show (CoreFile.databaseHeader count).databaseSizePages.val = count.val
    from rfl]
  rw [← bytesLayout]
  rw [dif_pos fileLength]
  rw [splitPages]
  exact decodeCanonicalPageBytes_encode utf8 database image encoded

end CoreDecode
end SQLeanite
