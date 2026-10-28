import SQLeanite.CoreTextEncoding
import Init.Data.Int.Compare
import SQLeanite.CoreFile.TableInteriorPage

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
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

end CoreDecode

end SQLeanite
