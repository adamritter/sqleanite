import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodePackedIndexCellsFromResolvePlans

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

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

end CoreDecode

end SQLeanite
