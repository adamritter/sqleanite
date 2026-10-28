import SQLeaniteTests.Fail

namespace SQLeanite.Tests
open SQLeanite

def expectSignedIntegerCodec : IO Unit := do
  let suffix : List UInt8 := [7, 9]
  expectSignedIntegerCase "one-byte minimum"
    ({ value := -128, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .one) [128] suffix
  expectSignedIntegerCase "negative one"
    ({ value := -1, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .one) [255] suffix
  expectSignedIntegerCase "one-byte maximum"
    ({ value := 127, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .one) [127] suffix
  expectSignedIntegerCase "two-byte negative"
    ({ value := -129, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .two) [255, 127] suffix
  expectSignedIntegerCase "three-byte minimum"
    ({ value := -8388608, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .three) [128, 0, 0] suffix
  expectSignedIntegerCase "four-byte maximum"
    ({ value := 2147483647, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .four) [127, 255, 255, 255] suffix
  expectSignedIntegerCase "six-byte minimum"
    ({ value := -140737488355328, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .six) [128, 0, 0, 0, 0, 0] suffix
  expectSignedIntegerCase "eight-byte minimum"
    ({ value := -9223372036854775808, lowerBound := by decide, upperBound := by decide } :
      FileFormat.SignedInteger .eight) [128, 0, 0, 0, 0, 0, 0, 0] suffix
  unless FileFormat.decodeSignedInteger .eight [0, 0, 0] == none do
    fail "signed integer decoder accepted a truncated eight-byte payload"

def expectRecordFieldCase (label : String) (field : FileFormat.RecordField)
    (expected suffix : List UInt8) : IO Unit := do
  unless field.encodePayload == expected do
    fail s!"record field {label}: wrong payload bytes"
  unless FileFormat.decodeRecordFieldPayload field.serialType (expected ++ suffix) ==
      some (field, suffix) do
    fail s!"record field {label}: roundtrip did not preserve its suffix"

def expectRecordFields : IO Unit := do
  let suffix : List UInt8 := [7, 9]
  let integer : FileFormat.SignedInteger .two := {
    value := -129
    lowerBound := by decide
    upperBound := by decide }
  expectRecordFieldCase "integer" (.integer .two integer) [255, 127] suffix
  expectRecordFieldCase "float bits"
    (.floatBits ⟨4607182418800017408, by omega⟩)
    [63, 240, 0, 0, 0, 0, 0, 0] suffix
  let blobMetadata : FileFormat.BlobSerialType := {
    code := ⟨18, by omega⟩
    atLeastTwelve := by decide
    evenCode := by decide }
  let blobPayload : FileFormat.SizedBytes
      (FileFormat.serialTypePayloadSize (.blob blobMetadata)) := {
    bytes := [1, 2, 3]
    length_eq := by decide }
  expectRecordFieldCase "blob" (.blob blobMetadata blobPayload) [1, 2, 3] suffix
  let textMetadata : FileFormat.TextSerialType := {
    code := ⟨19, by omega⟩
    atLeastThirteen := by decide
    oddCode := by decide }
  let textPayload : FileFormat.SizedBytes
      (FileFormat.serialTypePayloadSize (.text textMetadata)) := {
    bytes := [97, 98, 99]
    length_eq := by decide }
  expectRecordFieldCase "text" (.text textMetadata textPayload) [97, 98, 99] suffix
  expectRecordFieldCase "constant zero" .constantZero [] suffix

def expectRecordHeader : IO Unit := do
  unless FileFormat.recordHeaderSize 0 == 1 &&
      FileFormat.recordHeaderSize 126 == 127 &&
      FileFormat.recordHeaderSize 127 == 129 &&
      FileFormat.recordHeaderSize 16381 == 16383 &&
      FileFormat.recordHeaderSize 16382 == 16385 &&
      FileFormat.recordHeaderSize 72057594037927928 == 72057594037927937 do
    fail "SQLite record-header size changed incorrectly at a varint boundary"
  let integer : FileFormat.SignedInteger .one := {
    value := -1
    lowerBound := by decide
    upperBound := by decide }
  let fields : List FileFormat.RecordField := [.integer .one integer, .constantZero]
  let record : FileFormat.PhysicalRecord := {
    fields
    headerSizeBound := by decide }
  unless record.encodeHeader == [3, 1, 8] do
    fail s!"SQLite record header had wrong bytes: {repr record.encodeHeader}"
  unless record.encodePayload == [255] && record.encode == [3, 1, 8, 255] do
    fail "SQLite physical record did not place its payload after the header"
  let suffix : List UInt8 := [7, 9]
  unless FileFormat.decodePhysicalRecord (record.encode ++ suffix) ==
      some (record, suffix) do
    fail "SQLite physical record decoder did not preserve its suffix"
  unless FileFormat.decodePhysicalRecord [4, 1, 8, 255] == none do
    fail "SQLite physical record decoder accepted a false header boundary"
  unless FileFormat.decodePhysicalRecord [3, 128, 8] == none do
    fail "SQLite physical record decoder accepted a noncanonical serial varint"

def expectBTreePageHeaders : IO Unit := do
  let leafCommon : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨2, by omega⟩
    cellContentStart := ⟨4000, by omega⟩
    fragmentedFreeBytes := 0 }
  let leaf : FileFormat.ValidBTreePageHeader 4096 := {
    header := .leafTable leafCommon
    wellFormed := by decide }
  let leafBytes : List UInt8 := [13, 0, 0, 0, 2, 15, 160, 0]
  unless FileFormat.encodeBTreePageHeader leaf.header == leafBytes do
    fail "SQLite leaf-table page header had the wrong byte layout"
  unless FileFormat.decodeValidBTreePageHeader 4096 (leafBytes ++ [7, 9]) ==
      some (leaf, [7, 9]) do
    fail "SQLite leaf-table page header did not preserve its suffix"
  let interiorCommon : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨1, by omega⟩
    cellContentStart := ⟨4000, by omega⟩
    fragmentedFreeBytes := 0 }
  let interior : FileFormat.ValidBTreePageHeader 4096 := {
    header := .interiorTable interiorCommon ⟨3, by omega⟩
    wellFormed := by decide }
  unless FileFormat.encodeBTreePageHeader interior.header ==
      [5, 0, 0, 0, 1, 15, 160, 0, 0, 0, 0, 3] do
    fail "SQLite interior-table page header had the wrong byte layout"
  let zeroChildBytes : List UInt8 :=
    [5, 0, 0, 0, 1, 15, 160, 0, 0, 0, 0, 0]
  unless FileFormat.decodeValidBTreePageHeader 4096 zeroChildBytes == none do
    fail "SQLite B-tree page decoder accepted child page number zero"
  let invalidCommon : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨1, by omega⟩
    cellContentStart := ⟨4000, by omega⟩
    fragmentedFreeBytes := 61 }
  let invalidBytes := FileFormat.encodeBTreePageHeader (.leafTable invalidCommon)
  unless FileFormat.decodeValidBTreePageHeader 4096 invalidBytes == none do
    fail "SQLite B-tree page decoder accepted excessive fragmented bytes"
  let pointers : FileFormat.SizedU16Values 2 := {
    values := [⟨4000, by omega⟩, ⟨4050, by omega⟩]
    length_eq := rfl }
  let pagePrefix : FileFormat.BTreePagePrefix 4096 := {
    header := leaf
    pointers
    pointersWithin := by decide }
  let prefixBytes := leafBytes ++ [15, 160, 15, 210]
  unless pagePrefix.encode == prefixBytes do
    fail "SQLite B-tree cell-pointer array had the wrong byte layout"
  unless FileFormat.decodeBTreePagePrefix 4096 (prefixBytes ++ [7, 9]) ==
      some (pagePrefix, [7, 9]) do
    fail "SQLite B-tree page prefix did not preserve its suffix"
  let invalidPointerBytes := leafBytes ++ [15, 159, 15, 210]
  unless FileFormat.decodeBTreePagePrefix 4096 invalidPointerBytes == none do
    fail "SQLite B-tree page decoder accepted a pointer before cell content"
  let firstCell : FileFormat.PlacedCell 4096 := {
    offset := ⟨4000, by omega⟩
    bytes := List.replicate 10 1
    nonempty := by decide
    endWithinPage := by decide }
  let secondCell : FileFormat.PlacedCell 4096 := {
    offset := ⟨4050, by omega⟩
    bytes := List.replicate 20 2
    nonempty := by decide
    endWithinPage := by decide }
  let layout : FileFormat.BTreeCellLayout 4096 := {
    pagePrefix
    cells := [firstCell, secondCell]
    pointerAgreement := rfl
    afterPrefix := by decide
    pairwiseDisjoint := by decide }
  unless layout.cells.length == 2 && firstCell.Disjoint secondCell do
    fail "SQLite B-tree cell layout lost pointer agreement or disjointness"
  let overlappingCell : FileFormat.PlacedCell 4096 := {
    offset := ⟨4005, by omega⟩
    bytes := List.replicate 10 3
    nonempty := by decide
    endWithinPage := by decide }
  unless !(firstCell.Disjoint overlappingCell) do
    fail "SQLite B-tree cell interval check accepted overlapping cells"
  let pageImage := layout.encodePage
  unless pageImage.bytes.size == 4096 &&
      pageImage.bytes.toList.take prefixBytes.length == prefixBytes &&
      pageImage.bytes[4000]? == some 1 &&
      pageImage.bytes[4020]? == some 0 &&
      pageImage.bytes[4050]? == some 2 do
    fail "SQLite B-tree layout materialized the wrong fixed-size page image"

def expectTableBTreeCells : IO Unit := do
  let usable : FileFormat.UsablePageSize := {
    val := 4096
    atLeastMinimum := by decide
    atMostMaximum := by decide }
  unless FileFormat.tableLeafMaxLocal usable == 4061 &&
      FileFormat.minLocalPayload usable == 489 &&
      FileFormat.overflowPayloadCapacity usable == 4092 do
    fail "SQLite table-leaf payload thresholds were calculated incorrectly"
  unless FileFormat.tableLeafLocalPayloadSize usable 4061 == 4061 &&
      FileFormat.tableLeafLocalPayloadSize usable 4062 == 489 &&
      FileFormat.tableLeafLocalPayloadSize usable 5000 == 908 do
    fail "SQLite table-leaf local/overflow split was calculated incorrectly"
  unless FileFormat.indexMaxLocal usable == 1002 &&
      FileFormat.indexLocalPayloadSize usable 1002 == 1002 &&
      FileFormat.indexLocalPayloadSize usable 1003 == 489 &&
      FileFormat.indexLocalPayloadSize usable 5000 == 908 do
    fail "SQLite index local/overflow split was calculated incorrectly"
  let negativeKey : FileFormat.SignedInteger .eight := {
    value := -1
    lowerBound := by decide
    upperBound := by decide }
  let childPage : FileFormat.PageNumber :=
    FileFormat.PageNumber.mk ⟨3, by omega⟩ (by decide)
  let interior : FileFormat.InteriorTableCell := {
    leftChildPage := childPage
    key := negativeKey }
  let interiorBytes : List UInt8 :=
    [0, 0, 0, 3, 255, 255, 255, 255, 255, 255, 255, 255, 255]
  unless interior.encode == interiorBytes do
    fail "SQLite interior table cell had the wrong byte layout"
  unless FileFormat.decodeInteriorTableCell (interiorBytes ++ [7, 9]) ==
      some (interior, [7, 9]) do
    fail "SQLite interior table cell did not preserve its suffix"
  unless FileFormat.decodeInteriorTableCell [0, 0, 0] == none do
    fail "SQLite interior table cell decoder accepted a truncated child page"
  unless FileFormat.decodeInteriorTableCell [0, 0, 0, 0, 1] == none do
    fail "SQLite interior table cell decoder accepted child page number zero"
  let payloadSize : FileFormat.U64Value := ⟨4, by omega⟩
  let rowid : FileFormat.SignedInteger .eight := {
    value := 1
    lowerBound := by decide
    upperBound := by decide }
  let payload : FileFormat.SizedBytes payloadSize.val := {
    bytes := [3, 1, 8, 255]
    length_eq := by decide }
  let leaf : FileFormat.InlineTableLeafCell := { payloadSize, rowid, payload }
  let leafBytes : List UInt8 := [4, 1, 3, 1, 8, 255]
  unless leaf.encode == leafBytes do
    fail "SQLite inline table leaf cell had the wrong byte layout"
  unless FileFormat.decodeInlineTableLeafCell (leafBytes ++ [7, 9]) ==
      some (leaf, [7, 9]) do
    fail "SQLite inline table leaf cell did not preserve its suffix"
  unless FileFormat.decodeInlineTableLeafCell [4, 1, 3, 1, 8] == none do
    fail "SQLite inline table leaf cell decoder accepted a truncated payload"
  let verifiedInline : FileFormat.TableLeafPayload usable payloadSize.val := {
    data := .inline payload.bytes
    wellFormed := by decide }
  let verifiedLeaf : FileFormat.TableLeafCell usable := {
    payloadSize
    rowid
    payload := verifiedInline }
  unless verifiedLeaf.encode == leafBytes do
    fail "Verified table leaf cell changed the inline byte layout"
  unless FileFormat.decodeTableLeafCell usable (verifiedLeaf.encode ++ [7, 9]) ==
      some (verifiedLeaf, [7, 9]) do
    fail "Verified inline table leaf cell did not preserve its suffix"
  let smallUsable : FileFormat.UsablePageSize := {
    val := 480
    atLeastMinimum := by decide
    atMostMaximum := by decide }
  let overflowSize : FileFormat.U64Value := ⟨446, by omega⟩
  let localBytes : List UInt8 := List.replicate 35 0
  let firstOverflowPage : FileFormat.PageNumber :=
    FileFormat.PageNumber.mk ⟨7, by omega⟩ (by decide)
  let overflowPayload : FileFormat.TableLeafPayload smallUsable overflowSize.val := {
    data := .overflow localBytes firstOverflowPage
    wellFormed := by
      constructor
      · decide
      · decide }
  let overflowLeaf : FileFormat.TableLeafCell smallUsable := {
    payloadSize := overflowSize
    rowid
    payload := overflowPayload }
  unless overflowLeaf.encode.length == 42 &&
      overflowLeaf.encode.take 3 == [131, 62, 1] &&
      overflowLeaf.encode.drop 38 == [0, 0, 0, 7] do
    fail "SQLite overflowing table leaf cell had the wrong byte layout"
  unless FileFormat.decodeTableLeafCell smallUsable (overflowLeaf.encode ++ [7, 9]) ==
      some (overflowLeaf, [7, 9]) do
    fail "SQLite overflowing table leaf cell did not preserve its suffix"
  let zeroOverflow := overflowLeaf.encode.take 38 ++ [0, 0, 0, 0]
  unless FileFormat.decodeTableLeafCell smallUsable zeroOverflow == none do
    fail "SQLite table leaf cell accepted overflow page number zero"
  let nextPage : FileFormat.OverflowNext := .page firstOverflowPage
  unless nextPage.encode == [0, 0, 0, 7] &&
      FileFormat.decodeOverflowNext (nextPage.encode ++ [9]) ==
        some (nextPage, [9]) &&
      FileFormat.decodeOverflowNext ([0, 0, 0, 0] ++ [9]) ==
        some (.endOfChain, [9]) do
    fail "SQLite overflow next-page pointer had the wrong byte layout"
  have capacity : FileFormat.overflowPayloadCapacity smallUsable = 476 := by
    decide
  let rawOverflowBytes : FileFormat.SizedBytes 476 := {
    bytes := List.replicate 476 0
    length_eq := List.length_replicate .. }
  let overflowPagePayload :
      FileFormat.SizedBytes (FileFormat.overflowPayloadCapacity smallUsable) :=
    capacity.symm ▸ rawOverflowBytes
  let overflowPage : FileFormat.OverflowPage smallUsable := {
    next := .endOfChain
    payload := overflowPagePayload }
  unless overflowPage.encode.length == 480 &&
      overflowPage.encode.take 4 == [0, 0, 0, 0] do
    fail "SQLite overflow page had the wrong byte layout"
  unless FileFormat.decodeOverflowPage smallUsable (overflowPage.encode ++ [9]) ==
      some (overflowPage, [9]) do
    fail "SQLite overflow page did not preserve its suffix"
  let secondPage : FileFormat.PageNumber :=
    FileFormat.PageNumber.mk ⟨8, by omega⟩ (by decide)
  let chainTail : FileFormat.OverflowChainData smallUsable :=
    .last firstOverflowPage overflowPagePayload 10 (by decide)
  let chainData : FileFormat.OverflowChainData smallUsable :=
    .link secondPage overflowPagePayload chainTail
  let chain : FileFormat.OverflowChain smallUsable := {
    data := chainData
    acyclic := by
      simp [chainData, chainTail, FileFormat.OverflowChainData.pageNumbers,
        secondPage, firstOverflowPage] }
  unless chain.firstPage == secondPage && chain.data.pageCount == 2 &&
      chain.logicalPayload.length == 486 &&
      chain.toPages.map (fun numbered => (numbered.1, numbered.2.next)) ==
        [(secondPage, .page firstOverflowPage),
          (firstOverflowPage, .endOfChain)] do
    fail "SQLite overflow chain linkage or logical length was incorrect"
  let boundedChain : FileFormat.BoundedOverflowChain smallUsable 10 := {
    chain
    referencesWithin := by
      simp [FileFormat.OverflowChain.ReferencesWithin, chain, chainData,
        chainTail, FileFormat.OverflowChainData.pageNumbers,
        FileFormat.PageNumber.WithinDatabase, secondPage, firstOverflowPage] <;>
        constructor <;> decide }
  unless boundedChain.firstPage.toPageId.val == 7 do
    fail "SQLite bounded overflow chain root mapped to the wrong pager PageId"
  let overflowWrites := boundedChain.toPageWrites
  unless overflowWrites.map (fun write => write.pageId.val) == [7, 6] &&
      overflowWrites.all (fun write => write.page.bytes.size == 480) do
    fail "SQLite overflow chain produced invalid pager writes"
  let resolvedData : FileFormat.OverflowChainData smallUsable :=
    .last firstOverflowPage overflowPagePayload 411 (by decide)
  let resolvedChain : FileFormat.OverflowChain smallUsable := {
    data := resolvedData
    acyclic := by
      simp [resolvedData, FileFormat.OverflowChainData.pageNumbers] }
  let resolvedLeaf : FileFormat.ResolvedTableLeafCell smallUsable := {
    cell := overflowLeaf
    chain := some resolvedChain
    resolved := by
      change resolvedChain.firstPage = firstOverflowPage ∧
        localBytes.length + resolvedChain.logicalPayload.length = overflowSize.val
      constructor
      · rfl
      · have localLength := overflowPayload.wellFormed.2
        have localSize : FileFormat.tableLeafLocalPayloadSize
            smallUsable overflowSize.val = 35 := by decide
        have chainLength := resolvedChain.logicalPayload_length
        have chainSize : resolvedChain.data.logicalPayloadSize = 411 := by
          rfl
        rw [chainSize] at chainLength
        have announcedSize : overflowSize.val = 446 := rfl
        omega }
  unless resolvedLeaf.logicalPayload.length == 446 do
    fail "Resolved table leaf cell reconstructed the wrong payload length"
  let indexPayload : FileFormat.IndexPayload usable payloadSize.val := {
    data := .inline payload.bytes
    wellFormed := by decide }
  let leafIndexCell : FileFormat.LeafIndexCell usable := {
    payloadSize
    payload := indexPayload }
  unless leafIndexCell.encode == [4, 3, 1, 8, 255] &&
      FileFormat.decodeLeafIndexCell usable (leafIndexCell.encode ++ [9]) ==
        some (leafIndexCell, [9]) do
    fail "SQLite leaf index cell had the wrong inline layout"
  let interiorIndexCell : FileFormat.InteriorIndexCell usable := {
    leftChildPage := childPage
    payloadSize
    payload := indexPayload }
  unless interiorIndexCell.encode == [0, 0, 0, 3, 4, 3, 1, 8, 255] &&
      FileFormat.decodeInteriorIndexCell usable
        (interiorIndexCell.encode ++ [9]) == some (interiorIndexCell, [9]) do
    fail "SQLite interior index cell had the wrong inline layout"
  let indexOverflowSize : FileFormat.U64Value := ⟨95, by omega⟩
  let indexOverflowPayload :
      FileFormat.IndexPayload smallUsable indexOverflowSize.val := {
    data := .overflow localBytes firstOverflowPage
    wellFormed := by
      constructor <;> decide }
  let overflowingIndexCell : FileFormat.LeafIndexCell smallUsable := {
    payloadSize := indexOverflowSize
    payload := indexOverflowPayload }
  unless overflowingIndexCell.encode.length == 40 &&
      overflowingIndexCell.encode.take 1 == [95] &&
      overflowingIndexCell.encode.drop 36 == [0, 0, 0, 7] &&
      FileFormat.decodeLeafIndexCell smallUsable
        (overflowingIndexCell.encode ++ [9]) == some (overflowingIndexCell, [9]) do
    fail "SQLite leaf index cell had the wrong overflow layout"

def expectTypedBTreeLayout : IO Unit := do
  let usable : FileFormat.UsablePageSize := {
    val := 4096
    atLeastMinimum := by decide
    atMostMaximum := by decide }
  let payloadSize : FileFormat.U64Value := ⟨1, by omega⟩
  let rowid : FileFormat.SignedInteger .eight := {
    value := 1
    lowerBound := by decide
    upperBound := by decide }
  let payload : FileFormat.TableLeafPayload usable payloadSize.val := {
    data := .inline [42]
    wellFormed := by decide }
  let leaf : FileFormat.TableLeafCell usable := { payloadSize, rowid, payload }
  let typedCell : FileFormat.TypedBTreeCell usable .leafTable := {
    offset := ⟨4000, by omega⟩
    body := .leafTable leaf
    matchesPage := rfl
    endWithinPage := by decide }
  let common : FileFormat.BTreePageHeaderCommon := {
    firstFreeblock := ⟨0, by omega⟩
    cellCount := ⟨1, by omega⟩
    cellContentStart := ⟨4000, by omega⟩
    fragmentedFreeBytes := 0 }
  let header : FileFormat.ValidBTreePageHeader usable.val := {
    header := .leafTable common
    wellFormed := by decide }
  let pointers : FileFormat.SizedU16Values 1 := {
    values := [⟨4000, by omega⟩]
    length_eq := rfl }
  let pagePrefix : FileFormat.BTreePagePrefix usable.val := {
    header
    pointers
    pointersWithin := by decide }
  let generic : FileFormat.BTreeCellLayout usable.val := {
    pagePrefix
    cells := [typedCell.toPlacedCell]
    pointerAgreement := rfl
    afterPrefix := by decide
    pairwiseDisjoint := by decide }
  let layout : FileFormat.TypedBTreePageLayout usable := {
    generic
    cells := [typedCell]
    placementsAgree := rfl }
  let boundedLayout : FileFormat.BoundedTypedBTreePageLayout usable 10 := {
    layout
    referencesWithin := by decide }
  let pageNumber : FileFormat.BoundedPageNumber 10 := {
    number := FileFormat.PageNumber.mk ⟨3, by omega⟩ (by decide)
    withinDatabase := by decide }
  let numberedPage : FileFormat.NumberedTypedBTreePage usable 10 := {
    pageNumber
    notFirstPage := by decide
    layout := boundedLayout }
  let pageWrite := numberedPage.toPageWrite
  let pageSet : FileFormat.VerifiedPageSet usable 10 := {
    btreePages := [numberedPage]
    overflowChains := []
    pageIdsNodup := by decide }
  let decodedCell : FileFormat.DecodedTypedBTreeCell usable .leafTable := {
    body := .leafTable leaf
    matchesPage := rfl }
  let decodedCells : FileFormat.DecodedBTreeCells usable .leafTable 1 := {
    cells := [decodedCell]
    length_eq := rfl }
  unless layout.cells.length == 1 &&
      layout.encodePage.bytes[4000]? == some 1 &&
      boundedLayout.layout.cells.length == 1 && pageWrite.pageId.val == 2 &&
      pageWrite.page.bytes.size == 4096 &&
      pageSet.writes.map (fun write => write.pageId.val) == [2] &&
      FileFormat.decodeBTreePageCells pagePrefix layout.encodePage ==
        some decodedCells do
    fail "Typed B-tree page layout did not place a matching leaf-table cell"

end SQLeanite.Tests
