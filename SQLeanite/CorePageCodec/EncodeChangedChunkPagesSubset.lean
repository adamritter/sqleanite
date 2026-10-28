import SQLeanite.CorePageCodec.PhysicalChunkPagesFastEq

namespace SQLeanite
namespace CorePageCodec

/-- Every byte selected by the exact physical-difference encoder is an exact
page of the complete post-state encoding. -/
theorem encodeChangedChunkPages_subset (schema : Core.Schema)
    (before after : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (afterPages changedPages : List NumberedPage)
    (afterEncoded : encodeChunkNode schema after = some afterPages)
    (changedEncoded : encodeChangedChunkPages schema before after =
      some changedPages) :
    ∀ page ∈ changedPages, page ∈ afterPages := by
  rw [encodeChunkNode_eq_mapM] at afterEncoded
  unfold encodeChangedChunkPages at changedEncoded
  intro page pageMember
  rcases mapM_encodePhysicalChunkPage_output schema changedEncoded page
      pageMember with ⟨descriptor, descriptorMember, descriptorEncoded⟩
  have postDescriptor : descriptor ∈ physicalChunkPages after :=
    (List.mem_filter.mp descriptorMember).1
  rcases mapM_encodePhysicalChunkPage_input schema afterEncoded descriptor
      postDescriptor with ⟨post, postMember, postEncoded⟩
  have equal : post = page := Option.some.inj
    (postEncoded.symm.trans descriptorEncoded)
  simpa [equal] using postMember

theorem encodeChunkNode_pageNumbers (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (pages : List NumberedPage)
    (encoded : encodeChunkNode schema node = some pages) :
    pages.map NumberedPage.pageNumber = node.pageIds := by
  induction node generalizing pages with
  | leaf pageId entries =>
      unfold encodeChunkNode at encoded
      cases leafResult : encodeChunkLeaf schema entries with
      | none => simp [leafResult] at encoded
      | some page =>
          simp only [leafResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at encoded
          subst pages
          rfl
  | branch2 pageId left separator right leftInduction rightInduction =>
      unfold encodeChunkNode at encoded
      cases keyResult : maximumChunkRowid? left with
      | none => simp [keyResult] at encoded
      | some key =>
          simp only [keyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases rootResult : RecursivePageBTree.interiorPage?
              [(left.rootId, key)] right.rootId with
          | none => simp [rootResult] at encoded
          | some root =>
              simp only [rootResult] at encoded
              cases leftResult : encodeChunkNode schema left with
              | none => simp [leftResult] at encoded
              | some leftPages =>
                  simp only [leftResult] at encoded
                  cases rightResult : encodeChunkNode schema right with
                  | none => simp [rightResult] at encoded
                  | some rightPages =>
                      simp only [rightResult, Option.some.injEq] at encoded
                      subst pages
                      simp only [List.map_cons, List.map_append,
                        PersistentPageTree.Node.pageIds]
                      rw [leftInduction leftPages leftResult,
                        rightInduction rightPages rightResult]
  | branch3 pageId left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      unfold encodeChunkNode at encoded
      cases leftKeyResult : maximumChunkRowid? left with
      | none => simp [leftKeyResult] at encoded
      | some leftKey =>
          simp only [leftKeyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases middleKeyResult : maximumChunkRowid? middle with
          | none => simp [middleKeyResult] at encoded
          | some middleKey =>
              simp only [middleKeyResult] at encoded
              cases rootResult : RecursivePageBTree.interiorPage?
                  [(left.rootId, leftKey), (middle.rootId, middleKey)]
                    right.rootId with
              | none => simp [rootResult] at encoded
              | some root =>
                  simp only [rootResult] at encoded
                  cases leftResult : encodeChunkNode schema left with
                  | none => simp [leftResult] at encoded
                  | some leftPages =>
                      simp only [leftResult] at encoded
                      cases middleResult : encodeChunkNode schema middle with
                      | none => simp [middleResult] at encoded
                      | some middlePages =>
                          simp only [middleResult] at encoded
                          cases rightResult : encodeChunkNode schema right with
                          | none => simp [rightResult] at encoded
                          | some rightPages =>
                              simp only [rightResult, Option.some.injEq] at encoded
                              subst pages
                              simp only [List.map_cons, List.map_append,
                                PersistentPageTree.Node.pageIds]
                              rw [leftInduction leftPages leftResult,
                                middleInduction middlePages middleResult,
                                rightInduction rightPages rightResult]

def encodeChunkRoot (schema : Core.Schema) :
    PersistentPageTree.Node CoreChunkPageState.Chunk → Option NumberedPage
  | .leaf pageId entries => do
      let page ← encodeChunkLeaf schema entries
      some ⟨pageId, page⟩
  | .branch2 pageId left _ right => do
      let leftKey ← maximumChunkRowid? left
      let page ← RecursivePageBTree.interiorPage?
        [(left.rootId, leftKey)] right.rootId
      some ⟨pageId, page⟩
  | .branch3 pageId left _ middle _ right => do
      let leftKey ← maximumChunkRowid? left
      let middleKey ← maximumChunkRowid? middle
      let page ← RecursivePageBTree.interiorPage?
        [(left.rootId, leftKey), (middle.rootId, middleKey)] right.rootId
      some ⟨pageId, page⟩

theorem encodeChunkRoot_eq_encodePhysicalChunkRoot (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk) :
    encodeChunkRoot schema node =
      encodePhysicalChunkPage schema (physicalChunkRoot node) := by
  cases node <;> rfl

theorem encodeChunkRoot_pageNumber (schema : Core.Schema)
    (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
    (page : NumberedPage) (encoded : encodeChunkRoot schema node = some page) :
    page.pageNumber = node.rootId := by
  cases node with
  | leaf pageId entries =>
      change page.pageNumber = pageId
      simp only [encodeChunkRoot] at encoded
      cases pageResult : encodeChunkLeaf schema entries with
      | none => simp [pageResult] at encoded
      | some built =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at encoded
          subst page
          rfl
  | branch2 pageId left separator right =>
      change page.pageNumber = pageId
      simp only [encodeChunkRoot] at encoded
      cases keyResult : maximumChunkRowid? left with
      | none => simp [keyResult] at encoded
      | some key =>
          simp only [keyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases rootResult : RecursivePageBTree.interiorPage?
              [(left.rootId, key)] right.rootId with
          | none =>
              rw [rootResult] at encoded
              contradiction
          | some built =>
              rw [rootResult] at encoded
              simp only [Option.some.injEq] at encoded
              subst page
              rfl
  | branch3 pageId left firstSeparator middle secondSeparator right =>
      change page.pageNumber = pageId
      simp only [encodeChunkRoot] at encoded
      cases leftResult : maximumChunkRowid? left with
      | none => simp [leftResult] at encoded
      | some leftKey =>
          simp only [leftResult, Option.bind_eq_bind, Option.bind] at encoded
          cases middleResult : maximumChunkRowid? middle with
          | none => simp [middleResult] at encoded
          | some middleKey =>
              simp only [middleResult] at encoded
              cases rootResult : RecursivePageBTree.interiorPage?
                  [(left.rootId, leftKey), (middle.rootId, middleKey)]
                    right.rootId with
              | none =>
                  rw [rootResult] at encoded
                  contradiction
              | some built =>
                  rw [rootResult] at encoded
                  simp only [Option.some.injEq] at encoded
                  subst page
                  rfl

theorem boundedU32?_value {value : Nat} {bounded : FileFormat.U32Value}
    (success : RecursivePageBTree.boundedU32? value = some bounded) :
    bounded.val = value := by
  unfold RecursivePageBTree.boundedU32? at success
  split at success
  next =>
    injection success with equal
    subst bounded
    rfl
  next => contradiction

theorem interiorCell?_shape {child key : Nat} {cell : List UInt8}
    (success : RecursivePageBTree.interiorCell? child key = some cell) :
    ∃ childValue : FileFormat.U32Value,
      childValue.val = child ∧
      ∃ keyValue : FileFormat.U64Value, keyValue.val = key ∧
        cell = FileFormat.encodeU32Bytes childValue ++
          FileFormat.encodeVarint keyValue := by
  unfold RecursivePageBTree.interiorCell? at success
  cases childResult : RecursivePageBTree.boundedU32? child with
  | none => simp [childResult] at success
  | some childValue =>
      simp only [childResult, Option.bind_eq_bind, Option.bind] at success
      cases keyResult : RecursivePageBTree.boundedU64? key with
      | none => simp [keyResult] at success
      | some keyValue =>
          simp only [keyResult, Option.some.injEq] at success
          subst cell
          refine ⟨childValue, boundedU32?_value childResult, keyValue, ?_, rfl⟩
          unfold RecursivePageBTree.boundedU64? at keyResult
          split at keyResult
          next =>
            injection keyResult with equal
            subst keyValue
            rfl
          next => contradiction

theorem interiorChildren_interiorPage_one {child key right : Nat}
    {page : CoreFile.Page}
    (built : RecursivePageBTree.interiorPage? [(child, key)] right = some page) :
    CoreDecode.interiorChildren? page.bytes = some [child, right] := by
  unfold RecursivePageBTree.interiorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      cases cellResult : RecursivePageBTree.interiorCell? child key with
      | none => simp [cellResult] at built
      | some cell =>
          rcases interiorCell?_shape cellResult with
            ⟨childValue, childEqual, keyValue, keyEqual, cellEqual⟩
          subst cell
          simp only [List.mapM_cons, cellResult, List.mapM_nil, pure,
            Pure.pure, Option.bind_eq_bind, Option.bind] at built
          split at built
          next fits =>
            injection built with equal
            subst page
            let encodedCell := FileFormat.encodeU32Bytes childValue ++
              FileFormat.encodeVarint keyValue
            let contentStart := PhysicalCodec.pageSize -
              (PhysicalCodec.cellBytes [encodedCell]).length
            let afterHeader := PhysicalCodec.leafPointers contentStart
                [encodedCell] ++
              List.replicate
                (contentStart -
                  (PhysicalTableBTree.interiorHeader 1 contentStart rightmost ++
                    PhysicalCodec.leafPointers contentStart
                      [encodedCell]).length) 0 ++
              PhysicalCodec.cellBytes [encodedCell]
            have bodyLayout :
                PhysicalTableBTree.interiorPageBody rightmost [encodedCell] =
                  5 :: 0 :: 0 ::
                    (PhysicalCodec.encodeU16Nat 1 ++
                      PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
                        (FileFormat.encodeU32Bytes rightmost ++
                          afterHeader)) := by
              unfold PhysicalTableBTree.interiorPageBody
                PhysicalTableBTree.interiorHeader
              simp only [List.cons_append, List.nil_append]
              rfl
            change CoreDecode.interiorChildren?
              (PhysicalTableBTree.interiorPageBody rightmost [encodedCell]) =
                some [child, right]
            unfold CoreDecode.interiorChildren?
            have bodyLength :
                (5 :: 0 :: 0 ::
                  (PhysicalCodec.encodeU16Nat 1 ++
                    PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
                      (FileFormat.encodeU32Bytes rightmost ++
                        afterHeader))).length = PhysicalCodec.pageSize := by
              rw [← bodyLayout]
              exact PhysicalTableBTree.interiorPageBody_length rightmost
                [encodedCell] fits
            simp only [bodyLayout]
            rw [if_pos (by simpa using bodyLength)]
            unfold PhysicalCodec.encodeU16Nat
            simp [FileFormat.encodeUnsignedFixed,
              FileFormat.decodeU16, FileFormat.encodeU32Bytes,
              FileFormat.decodeU32_encode]
            unfold afterHeader
            unfold PhysicalCodec.leafPointers PhysicalCodec.cellOffsetsFrom
            unfold PhysicalCodec.encodeU16Nat
            have contentBound : contentStart < 256 ^ 2 := by
              simpa using PhysicalCodec.contentStart_lt [encodedCell]
            have decodeOneOffset (suffix : List UInt8) :
                CoreDecode.decodeOffsetList 1
                  (FileFormat.encodeUnsignedFixed 2 contentStart ++ suffix) =
                    some [contentStart] := by
              unfold CoreDecode.decodeOffsetList
              rw [FileFormat.decodeUnsignedFixed_encode suffix contentBound]
              rfl
            simp only [PhysicalCodec.cellOffsetsFrom, List.flatMap_cons,
              List.flatMap_nil, List.append_nil, List.append_assoc,
              decodeOneOffset, Option.bind_eq_bind, Option.bind, List.mapM_cons,
              List.mapM_nil, pure, Pure.pure]
            have dropped := PhysicalTableBTree.interiorPageBody_drop_content
              rightmost [encodedCell] fits
            change (PhysicalTableBTree.interiorPageBody rightmost
              [encodedCell]).drop contentStart = [encodedCell].flatten at dropped
            simp only [bodyLayout] at dropped
            simp [PhysicalCodec.encodeU16Nat,
              FileFormat.encodeUnsignedFixed, FileFormat.encodeU32Bytes,
              afterHeader, PhysicalCodec.leafPointers,
              PhysicalCodec.cellOffsetsFrom] at dropped
            simp only [FileFormat.encodeUnsignedFixed, List.nil_append,
              List.singleton_append, List.cons_append, List.length_append,
              List.length_cons, List.length_nil]
            rw [dropped]
            have childDecoded := FileFormat.decodeU32_encode childValue
            have rightDecoded := FileFormat.decodeU32_encode rightmost
            simp [encodedCell, FileFormat.encodeU32Bytes, childDecoded,
              rightDecoded, childEqual, boundedU32?_value rightResult]
          next => contradiction

/-- The keyed routing decoder recovers the only separator and both children
from a generated two-way table interior page. -/
theorem decodeTableInterior_interiorPage_one {child key right : Nat}
    {page : CoreFile.Page} (childPositive : 0 < child)
    (keyBound : key < 2 ^ 64)
    (built : RecursivePageBTree.interiorPage? [(child, key)] right = some page) :
    CoreDecode.decodeTableInterior? page.bytes = some
      ([(child, FileFormat.signedIntegerFromUnsigned .eight
        ⟨key, by simpa [FileFormat.IntegerWidth.modulus] using keyBound⟩)], right) := by
  unfold RecursivePageBTree.interiorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      cases cellResult : RecursivePageBTree.interiorCell? child key with
      | none => simp [cellResult] at built
      | some cell =>
          rcases interiorCell?_shape cellResult with
            ⟨childValue, childEqual, keyValue, keyEqual, cellEqual⟩
          subst cell
          simp only [List.mapM_cons, cellResult, List.mapM_nil, pure,
            Pure.pure, Option.bind_eq_bind, Option.bind] at built
          split at built
          next fits =>
            injection built with equal
            subst page
            let encodedCell := FileFormat.encodeU32Bytes childValue ++
              FileFormat.encodeVarint keyValue
            let cells := [encodedCell]
            let contentStart := PhysicalCodec.pageSize -
              (PhysicalCodec.cellBytes cells).length
            let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
              List.replicate
                (contentStart -
                  (PhysicalTableBTree.interiorHeader 1 contentStart rightmost ++
                    PhysicalCodec.leafPointers contentStart cells).length) 0 ++
              PhysicalCodec.cellBytes cells
            have bodyLayout :
                PhysicalTableBTree.interiorPageBody rightmost cells =
                  PhysicalTableBTree.interiorHeader 1 contentStart rightmost ++
                    afterHeader := by
              unfold PhysicalTableBTree.interiorPageBody afterHeader cells
              rfl
            have bodyLength :
                (PhysicalTableBTree.interiorPageBody rightmost cells).length =
                  PhysicalCodec.pageSize :=
              PhysicalTableBTree.interiorPageBody_length rightmost cells fits
            have countBound : 1 < 256 ^ 2 := by decide
            have contentBound : contentStart < 256 ^ 2 := by
              simpa [cells] using PhysicalCodec.contentStart_lt cells
            let common : FileFormat.BTreePageHeaderCommon := {
              firstFreeblock := ⟨0, by decide⟩
              cellCount := ⟨1, by decide⟩
              cellContentStart := ⟨contentStart, by
                simpa using contentBound⟩
              fragmentedFreeBytes := 0 }
            have headerEncoding :
                FileFormat.encodeBTreePageHeader
                    (.interiorTable common rightmost) =
                  PhysicalTableBTree.interiorHeader 1 contentStart rightmost := by
              rw [FileFormat.encodeBTreePageHeader_interiorTable]
              rw [FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed,
                FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed,
                FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed]
              dsimp [common]
              simp [PhysicalTableBTree.interiorHeader,
                PhysicalCodec.encodeU16Nat, FileFormat.encodeUnsignedFixed]
            have decodeOneOffset (suffix : List UInt8) :
                CoreDecode.decodeOffsets 1
                    (FileFormat.encodeUnsignedFixed 2 contentStart ++ suffix) =
                  some ([contentStart], suffix) := by
              unfold CoreDecode.decodeOffsets
              rw [FileFormat.decodeUnsignedFixed_encode suffix contentBound]
              rfl
            have dropped := PhysicalTableBTree.interiorPageBody_drop_content
              rightmost cells fits
            change (PhysicalTableBTree.interiorPageBody rightmost cells).drop
              contentStart = cells.flatten at dropped
            have droppedCell :
                (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                    contentStart = encodedCell := by
              simpa [cells, PhysicalCodec.cellBytes] using dropped
            let childPage : FileFormat.PageNumber :=
              ⟨childValue, by rw [childEqual]; exact childPositive⟩
            let signedKey := FileFormat.signedIntegerFromUnsigned .eight keyValue
            let typedCell : FileFormat.InteriorTableCell :=
              ⟨childPage, signedKey⟩
            have typedEncoding : typedCell.encode = encodedCell := by
              change FileFormat.encodeU32Bytes childValue ++
                  FileFormat.encodeVarint
                    (FileFormat.signedInteger64Bits signedKey) = encodedCell
              have bitsEqual :
                  FileFormat.signedInteger64Bits signedKey = keyValue := by
                apply Fin.ext
                exact FileFormat.SignedInteger.toUnsigned_fromUnsigned
                  .eight keyValue
              rw [bitsEqual]
            have keyValueEq : keyValue =
                ⟨key, by simpa [FileFormat.IntegerWidth.modulus] using keyBound⟩ := by
              apply Fin.ext
              exact keyEqual
            change CoreDecode.decodeTableInterior?
              (PhysicalTableBTree.interiorPageBody rightmost cells) = _
            unfold CoreDecode.decodeTableInterior?
            rw [dif_pos bodyLength]
            have headerDecoded : FileFormat.decodeBTreePageHeader
                (PhysicalTableBTree.interiorPageBody rightmost cells) =
                  some (.interiorTable common rightmost, afterHeader) := by
              rw [bodyLayout, ← headerEncoding,
                FileFormat.decodeBTreePageHeader_encode]
            rw [headerDecoded]
            simp only [Option.bind_eq_bind, Option.bind]
            simp only [common]
            unfold afterHeader PhysicalCodec.leafPointers
              PhysicalCodec.cellOffsetsFrom cells
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
              List.append_assoc, PhysicalCodec.encodeU16Nat]
            rw [decodeOneOffset]
            simp only [Option.bind_eq_bind, Option.bind, List.mapM_cons,
              List.mapM_nil, pure, Pure.pure]
            have contentWithin : contentStart <
                (PhysicalTableBTree.interiorPageBody rightmost
                  [encodedCell]).length := by
              rw [show (PhysicalTableBTree.interiorPageBody rightmost
                [encodedCell]).length = PhysicalCodec.pageSize from by
                  simpa [cells] using bodyLength]
              unfold contentStart
              have cellBytesPositive :
                  0 < (PhysicalCodec.cellBytes cells).length := by
                simp [cells, encodedCell, PhysicalCodec.cellBytes,
                  FileFormat.encodeU32Bytes]
              have pageSizePositive : 0 < PhysicalCodec.pageSize := by decide
              omega
            rw [dif_pos contentWithin]
            rw [show (PhysicalTableBTree.interiorPageBody rightmost
              [encodedCell]).drop contentStart = encodedCell from by
                simpa [cells] using droppedCell, ← typedEncoding]
            have typedDecoded : FileFormat.decodeInteriorTableCell
                typedCell.encode = some (typedCell, []) := by
              simpa using
                FileFormat.decodeInteriorTableCell_encode typedCell []
            rw [typedDecoded]
            simp only [Option.bind_eq_bind, Option.bind]
            subst keyValue
            have signedKeyExpected : signedKey =
                FileFormat.signedIntegerFromUnsigned .eight
                  ⟨key, by simpa [FileFormat.IntegerWidth.modulus] using
                    keyBound⟩ := by
              apply FileFormat.SignedInteger.ext
              rfl
            simp [typedCell, childPage, childEqual,
              signedKeyExpected, boundedU32?_value rightResult]
          next => contradiction

end CorePageCodec

end SQLeanite
