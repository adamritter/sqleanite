import SQLeanite.CorePageCodec.EncodeChangedChunkPagesSubset

namespace SQLeanite
namespace CorePageCodec

theorem interiorChildren_interiorPage_two {firstChild firstKey secondChild
    secondKey right : Nat} {page : CoreFile.Page}
    (built : RecursivePageBTree.interiorPage?
      [(firstChild, firstKey), (secondChild, secondKey)] right = some page) :
    CoreDecode.interiorChildren? page.bytes =
      some [firstChild, secondChild, right] := by
  unfold RecursivePageBTree.interiorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      cases firstResult : RecursivePageBTree.interiorCell? firstChild firstKey with
      | none => simp [firstResult] at built
      | some firstCell =>
          cases secondResult : RecursivePageBTree.interiorCell?
              secondChild secondKey with
          | none => simp [firstResult, secondResult] at built
          | some secondCell =>
              rcases interiorCell?_shape firstResult with
                ⟨firstValue, firstEqual, firstKeyValue, _, firstCellEqual⟩
              rcases interiorCell?_shape secondResult with
                ⟨secondValue, secondEqual, secondKeyValue, _, secondCellEqual⟩
              subst firstCell
              subst secondCell
              simp only [List.mapM_cons, firstResult, secondResult,
                List.mapM_nil, pure, Pure.pure, Option.bind_eq_bind,
                Option.bind] at built
              split at built
              next fits =>
                injection built with equal
                subst page
                let encodedFirst := FileFormat.encodeU32Bytes firstValue ++
                  FileFormat.encodeVarint firstKeyValue
                let encodedSecond := FileFormat.encodeU32Bytes secondValue ++
                  FileFormat.encodeVarint secondKeyValue
                let cells := [encodedFirst, encodedSecond]
                change PhysicalTableBTree.InteriorPageFit cells at fits
                let contentStart := PhysicalCodec.pageSize -
                  (PhysicalCodec.cellBytes cells).length
                let secondStart := contentStart + encodedFirst.length
                let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
                  List.replicate
                    (contentStart -
                      (PhysicalTableBTree.interiorHeader 2 contentStart
                        rightmost ++
                        PhysicalCodec.leafPointers contentStart cells).length) 0 ++
                  PhysicalCodec.cellBytes cells
                have bodyLayout :
                    PhysicalTableBTree.interiorPageBody rightmost cells =
                      5 :: 0 :: 0 ::
                        (PhysicalCodec.encodeU16Nat 2 ++
                          PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
                            (FileFormat.encodeU32Bytes rightmost ++
                              afterHeader)) := by
                  unfold PhysicalTableBTree.interiorPageBody
                    PhysicalTableBTree.interiorHeader
                  simp only [List.cons_append, List.nil_append]
                  rfl
                change CoreDecode.interiorChildren?
                  (PhysicalTableBTree.interiorPageBody rightmost cells) =
                    some [firstChild, secondChild, right]
                unfold CoreDecode.interiorChildren?
                have bodyLength :
                    (5 :: 0 :: 0 ::
                      (PhysicalCodec.encodeU16Nat 2 ++
                        PhysicalCodec.encodeU16Nat contentStart ++ 0 ::
                          (FileFormat.encodeU32Bytes rightmost ++
                            afterHeader))).length = PhysicalCodec.pageSize := by
                  rw [← bodyLayout]
                  exact PhysicalTableBTree.interiorPageBody_length rightmost
                    cells fits
                simp only [bodyLayout]
                rw [if_pos (by simpa using bodyLength)]
                unfold PhysicalCodec.encodeU16Nat
                simp [FileFormat.encodeUnsignedFixed, FileFormat.decodeU16,
                  FileFormat.encodeU32Bytes, FileFormat.decodeU32_encode]
                unfold afterHeader PhysicalCodec.leafPointers
                  PhysicalCodec.cellOffsetsFrom PhysicalCodec.encodeU16Nat
                have firstBound : contentStart < 256 ^ 2 := by
                  simpa [cells] using PhysicalCodec.contentStart_lt cells
                have secondBound : secondStart < 256 ^ 2 := by
                  have contentLe : (PhysicalCodec.cellBytes cells).length ≤
                      PhysicalCodec.pageSize := by
                    unfold PhysicalTableBTree.InteriorPageFit at fits
                    omega
                  have firstLengthLe : encodedFirst.length ≤
                      (PhysicalCodec.cellBytes cells).length := by
                    simp [cells, PhysicalCodec.cellBytes]
                  have contentIdentity : contentStart +
                      (PhysicalCodec.cellBytes cells).length =
                        PhysicalCodec.pageSize := by
                    unfold contentStart
                    exact Nat.sub_add_cancel contentLe
                  calc
                    secondStart ≤ contentStart +
                        (PhysicalCodec.cellBytes cells).length := by
                      unfold secondStart
                      exact Nat.add_le_add_left firstLengthLe contentStart
                    _ = PhysicalCodec.pageSize := contentIdentity
                    _ < 256 ^ 2 := by decide
                have decodeTwoOffsets (suffix : List UInt8) :
                    CoreDecode.decodeOffsetList 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        FileFormat.encodeUnsignedFixed 2 secondStart ++ suffix) =
                      some [contentStart, secondStart] := by
                  unfold CoreDecode.decodeOffsetList
                  simp only [List.append_assoc,
                    FileFormat.decodeUnsignedFixed_encode _ firstBound,
                    Option.bind_eq_bind, Option.bind]
                  unfold CoreDecode.decodeOffsetList
                  rw [FileFormat.decodeUnsignedFixed_encode suffix secondBound]
                  rfl
                have decodeTwoOffsetsExpanded (suffix : List UInt8) :
                    CoreDecode.decodeOffsetList 2
                      (UInt8.ofNat (contentStart / 256 % 256) ::
                        UInt8.ofNat (contentStart % 256) ::
                        UInt8.ofNat (secondStart / 256 % 256) ::
                        UInt8.ofNat (secondStart % 256) :: suffix) =
                      some [contentStart, secondStart] := by
                  simpa [FileFormat.encodeUnsignedFixed] using
                    decodeTwoOffsets suffix
                have decodeTwoOffsetsConcrete (suffix : List UInt8) :
                    CoreDecode.decodeOffsetList 2
                      (UInt8.ofNat (contentStart / 256 % 256) ::
                        UInt8.ofNat (contentStart % 256) ::
                        UInt8.ofNat
                          ((contentStart + encodedFirst.length) / 256 % 256) ::
                        UInt8.ofNat
                          ((contentStart + encodedFirst.length) % 256) :: suffix) =
                      some [contentStart, contentStart + encodedFirst.length] := by
                  simpa [secondStart] using decodeTwoOffsetsExpanded suffix
                have decodeTwoOffsetsRight (suffix : List UInt8) :
                    CoreDecode.decodeOffsetList 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        (FileFormat.encodeUnsignedFixed 2
                          (contentStart + encodedFirst.length) ++ suffix)) =
                      some [contentStart, contentStart + encodedFirst.length] := by
                  simpa [secondStart, List.append_assoc] using
                    decodeTwoOffsets suffix
                simp only [cells, PhysicalCodec.cellOffsetsFrom,
                  List.flatMap_cons, List.flatMap_nil, List.append_nil,
                  List.append_assoc]
                rw [decodeTwoOffsetsRight]
                simp only [Option.bind_eq_bind, Option.bind]
                simp only [cells, PhysicalCodec.cellOffsetsFrom,
                  List.flatMap_cons, List.flatMap_nil, List.append_nil,
                  List.append_assoc, decodeTwoOffsets,
                  decodeTwoOffsetsExpanded, decodeTwoOffsetsConcrete,
                  Option.bind_eq_bind,
                  Option.bind, List.mapM_cons, List.mapM_nil, pure, Pure.pure]
                have droppedFirst :=
                  PhysicalTableBTree.interiorPageBody_drop_content rightmost
                    cells fits
                change (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                    contentStart = cells.flatten at droppedFirst
                have droppedSecond :
                    (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                      secondStart = encodedSecond := by
                  rw [show secondStart = contentStart + encodedFirst.length from rfl,
                    ← List.drop_drop, droppedFirst]
                  simp [cells, PhysicalCodec.cellBytes]
                simp only [bodyLayout] at droppedFirst droppedSecond
                simp [PhysicalCodec.encodeU16Nat,
                  FileFormat.encodeUnsignedFixed, FileFormat.encodeU32Bytes,
                  afterHeader, PhysicalCodec.leafPointers,
                  PhysicalCodec.cellOffsetsFrom, cells] at droppedFirst droppedSecond
                simp only [FileFormat.encodeUnsignedFixed, List.nil_append,
                  List.singleton_append, List.cons_append, List.length_append,
                  List.length_cons, List.length_nil]
                rw [droppedFirst, droppedSecond]
                have firstDecoded := FileFormat.decodeU32_encode firstValue
                have secondDecoded := FileFormat.decodeU32_encode secondValue
                have rightDecoded := FileFormat.decodeU32_encode rightmost
                simp [encodedFirst, encodedSecond, FileFormat.encodeU32Bytes,
                  firstDecoded, secondDecoded, rightDecoded, firstEqual,
                  secondEqual, boundedU32?_value rightResult]
              next => injection built

/-- The keyed routing decoder recovers both separators and all three children
from a generated three-way table interior page. -/
theorem decodeTableInterior_interiorPage_two
    {firstChild firstKey secondChild secondKey right : Nat}
    {page : CoreFile.Page} (firstPositive : 0 < firstChild)
    (secondPositive : 0 < secondChild) (firstKeyBound : firstKey < 2 ^ 64)
    (secondKeyBound : secondKey < 2 ^ 64)
    (built : RecursivePageBTree.interiorPage?
      [(firstChild, firstKey), (secondChild, secondKey)] right = some page) :
    CoreDecode.decodeTableInterior? page.bytes = some
      ([(firstChild, FileFormat.signedIntegerFromUnsigned .eight
          ⟨firstKey, by simpa [FileFormat.IntegerWidth.modulus] using
            firstKeyBound⟩),
        (secondChild, FileFormat.signedIntegerFromUnsigned .eight
          ⟨secondKey, by simpa [FileFormat.IntegerWidth.modulus] using
            secondKeyBound⟩)], right) := by
  unfold RecursivePageBTree.interiorPage? at built
  cases rightResult : RecursivePageBTree.boundedU32? right with
  | none => simp [rightResult] at built
  | some rightmost =>
      simp only [rightResult, Option.bind_eq_bind, Option.bind] at built
      cases firstResult : RecursivePageBTree.interiorCell? firstChild firstKey with
      | none => simp [firstResult] at built
      | some firstCell =>
          cases secondResult : RecursivePageBTree.interiorCell?
              secondChild secondKey with
          | none => simp [firstResult, secondResult] at built
          | some secondCell =>
              rcases interiorCell?_shape firstResult with
                ⟨firstValue, firstEqual, firstKeyValue, firstKeyEqual,
                  firstCellEqual⟩
              rcases interiorCell?_shape secondResult with
                ⟨secondValue, secondEqual, secondKeyValue, secondKeyEqual,
                  secondCellEqual⟩
              subst firstCell
              subst secondCell
              simp only [List.mapM_cons, firstResult, secondResult,
                List.mapM_nil, pure, Pure.pure, Option.bind_eq_bind,
                Option.bind] at built
              split at built
              next fits =>
                injection built with equal
                subst page
                let encodedFirst := FileFormat.encodeU32Bytes firstValue ++
                  FileFormat.encodeVarint firstKeyValue
                let encodedSecond := FileFormat.encodeU32Bytes secondValue ++
                  FileFormat.encodeVarint secondKeyValue
                let cells := [encodedFirst, encodedSecond]
                change PhysicalTableBTree.InteriorPageFit cells at fits
                let contentStart := PhysicalCodec.pageSize -
                  (PhysicalCodec.cellBytes cells).length
                let secondStart := contentStart + encodedFirst.length
                let afterHeader := PhysicalCodec.leafPointers contentStart cells ++
                  List.replicate
                    (contentStart -
                      (PhysicalTableBTree.interiorHeader 2 contentStart
                        rightmost ++
                        PhysicalCodec.leafPointers contentStart cells).length) 0 ++
                  PhysicalCodec.cellBytes cells
                have bodyLayout :
                    PhysicalTableBTree.interiorPageBody rightmost cells =
                      PhysicalTableBTree.interiorHeader 2 contentStart
                        rightmost ++ afterHeader := by
                  unfold PhysicalTableBTree.interiorPageBody afterHeader cells
                  rfl
                have bodyLength :
                    (PhysicalTableBTree.interiorPageBody rightmost cells).length =
                      PhysicalCodec.pageSize :=
                  PhysicalTableBTree.interiorPageBody_length rightmost cells fits
                have firstBound : contentStart < 256 ^ 2 := by
                  simpa [cells] using PhysicalCodec.contentStart_lt cells
                have contentLe : (PhysicalCodec.cellBytes cells).length ≤
                    PhysicalCodec.pageSize := by
                  unfold PhysicalTableBTree.InteriorPageFit at fits
                  omega
                have contentIdentity : contentStart +
                    (PhysicalCodec.cellBytes cells).length =
                      PhysicalCodec.pageSize := by
                  unfold contentStart
                  exact Nat.sub_add_cancel contentLe
                have secondBound : secondStart < 256 ^ 2 := by
                  have firstLengthLe : encodedFirst.length ≤
                      (PhysicalCodec.cellBytes cells).length := by
                    simp [cells, PhysicalCodec.cellBytes]
                  calc
                    secondStart ≤ contentStart +
                        (PhysicalCodec.cellBytes cells).length := by
                      unfold secondStart
                      exact Nat.add_le_add_left firstLengthLe contentStart
                    _ = PhysicalCodec.pageSize := contentIdentity
                    _ < 256 ^ 2 := by decide
                let common : FileFormat.BTreePageHeaderCommon := {
                  firstFreeblock := ⟨0, by decide⟩
                  cellCount := ⟨2, by decide⟩
                  cellContentStart := ⟨contentStart, by
                    simpa using firstBound⟩
                  fragmentedFreeBytes := 0 }
                have headerEncoding :
                    FileFormat.encodeBTreePageHeader
                        (.interiorTable common rightmost) =
                      PhysicalTableBTree.interiorHeader 2 contentStart
                        rightmost := by
                  rw [FileFormat.encodeBTreePageHeader_interiorTable]
                  rw [FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed,
                    FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed,
                    FileFormat.encodeU16Bytes_eq_encodeUnsignedFixed]
                  dsimp [common]
                  simp [PhysicalTableBTree.interiorHeader,
                    PhysicalCodec.encodeU16Nat,
                    FileFormat.encodeUnsignedFixed]
                have decodeTwoOffsets (suffix : List UInt8) :
                    CoreDecode.decodeOffsets 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        FileFormat.encodeUnsignedFixed 2 secondStart ++ suffix) =
                      some ([contentStart, secondStart], suffix) := by
                  unfold CoreDecode.decodeOffsets
                  simp only [List.append_assoc]
                  rw [FileFormat.decodeUnsignedFixed_encode _ firstBound]
                  simp only [Option.bind_eq_bind, Option.bind]
                  unfold CoreDecode.decodeOffsets
                  rw [FileFormat.decodeUnsignedFixed_encode suffix secondBound]
                  rfl
                have decodeTwoOffsetsConcrete (suffix : List UInt8) :
                    CoreDecode.decodeOffsets 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        FileFormat.encodeUnsignedFixed 2
                          (contentStart + encodedFirst.length) ++ suffix) =
                      some ([contentStart,
                        contentStart + encodedFirst.length], suffix) := by
                  simpa [secondStart] using decodeTwoOffsets suffix
                have decodeTwoOffsetsRight (suffix : List UInt8) :
                    CoreDecode.decodeOffsets 2
                      (FileFormat.encodeUnsignedFixed 2 contentStart ++
                        (FileFormat.encodeUnsignedFixed 2
                          (contentStart + encodedFirst.length) ++ suffix)) =
                      some ([contentStart,
                        contentStart + encodedFirst.length], suffix) := by
                  simpa [List.append_assoc] using
                    decodeTwoOffsetsConcrete suffix
                have droppedFirst :=
                  PhysicalTableBTree.interiorPageBody_drop_content rightmost
                    cells fits
                change (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                    contentStart = cells.flatten at droppedFirst
                have firstDrop :
                    (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                      contentStart = encodedFirst ++ encodedSecond := by
                  simpa [cells, PhysicalCodec.cellBytes] using droppedFirst
                have secondDrop :
                    (PhysicalTableBTree.interiorPageBody rightmost cells).drop
                      secondStart = encodedSecond := by
                  rw [show secondStart = contentStart + encodedFirst.length from
                    rfl, ← List.drop_drop, firstDrop]
                  simp
                let firstPage : FileFormat.PageNumber :=
                  ⟨firstValue, by rw [firstEqual]; exact firstPositive⟩
                let secondPage : FileFormat.PageNumber :=
                  ⟨secondValue, by rw [secondEqual]; exact secondPositive⟩
                let firstSigned :=
                  FileFormat.signedIntegerFromUnsigned .eight firstKeyValue
                let secondSigned :=
                  FileFormat.signedIntegerFromUnsigned .eight secondKeyValue
                let typedFirst : FileFormat.InteriorTableCell :=
                  ⟨firstPage, firstSigned⟩
                let typedSecond : FileFormat.InteriorTableCell :=
                  ⟨secondPage, secondSigned⟩
                have firstEncoding : typedFirst.encode = encodedFirst := by
                  change FileFormat.encodeU32Bytes firstValue ++
                    FileFormat.encodeVarint
                      (FileFormat.signedInteger64Bits firstSigned) = encodedFirst
                  have bitsEqual : FileFormat.signedInteger64Bits firstSigned =
                      firstKeyValue := by
                    apply Fin.ext
                    exact FileFormat.SignedInteger.toUnsigned_fromUnsigned
                      .eight firstKeyValue
                  rw [bitsEqual]
                have secondEncoding : typedSecond.encode = encodedSecond := by
                  change FileFormat.encodeU32Bytes secondValue ++
                    FileFormat.encodeVarint
                      (FileFormat.signedInteger64Bits secondSigned) = encodedSecond
                  have bitsEqual : FileFormat.signedInteger64Bits secondSigned =
                      secondKeyValue := by
                    apply Fin.ext
                    exact FileFormat.SignedInteger.toUnsigned_fromUnsigned
                      .eight secondKeyValue
                  rw [bitsEqual]
                have firstDecoded : FileFormat.decodeInteriorTableCell
                    (typedFirst.encode ++ encodedSecond) =
                      some (typedFirst, encodedSecond) :=
                  FileFormat.decodeInteriorTableCell_encode _ _
                have secondDecoded : FileFormat.decodeInteriorTableCell
                    typedSecond.encode = some (typedSecond, []) := by
                  simpa using FileFormat.decodeInteriorTableCell_encode
                    typedSecond []
                have firstKeyValueEq : firstKeyValue =
                    ⟨firstKey, by simpa [FileFormat.IntegerWidth.modulus]
                      using firstKeyBound⟩ := by
                  apply Fin.ext
                  exact firstKeyEqual
                have secondKeyValueEq : secondKeyValue =
                    ⟨secondKey, by simpa [FileFormat.IntegerWidth.modulus]
                      using secondKeyBound⟩ := by
                  apply Fin.ext
                  exact secondKeyEqual
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
                simp only [Option.bind_eq_bind, Option.bind, common]
                unfold afterHeader PhysicalCodec.leafPointers
                  PhysicalCodec.cellOffsetsFrom cells
                simp only [List.flatMap_cons, List.flatMap_nil,
                  List.append_nil, List.append_assoc,
                  PhysicalCodec.encodeU16Nat,
                  PhysicalCodec.cellOffsetsFrom]
                rw [decodeTwoOffsetsRight]
                simp only [Option.bind_eq_bind, Option.bind, List.mapM_cons,
                  List.mapM_nil, pure, Pure.pure]
                have contentWithin : contentStart <
                    (PhysicalTableBTree.interiorPageBody rightmost cells).length := by
                  rw [bodyLength, ← contentIdentity]
                  have bytesPositive :
                      0 < (PhysicalCodec.cellBytes cells).length := by
                    simp [cells, encodedFirst, PhysicalCodec.cellBytes,
                      FileFormat.encodeU32Bytes]
                  omega
                have secondWithin : secondStart <
                    (PhysicalTableBTree.interiorPageBody rightmost cells).length := by
                  rw [bodyLength, ← contentIdentity]
                  unfold secondStart
                  have firstLengthLt : encodedFirst.length <
                      (PhysicalCodec.cellBytes cells).length := by
                    simp [cells, encodedSecond, PhysicalCodec.cellBytes,
                      FileFormat.encodeU32Bytes]
                  omega
                have secondWithinTyped :
                    contentStart + typedFirst.encode.length <
                      (PhysicalTableBTree.interiorPageBody rightmost
                        [typedFirst.encode, encodedSecond]).length := by
                  rw [firstEncoding]
                  simpa [cells, secondStart] using secondWithin
                have secondDropTyped :
                    (PhysicalTableBTree.interiorPageBody rightmost
                      [typedFirst.encode, encodedSecond]).drop
                        (contentStart + typedFirst.encode.length) =
                      encodedSecond := by
                  rw [firstEncoding]
                  simpa [cells, secondStart] using secondDrop
                rw [dif_pos contentWithin, firstDrop, ← firstEncoding,
                  firstDecoded]
                simp only [Option.bind_eq_bind, Option.bind]
                rw [dif_pos secondWithinTyped, secondDropTyped,
                  ← secondEncoding,
                  secondDecoded]
                simp only [Option.bind_eq_bind, Option.bind]
                subst firstKeyValue
                subst secondKeyValue
                have firstSignedExpected : firstSigned =
                    FileFormat.signedIntegerFromUnsigned .eight
                      ⟨firstKey, by simpa [FileFormat.IntegerWidth.modulus]
                        using firstKeyBound⟩ := by
                  apply FileFormat.SignedInteger.ext
                  rfl
                have secondSignedExpected : secondSigned =
                    FileFormat.signedIntegerFromUnsigned .eight
                      ⟨secondKey, by simpa [FileFormat.IntegerWidth.modulus]
                        using secondKeyBound⟩ := by
                  apply FileFormat.SignedInteger.ext
                  rfl
                simp [typedFirst, typedSecond, firstPage, secondPage,
                  firstEqual, secondEqual, firstSignedExpected,
                  secondSignedExpected, boundedU32?_value rightResult]
              next => contradiction

end CorePageCodec

end SQLeanite
