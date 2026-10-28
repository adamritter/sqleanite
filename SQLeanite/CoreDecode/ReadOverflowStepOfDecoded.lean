import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeCanonicalTableStepEncoded

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

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

theorem decodeOverflowPayloadBytesFrom_of_decoded
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

end CoreDecode

end SQLeanite
