import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.ReadOverflowStepOfDecoded

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

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

end CoreDecode

end SQLeanite
