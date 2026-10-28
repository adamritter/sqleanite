import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeRowCellWithSuffixFromTableCellPlanOverflowFuel

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

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

end CoreDecode

end SQLeanite
