import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeRowCellWithSuffixFromEncodeCell

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

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

end CoreDecode

end SQLeanite
