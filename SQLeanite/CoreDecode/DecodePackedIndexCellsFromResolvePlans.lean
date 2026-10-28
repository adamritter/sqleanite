import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeRowsFromResolvedLeaf

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

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

end CoreDecode

end SQLeanite
