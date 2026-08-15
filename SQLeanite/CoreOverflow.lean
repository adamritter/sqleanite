import SQLeanite.RecursivePageBTree

namespace SQLeanite
namespace CoreOverflow

open FileFormat

inductive PayloadKind where
  | table
  | index
  deriving DecidableEq

def maxLocal : PayloadKind → Nat
  | .table => tableLeafMaxLocal PhysicalCodec.usablePageSize
  | .index => indexMaxLocal PhysicalCodec.usablePageSize

def localSize : PayloadKind → Nat → Nat
  | .table => tableLeafLocalPayloadSize PhysicalCodec.usablePageSize
  | .index => indexLocalPayloadSize PhysicalCodec.usablePageSize

structure CellPlan where
  kind : PayloadKind
  cellPrefix : List UInt8
  payload : List UInt8

def CellPlan.localBytes (plan : CellPlan) : List UInt8 :=
  plan.payload.take (localSize plan.kind plan.payload.length)

def CellPlan.overflowBytes (plan : CellPlan) : List UInt8 :=
  plan.payload.drop (localSize plan.kind plan.payload.length)

theorem CellPlan.local_append_overflow (plan : CellPlan) :
    plan.localBytes ++ plan.overflowBytes = plan.payload := by
  exact List.take_append_drop _ _

def boundedPageNumber? (value : Nat) : Option PageNumber :=
  if positive : 0 < value then
    if bounded : value < 2 ^ 32 then
      some ⟨⟨value, by simpa using bounded⟩, positive⟩
    else none
  else none

theorem boundedPageNumber?_page (page : PageNumber) :
  boundedPageNumber? page.value.val = some page := by
  unfold boundedPageNumber?
  rw [dif_pos page.positive, dif_pos page.value.isLt]

def CellPlan.cellBytes? (plan : CellPlan) (firstOverflow : Option Nat) :
    Option (List UInt8) :=
  if _fits : plan.payload.length ≤ maxLocal plan.kind then
    some (plan.cellPrefix ++ plan.payload)
  else do
    let first ← firstOverflow
    let page ← boundedPageNumber? first
    some (plan.cellPrefix ++ plan.localBytes ++ page.encode)

def CellPlan.storedPayloadLength (plan : CellPlan) : Nat :=
  if plan.payload.length ≤ maxLocal plan.kind then
    plan.payload.length
  else plan.localBytes.length + 4

theorem CellPlan.cellBytes_length {plan : CellPlan} {firstOverflow : Option Nat}
    {bytes : List UInt8} (built : plan.cellBytes? firstOverflow = some bytes) :
    bytes.length = plan.cellPrefix.length + plan.storedPayloadLength := by
  unfold CellPlan.cellBytes? at built
  split at built
  next fits =>
    injection built with equal
    subst bytes
    simp [CellPlan.storedPayloadLength, fits]
  next doesNotFit =>
    simp only [Option.bind_eq_bind, Option.bind] at built
    cases firstOverflow with
    | none => contradiction
    | some first =>
      cases pageResult : boundedPageNumber? first with
      | none => simp [pageResult] at built
      | some page =>
        simp only [pageResult, Option.some.injEq] at built
        subst bytes
        simp [CellPlan.storedPayloadLength, doesNotFit,
          PageNumber.encode, encodeU32Bytes]

theorem CellPlan.pointer_substitution_preserves_length (plan : CellPlan)
    {leftFirst rightFirst : Option Nat} {left right : List UInt8}
    (leftBuilt : plan.cellBytes? leftFirst = some left)
    (rightBuilt : plan.cellBytes? rightFirst = some right) :
    left.length = right.length := by
  rw [plan.cellBytes_length leftBuilt, plan.cellBytes_length rightBuilt]

def CellPlan.provisionalBytes? (plan : CellPlan) : Option (List UInt8) :=
  plan.cellBytes? (some 1)

def overflowCapacity : Nat :=
  overflowPayloadCapacity PhysicalCodec.usablePageSize

def overflowPageCount (bytes : List UInt8) : Nat :=
  if bytes.isEmpty then 0
  else (bytes.length + overflowCapacity - 1) / overflowCapacity

theorem overflowCapacity_positive : 0 < overflowCapacity := by
  decide

theorem overflowPageCount_eq_zero_iff (bytes : List UInt8) :
    overflowPageCount bytes = 0 ↔ bytes = [] := by
  unfold overflowPageCount
  cases bytes with
  | nil => simp
  | cons byte bytes =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, List.cons.injEq, false_iff]
      simp only [overflowCapacity, overflowPayloadCapacity,
        PhysicalCodec.usablePageSize, PhysicalCodec.pageSize]
      constructor
      · intro zero
        have positive : 0 <
            (bytes.length + 1 + (4096 - 4) - 1) / (4096 - 4) := by
          apply Nat.div_pos <;> omega
        omega
      · intro impossible
        contradiction

theorem overflowPageCount_positive {bytes : List UInt8}
    (nonempty : bytes ≠ []) : 0 < overflowPageCount bytes := by
  have nonzero : overflowPageCount bytes ≠ 0 :=
    fun equal => nonempty ((overflowPageCount_eq_zero_iff bytes).mp equal)
  omega

theorem overflowPageCount_eq_one_of_length_le {bytes : List UInt8}
    (nonempty : bytes ≠ []) (fits : bytes.length ≤ overflowCapacity) :
    overflowPageCount bytes = 1 := by
  unfold overflowPageCount
  rw [if_neg (by simpa using nonempty)]
  simp only [overflowCapacity, overflowPayloadCapacity,
    PhysicalCodec.usablePageSize, PhysicalCodec.pageSize] at fits ⊢
  have positive : 0 < bytes.length := List.length_pos_iff.mpr nonempty
  omega

theorem overflowPageCount_drop_capacity {bytes : List UInt8}
    (tooLarge : overflowCapacity < bytes.length) :
    overflowPageCount (bytes.drop overflowCapacity) + 1 =
      overflowPageCount bytes := by
  have droppedNonempty : bytes.drop overflowCapacity ≠ [] := by
    exact List.ne_nil_of_length_pos (by simp; omega)
  have nonempty : bytes ≠ [] := List.ne_nil_of_length_pos (by omega)
  unfold overflowPageCount
  rw [if_neg (by simpa using droppedNonempty),
    if_neg (by simpa using nonempty)]
  simp only [List.length_drop, overflowCapacity,
    overflowPayloadCapacity, PhysicalCodec.usablePageSize,
    PhysicalCodec.pageSize] at tooLarge ⊢
  omega

def overflowPageBytes (start count offset : Nat) (bytes : List UInt8) :
    List UInt8 :=
  let chunk := (bytes.drop (offset * overflowCapacity)).take overflowCapacity
  let next := if offset + 1 < count then start + offset + 1 else 0
  PhysicalTableBTree.encodeU32Nat next ++ chunk ++
    List.replicate (overflowCapacity - chunk.length) 0

theorem encodeU32Nat_eq_encodeU32Bytes {value : Nat}
    (bound : value < 2 ^ 32) :
    PhysicalTableBTree.encodeU32Nat value =
      FileFormat.encodeU32Bytes ⟨value, by simpa using bound⟩ := by
  have highByte : value / 16777216 < 256 := by omega
  simp [PhysicalTableBTree.encodeU32Nat, FileFormat.encodeUnsignedFixed,
    FileFormat.encodeU32Bytes, FileFormat.encodeU32,
    Nat.div_div_eq_div_mul, Nat.mod_eq_of_lt highByte]

theorem overflowPageBytes_length (start count offset : Nat)
    (bytes : List UInt8) :
    (overflowPageBytes start count offset bytes).length =
      PhysicalCodec.pageSize := by
  unfold overflowPageBytes
  dsimp only
  have chunkLe :
      ((bytes.drop (offset * overflowCapacity)).take overflowCapacity).length ≤
        overflowCapacity := List.length_take_le _ _
  simp only [List.length_append, PhysicalTableBTree.encodeU32Nat_length,
    List.length_replicate]
  simp only [overflowCapacity, overflowPayloadCapacity,
    PhysicalCodec.usablePageSize, PhysicalCodec.pageSize] at chunkLe ⊢
  omega

def generatedOverflowNext (start count offset : Nat)
    (bounded : start + count < 2 ^ 32) :
    OverflowNext :=
  if hasNext : offset + 1 < count then
    have valueBound : start + offset + 1 < 2 ^ 32 := by
      apply Nat.lt_of_lt_of_le
      · exact Nat.add_lt_add_left hasNext start
      · omega
    .page ⟨⟨start + offset + 1, valueBound⟩,
      by exact Nat.zero_lt_succ (start + offset)⟩
  else .endOfChain

def generatedOverflowPayload (offset : Nat) (bytes : List UInt8) :
    SizedBytes overflowCapacity :=
  let chunk := (bytes.drop (offset * overflowCapacity)).take overflowCapacity
  ⟨chunk ++ List.replicate (overflowCapacity - chunk.length) 0, by
    simp only [List.length_append, List.length_replicate]
    have chunkLe : chunk.length ≤ overflowCapacity :=
      List.length_take_le _ _
    omega⟩

def generatedOverflowPage (start count offset : Nat) (bytes : List UInt8)
    (bounded : start + count < 2 ^ 32) :
    OverflowPage PhysicalCodec.usablePageSize := {
  next := generatedOverflowNext start count offset bounded
  payload := generatedOverflowPayload offset bytes }

theorem overflowPageBytes_eq_generated (start count offset : Nat)
    (bytes : List UInt8) (bounded : start + count < 2 ^ 32) :
    overflowPageBytes start count offset bytes =
      (generatedOverflowPage start count offset bytes bounded).encode := by
  unfold overflowPageBytes generatedOverflowPage OverflowPage.encode
    generatedOverflowNext generatedOverflowPayload
  dsimp only
  split
  next hasNext =>
    rw [encodeU32Nat_eq_encodeU32Bytes (by omega)]
    rfl
  next noNext =>
    rw [encodeU32Nat_eq_encodeU32Bytes (value := 0) (by omega)]
    rfl

theorem decodeOverflowPage_overflowPageBytes (start count offset : Nat)
    (bytes : List UInt8) (bounded : start + count < 2 ^ 32) :
    decodeOverflowPage PhysicalCodec.usablePageSize
        (overflowPageBytes start count offset bytes) =
      some (generatedOverflowPage start count offset bytes bounded,
        []) := by
  rw [overflowPageBytes_eq_generated start count offset bytes bounded]
  simpa using decodeOverflowPage_encode
    (generatedOverflowPage start count offset bytes bounded) []

theorem generatedOverflowPage_next_final (start : Nat) (bytes : List UInt8)
    (bounded : start + 1 < 2 ^ 32) :
    (generatedOverflowPage start 1 0 bytes bounded).next =
      .endOfChain := by
  simp [generatedOverflowPage, generatedOverflowNext]

theorem generatedOverflowPage_next_step (start count : Nat)
    (bytes : List UInt8) (countPositive : 0 < count)
    (bounded : start + (count + 1) < 2 ^ 32) :
    ∃ next : PageNumber,
      (generatedOverflowPage start (count + 1) 0 bytes bounded).next =
        .page next ∧
      next.value.val = start + 1 := by
  unfold generatedOverflowPage generatedOverflowNext
  simp only [show 0 + 1 < count + 1 by omega, dite_true]
  exact ⟨_, rfl, by simp⟩

theorem generatedOverflowPage_payload_take_final (start : Nat)
    (bytes : List UInt8) (fits : bytes.length ≤ overflowCapacity)
    (bounded : start + 1 < 2 ^ 32) :
    (generatedOverflowPage start 1 0 bytes bounded).payload.bytes.take
        bytes.length = bytes := by
  unfold generatedOverflowPage generatedOverflowPayload
  dsimp only
  simp only [Nat.zero_mul, List.drop_zero]
  rw [List.take_of_length_le fits]
  simp

theorem generatedOverflowPage_payload_take_step (start count : Nat)
    (bytes : List UInt8) (tooLarge : overflowCapacity < bytes.length)
    (bounded : start + (count + 1) < 2 ^ 32) :
    (generatedOverflowPage start (count + 1) 0 bytes bounded).payload.bytes.take
        overflowCapacity = bytes.take overflowCapacity := by
  unfold generatedOverflowPage generatedOverflowPayload
  dsimp only
  simp only [Nat.zero_mul, List.drop_zero]
  have takenLength : (bytes.take overflowCapacity).length =
      overflowCapacity := by
    rw [List.length_take]
    exact Nat.min_eq_left (by omega)
  rw [List.take_append_of_le_length (by omega)]
  rw [List.take_take, Nat.min_self]

theorem overflowPageBytes_succ (start count tailCount offset : Nat)
    (bytes : List UInt8) (counts : tailCount + 1 = count) :
    overflowPageBytes start count (offset + 1) bytes =
      overflowPageBytes (start + 1) tailCount offset
        (bytes.drop overflowCapacity) := by
  unfold overflowPageBytes
  dsimp only
  have drops :
      bytes.drop ((offset + 1) * overflowCapacity) =
        (bytes.drop overflowCapacity).drop (offset * overflowCapacity) := by
    rw [List.drop_drop]
    simp [Nat.add_mul, Nat.add_comm]
  have nextIff : offset + 1 + 1 < count ↔ offset + 1 < tailCount := by
    omega
  have nextValues :
      (if offset + 1 + 1 < count then start + (offset + 1) + 1 else 0) =
        (if offset + 1 < tailCount then start + 1 + offset + 1 else 0) := by
    by_cases hasNext : offset + 1 + 1 < count
    · have tailHasNext := nextIff.mp hasNext
      simp [hasNext, tailHasNext]
      omega
    · have tailHasNoNext : ¬ offset + 1 < tailCount :=
        fun tailHasNext => hasNext (nextIff.mpr tailHasNext)
      simp [hasNext, tailHasNoNext]
  rw [drops, nextValues]

/-- The proof-carrying page corresponding to one overflow-chain position. -/
def overflowPage (start count offset : Nat) (bytes : List UInt8) :
    CoreFile.Page :=
  ⟨overflowPageBytes start count offset bytes,
    overflowPageBytes_length start count offset bytes⟩

def makeOverflowPages? (start : Nat) (bytes : List UInt8) :
    Option (List CoreFile.Page) :=
  let count := overflowPageCount bytes
  some ((List.range count).map fun offset =>
    overflowPage start count offset bytes)

theorem makeOverflowPages?_eq (start : Nat) (bytes : List UInt8) :
    makeOverflowPages? start bytes = some
      ((List.range (overflowPageCount bytes)).map fun offset =>
        overflowPage start (overflowPageCount bytes) offset bytes) := by
  rfl

theorem makeOverflowPages?_length {start : Nat} {bytes : List UInt8}
    {pages : List CoreFile.Page}
    (built : makeOverflowPages? start bytes = some pages) :
    pages.length = overflowPageCount bytes := by
  rw [makeOverflowPages?_eq] at built
  injection built with equal
  subst pages
  simp

theorem makeOverflowPages?_bytes {start : Nat} {bytes : List UInt8}
    {pages : List CoreFile.Page}
    (built : makeOverflowPages? start bytes = some pages) :
    pages.map CoreFile.Page.bytes =
      (List.range (overflowPageCount bytes)).map fun offset =>
        overflowPageBytes start (overflowPageCount bytes) offset bytes := by
  rw [makeOverflowPages?_eq] at built
  injection built with equal
  subst pages
  simp [overflowPage]

structure Resolved where
  cells : List (List UInt8)
  pages : List CoreFile.Page
  nextPage : Nat

def resolvePlans : Nat → List CellPlan → Option Resolved
  | next, [] => some ⟨[], [], next⟩
  | next, plan :: plans => do
      let overflow := plan.overflowBytes
      let count := overflowPageCount overflow
      let first := if count = 0 then none else some next
      let cell ← plan.cellBytes? first
      let pages ← makeOverflowPages? next overflow
      let rest ← resolvePlans (next + pages.length) plans
      some ⟨cell :: rest.cells, pages ++ rest.pages, rest.nextPage⟩

theorem resolvePlans_cells_length : ∀ {next : Nat} {plans : List CellPlan}
    {resolved : Resolved}, resolvePlans next plans = some resolved →
      resolved.cells.length = plans.length
  | _, [], resolved, success => by
      simp only [resolvePlans, Option.some.injEq] at success
      subst resolved
      rfl
  | next, plan :: plans, resolved, success => by
      simp only [resolvePlans, Option.bind_eq_bind, Option.bind] at success
      cases cellResult : plan.cellBytes?
          (if overflowPageCount plan.overflowBytes = 0 then none else some next) with
      | none => simp [cellResult] at success
      | some cell =>
          simp only [cellResult] at success
          cases pagesResult : makeOverflowPages? next plan.overflowBytes with
          | none => simp [pagesResult] at success
          | some pages =>
              simp only [pagesResult] at success
              cases restResult : resolvePlans (next + pages.length) plans with
              | none => simp [restResult] at success
              | some rest =>
                  simp only [restResult, Option.some.injEq] at success
                  subst resolved
                  simp only [List.length_cons]
                  rw [resolvePlans_cells_length restResult]

theorem resolvePlans_nextPage : ∀ {next : Nat} {plans : List CellPlan}
    {resolved : Resolved}, resolvePlans next plans = some resolved →
      resolved.nextPage = next + resolved.pages.length
  | _, [], resolved, success => by
      simp only [resolvePlans, Option.some.injEq] at success
      subst resolved
      simp
  | next, plan :: plans, resolved, success => by
      simp only [resolvePlans, Option.bind_eq_bind, Option.bind] at success
      cases cellResult : plan.cellBytes?
          (if overflowPageCount plan.overflowBytes = 0 then none else some next) with
      | none => simp [cellResult] at success
      | some cell =>
          simp only [cellResult] at success
          cases pagesResult : makeOverflowPages? next plan.overflowBytes with
          | none => simp [pagesResult] at success
          | some pages =>
              simp only [pagesResult] at success
              cases restResult : resolvePlans (next + pages.length) plans with
              | none => simp [restResult] at success
              | some rest =>
                  simp only [restResult, Option.some.injEq] at success
                  subst resolved
                  simp only [List.length_append]
                  rw [resolvePlans_nextPage restResult]
                  omega

/-- If resolution emitted no overflow pages, it is exactly the pointwise
`none`-pointer cell encoding and leaves the allocation cursor unchanged. -/
theorem resolvePlans_noOverflow : ∀ {next : Nat} {plans : List CellPlan}
    {resolved : Resolved},
    resolvePlans next plans = some resolved → resolved.pages = [] →
      plans.mapM (fun plan => plan.cellBytes? none) = some resolved.cells ∧
      resolved.nextPage = next
  | _, [], resolved, success, empty => by
      simp only [resolvePlans, Option.some.injEq] at success
      subst resolved
      exact ⟨rfl, rfl⟩
  | next, plan :: plans, resolved, success, empty => by
      simp only [resolvePlans, Option.bind_eq_bind, Option.bind] at success
      cases cellResult : plan.cellBytes?
          (if overflowPageCount plan.overflowBytes = 0 then none else some next) with
      | none => simp [cellResult] at success
      | some cell =>
        simp only [cellResult] at success
        cases pagesResult : makeOverflowPages? next plan.overflowBytes with
        | none => simp [pagesResult] at success
        | some pages =>
          simp only [pagesResult] at success
          cases restResult : resolvePlans (next + pages.length) plans with
          | none => simp [restResult] at success
          | some rest =>
            simp only [restResult, Option.some.injEq] at success
            subst resolved
            have emptyParts : pages = [] ∧ rest.pages = [] :=
              List.append_eq_nil_iff.mp empty
            have countZero : overflowPageCount plan.overflowBytes = 0 := by
              have pageLength := makeOverflowPages?_length pagesResult
              rw [emptyParts.1] at pageLength
              simpa using pageLength.symm
            have headCell : plan.cellBytes? none = some cell := by
              simpa [countZero] using cellResult
            have tail := resolvePlans_noOverflow restResult emptyParts.2
            constructor
            · rw [List.mapM_cons, headCell, tail.1]
              rfl
            · rw [tail.2, emptyParts.1]
              rfl

/-- A cell that can be encoded without an overflow pointer has no overflow
suffix.  This is the converse fact needed to lift the inline page encoder into
the general overflow-aware encoder. -/
theorem CellPlan.overflowBytes_eq_nil_of_cellBytes_none
    {plan : CellPlan} {cell : List UInt8}
    (built : plan.cellBytes? none = some cell) :
    plan.overflowBytes = [] := by
  unfold CellPlan.cellBytes? at built
  split at built
  next fits =>
    unfold CellPlan.overflowBytes
    cases kind : plan.kind with
    | table =>
        simp only [localSize]
        rw [tableLeafLocalPayloadSize_eq_payload_of_fits
          PhysicalCodec.usablePageSize plan.payload.length (by
            simpa [maxLocal, kind] using fits)]
        exact List.drop_length
    | index =>
        simp only [localSize]
        rw [indexLocalPayloadSize_eq_payload_of_fits
          PhysicalCodec.usablePageSize plan.payload.length (by
            simpa [maxLocal, kind] using fits)]
        exact List.drop_length
  next => contradiction

/-- Pointwise no-pointer cell encodings resolve to exactly the same cells,
allocate no overflow pages, and preserve the allocation cursor. -/
theorem resolvePlans_of_cellBytes_none : ∀ (next : Nat)
    (plans : List CellPlan) (cells : List (List UInt8)),
    plans.mapM (fun plan => plan.cellBytes? none) = some cells →
    resolvePlans next plans = some ⟨cells, [], next⟩
  | _, [], cells, built => by
      change some [] = some cells at built
      have equal : cells = [] := (Option.some.inj built).symm
      subst cells
      rfl
  | next, plan :: plans, cells, built => by
      simp only [List.mapM_cons] at built
      cases cellResult : plan.cellBytes? none with
      | none => simp [cellResult] at built
      | some cell =>
          simp only [cellResult, Option.bind_eq_bind, Option.bind] at built
          cases tailResult : plans.mapM (fun candidate =>
              candidate.cellBytes? none) with
          | none => simp [tailResult] at built
          | some tail =>
              simp only [tailResult, Option.some.injEq] at built
              have cellsEqual : cells = cell :: tail :=
                (Option.some.inj built).symm
              subst cells
              have noOverflow :=
                plan.overflowBytes_eq_nil_of_cellBytes_none cellResult
              have countZero : overflowPageCount plan.overflowBytes = 0 :=
                (overflowPageCount_eq_zero_iff plan.overflowBytes).2 noOverflow
              have tailResolved := resolvePlans_of_cellBytes_none next plans
                tail tailResult
              simp only [resolvePlans, countZero, if_pos, cellResult,
                Option.bind_eq_bind, Option.bind]
              rw [makeOverflowPages?_eq, noOverflow]
              simp only [overflowPageCount, List.isEmpty_nil, if_pos,
                List.range_zero, List.map_nil, List.length_nil, Nat.add_zero,
                List.nil_append]
              rw [tailResolved]

def tableCellPlan? (schema : Core.Schema) (row : Core.Row) : Option CellPlan := do
  let record ← CoreRecord.rowRecord? schema row
  if bounded : record.encode.length < 2 ^ 64 then
    let size : U64Value := ⟨record.encode.length, by simpa using bounded⟩
    some {
      kind := .table
      cellPrefix := encodeVarint size ++
        encodeVarint (signedInteger64Bits row.rowid)
      payload := record.encode }
  else none

def indexCellPlan? (index : Core.Index) (row : Core.Row) : Option CellPlan := do
  let record ← CoreFile.indexRecord? index row
  if bounded : record.encode.length < 2 ^ 64 then
    let size : U64Value := ⟨record.encode.length, by simpa using bounded⟩
    some ⟨PayloadKind.index, encodeVarint size, record.encode⟩
  else none

def indexPlans (table : Core.Table) (index : Core.Index) : Option (List CellPlan) :=
  (CoreFile.sortedIndexRows table index).mapM (indexCellPlan? index)

def provisionalIndexStore? (plans : List CellPlan) :
    Option RecursivePageBTree.IndexStore := do
  let cells ← plans.mapM CellPlan.provisionalBytes?
  RecursivePageBTree.IndexStore.build? cells

/-- Compatibility projection for statements about the page graph.  Live
encoding retains the `IndexStore`; it does not reconstruct topology from this
view. -/
def provisionalIndexPlan? (plans : List CellPlan) :
    Option RecursivePageBTree.IndexPlan :=
  (provisionalIndexStore? plans).map (·.plan)

theorem provisionalIndexPlan?_balanced {plans : List CellPlan}
    {plan : RecursivePageBTree.IndexPlan}
    (built : provisionalIndexPlan? plans = some plan) : plan.Balanced := by
  unfold provisionalIndexPlan? at built
  cases storeResult : provisionalIndexStore? plans with
  | none => simp [storeResult] at built
  | some store =>
      simp only [storeResult, Option.map, Option.some.injEq] at built
      rw [← built]
      exact store.balanced

structure IndexEncoding where
  table : Core.Table
  index : Core.Index
  rootPage : Nat
  topology : RecursivePageBTree.IndexStore
  treePages : List CoreFile.Page
  overflowPages : List CoreFile.Page

def IndexEncoding.plan (encoding : IndexEncoding) :
    RecursivePageBTree.IndexPlan := encoding.topology.plan

def IndexEncoding.pages (encoding : IndexEncoding) : List CoreFile.Page :=
  encoding.treePages ++ encoding.overflowPages

def encodeIndex (rootPage : Nat) (table : Core.Table) (index : Core.Index) :
    Option IndexEncoding := do
  let plans ← indexPlans table index
  let provisional ← provisionalIndexStore? plans
  let resolved ← resolvePlans (rootPage + provisional.plan.pageCount) plans
  let topology ← provisional.retarget? resolved.cells
  let treePages ← topology.plan.encodePagesFrom rootPage
  some ⟨table, index, rootPage, topology, treePages, resolved.pages⟩

theorem encodeIndex_identity {rootPage : Nat} {table : Core.Table}
    {index : Core.Index} {encoding : IndexEncoding}
    (encoded : encodeIndex rootPage table index = some encoding) :
    encoding.table = table ∧ encoding.index = index ∧
      encoding.rootPage = rootPage := by
  unfold encodeIndex at encoded
  cases plansResult : indexPlans table index with
  | none => simp [plansResult] at encoded
  | some plans =>
    simp only [plansResult, Option.bind_eq_bind, Option.bind] at encoded
    cases provisionalResult : provisionalIndexStore? plans with
    | none => simp [provisionalResult] at encoded
    | some provisional =>
      simp only [provisionalResult] at encoded
      cases resolvedResult : resolvePlans
          (rootPage + provisional.plan.pageCount) plans with
      | none => simp [resolvedResult] at encoded
      | some resolved =>
        simp only [resolvedResult] at encoded
        cases topologyResult : provisional.retarget? resolved.cells with
        | none => simp [topologyResult] at encoded
        | some topology =>
          simp only [topologyResult] at encoded
          cases pagesResult : topology.plan.encodePagesFrom rootPage with
          | none => simp [pagesResult] at encoded
          | some pages =>
            simp only [pagesResult, Option.some.injEq] at encoded
            subst encoding
            exact ⟨rfl, rfl, rfl⟩

def IndexEncoding.catalogEntry (encoding : IndexEncoding) : CoreFile.CatalogEntry := {
  kind := "index"
  name := encoding.index.name
  table := encoding.table.schema.name
  rootPage := encoding.rootPage
  sql := CoreFile.indexSQL encoding.table encoding.index
  sqlIsNull := encoding.index.isImplicitPrimary encoding.table.schema }

def encodeIndexes : Nat → List (Core.Table × Core.Index) →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, indexed :: indexes => do
      let encoded ← encodeIndex nextPage indexed.1 indexed.2
      let remaining ← encodeIndexes (nextPage + encoded.pages.length) indexes
      some (encoded :: remaining)

theorem encodeIndexes_pairs : ∀ (nextPage : Nat)
    (indexes : List (Core.Table × Core.Index)) (encodings : List IndexEncoding),
    encodeIndexes nextPage indexes = some encodings →
    encodings.map (fun encoding => (encoding.table, encoding.index)) = indexes
  | _, [], encodings, encoded => by
      simp only [encodeIndexes, Option.some.injEq] at encoded
      subst encodings
      rfl
  | nextPage, indexed :: indexes, encodings, encoded => by
      simp only [encodeIndexes, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeIndex nextPage indexed.1 indexed.2 with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : encodeIndexes
            (nextPage + head.pages.length) indexes with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          have identity := encodeIndex_identity headResult
          simp [identity.1, identity.2.1,
            encodeIndexes_pairs (nextPage + head.pages.length) indexes tail
              tailResult]

def indexPagesOf (encodings : List IndexEncoding) : List CoreFile.Page :=
  encodings.flatMap IndexEncoding.pages

theorem encodeIndexes_member_range : ∀ (nextPage : Nat)
    (indexes : List (Core.Table × Core.Index))
    (encodings : List IndexEncoding),
    encodeIndexes nextPage indexes = some encodings →
    ∀ encoding ∈ encodings,
      nextPage ≤ encoding.rootPage ∧
      encoding.rootPage + encoding.pages.length ≤
        nextPage + (indexPagesOf encodings).length
  | _, [], encodings, encoded => by
      simp only [encodeIndexes, Option.some.injEq] at encoded
      subst encodings
      simp
  | nextPage, indexed :: indexes, encodings, encoded => by
      simp only [encodeIndexes, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeIndex nextPage indexed.1 indexed.2 with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : encodeIndexes
            (nextPage + head.pages.length) indexes with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          intro encoding member
          simp only [List.mem_cons] at member
          have identity := encodeIndex_identity headResult
          simp only [indexPagesOf, List.flatMap_cons, List.length_append]
          rcases member with rfl | tailMember
          · constructor <;> omega
          · have range := encodeIndexes_member_range
                (nextPage + head.pages.length) indexes tail tailResult
                encoding tailMember
            simp only [indexPagesOf] at range
            constructor <;> omega

def indexEntriesOf (encodings : List IndexEncoding) : List CoreFile.CatalogEntry :=
  encodings.map IndexEncoding.catalogEntry

/-- Grouping wrapper for database reconstruction proofs. It preserves the
flat physical order but makes each table's contiguous index run explicit. -/
def encodeIndexTableGroups : Nat → List Core.Table →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let current ← encodeIndexes nextPage
        (table.indexes.map fun index => (table, index))
      let remaining ← encodeIndexTableGroups
        (nextPage + (indexPagesOf current).length) tables
      some (current ++ remaining)

theorem encodeIndexTableGroups_pairs : ∀ (nextPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups nextPage tables = some encodings →
    encodings.map (fun encoding => (encoding.table, encoding.index)) =
      tables.flatMap fun table => table.indexes.map fun index => (table, index)
  | _, [], encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.some.injEq] at encoded
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind]
        at encoded
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : encodeIndexTableGroups
            (nextPage + (indexPagesOf current).length) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult, Option.some.injEq] at encoded
          subst encodings
          simp only [List.map_append, List.flatMap_cons]
          rw [encodeIndexes_pairs nextPage _ current currentResult,
            encodeIndexTableGroups_pairs
              (nextPage + (indexPagesOf current).length) tables remaining
              remainingResult]

theorem encodeIndexTableGroups_tables {nextPage : Nat}
    {tables : List Core.Table} {encodings : List IndexEncoding}
    (encoded : encodeIndexTableGroups nextPage tables = some encodings) :
    ∀ encoding ∈ encodings, encoding.table ∈ tables := by
  have pairs := encodeIndexTableGroups_pairs nextPage tables encodings encoded
  intro encoding member
  have pairMember : (encoding.table, encoding.index) ∈
      encodings.map (fun candidate => (candidate.table, candidate.index)) :=
    List.mem_map_of_mem member
  rw [pairs] at pairMember
  simp only [List.mem_flatMap, List.mem_map] at pairMember
  rcases pairMember with ⟨table, tableMember, index, _, equal⟩
  injection equal with tableEqual
  simpa [tableEqual] using tableMember

theorem encodeIndexTableGroups_member_range : ∀ (nextPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups nextPage tables = some encodings →
    ∀ encoding ∈ encodings,
      nextPage ≤ encoding.rootPage ∧
      encoding.rootPage + encoding.pages.length ≤
        nextPage + (indexPagesOf encodings).length
  | _, [], encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.some.injEq] at encoded
      subst encodings
      simp
  | nextPage, table :: tables, encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind]
        at encoded
      cases currentResult : encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : encodeIndexTableGroups
            (nextPage + (indexPagesOf current).length) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult, Option.some.injEq] at encoded
          subst encodings
          intro encoding member
          simp only [List.mem_append] at member
          simp only [indexPagesOf, List.flatMap_append, List.length_append]
          rcases member with currentMember | remainingMember
          · have range := encodeIndexes_member_range nextPage _ current
                currentResult encoding currentMember
            simp only [indexPagesOf] at range
            constructor <;> omega
          · have range := encodeIndexTableGroups_member_range
                (nextPage + (List.flatMap IndexEncoding.pages current).length)
                tables remaining remainingResult encoding remainingMember
            simp only [indexPagesOf] at range
            constructor <;> omega

end CoreOverflow
end SQLeanite
