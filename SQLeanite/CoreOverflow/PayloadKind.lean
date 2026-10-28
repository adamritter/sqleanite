import SQLeanite.CoreFile.Page

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

/-- Folding by cons builds the reverse of `values` in front of an existing
reversed accumulator.  This small algebraic fact is the ordering argument for
the stack-safe overflow resolver below. -/
theorem foldl_cons_eq_reverse_append (values accumulator : List α) :
    values.foldl (fun reversed value => value :: reversed) accumulator =
      values.reverse ++ accumulator := by
  induction values generalizing accumulator with
  | nil => rfl
  | cons value values induction =>
      simp only [List.foldl_cons, induction, List.reverse_cons]
      simp [List.append_assoc]

/-- Tail-recursive implementation of `resolvePlans` for large physical
indexes.  The specification above waits for the complete tail before
constructing every cell and page list, giving it one native stack frame per
indexed row.  YCSB therefore aborted between 100k and 130k rows. -/
def resolvePlansGo : Nat → List CellPlan → List (List UInt8) →
    List CoreFile.Page → Option Resolved
  | next, [], reversedCells, reversedPages =>
      some ⟨reversedCells.reverse, reversedPages.reverse, next⟩
  | next, plan :: plans, reversedCells, reversedPages => do
      let overflow := plan.overflowBytes
      let count := overflowPageCount overflow
      let first := if count = 0 then none else some next
      let cell ← plan.cellBytes? first
      let pages ← makeOverflowPages? next overflow
      resolvePlansGo (next + pages.length) plans (cell :: reversedCells)
        (pages.foldl (fun reversed page => page :: reversed) reversedPages)

def resolvePlansTR (next : Nat) (plans : List CellPlan) : Option Resolved :=
  resolvePlansGo next plans [] []

theorem resolvePlansGo_eq (next : Nat) (plans : List CellPlan)
    (reversedCells : List (List UInt8))
    (reversedPages : List CoreFile.Page) :
    resolvePlansGo next plans reversedCells reversedPages =
      (resolvePlans next plans).map fun resolved =>
        ⟨reversedCells.reverse ++ resolved.cells,
          reversedPages.reverse ++ resolved.pages, resolved.nextPage⟩ := by
  induction plans generalizing next reversedCells reversedPages with
  | nil => simp [resolvePlansGo, resolvePlans]
  | cons plan plans induction =>
      simp only [resolvePlansGo, resolvePlans, Option.bind_eq_bind, Option.bind]
      cases cellResult : plan.cellBytes?
          (if overflowPageCount plan.overflowBytes = 0 then none else some next) with
      | none => simp [cellResult]
      | some cell =>
          simp only [cellResult]
          cases pagesResult : makeOverflowPages? next plan.overflowBytes with
          | none => simp [pagesResult]
          | some pages =>
              simp only [pagesResult]
              rw [induction]
              cases restResult : resolvePlans (next + pages.length) plans with
              | none => simp [restResult]
              | some rest =>
                  simp only [restResult, Option.map]
                  rw [foldl_cons_eq_reverse_append]
                  simp [List.append_assoc]

@[csimp] theorem resolvePlans_eq_resolvePlansTR :
    resolvePlans = resolvePlansTR := by
  funext next plans
  rw [resolvePlansTR, resolvePlansGo_eq]
  cases result : resolvePlans next plans <;> simp [result]

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

end CoreOverflow

end SQLeanite
