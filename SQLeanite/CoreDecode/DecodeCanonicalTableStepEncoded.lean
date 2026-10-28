import SQLeanite.CoreTextEncoding
import SQLeanite.CoreDecode.DecodeCanonicalCatalogSchemaPageForEntries
import SQLeanite.CoreOverflow.EncodeIndexesMemberRange

namespace SQLeanite
namespace CoreDecode
set_option backward.isDefEq.respectTransparency false
attribute [local simp] bind pure Functor.map
open FileFormat

theorem decodeCanonicalTableStep_encoded (table : Core.Table)
    (layout : CoreFile.TableLayout) {cells : List (List UInt8)}
    {physicalPages : List CoreFile.Page}
    (encoded : CoreFile.tableCells table = some cells)
    (paged : CoreFile.tableLeaves table = some layout.leaves)
    (built : CoreFile.tablePages? layout = some physicalPages)
    (suffix : List (List UInt8)) :
    let entry : CoreFile.CatalogEntry := {
      kind := "table"
      name := table.schema.name
      table := table.schema.name
      rootPage := layout.rootPage
      sql := CoreFile.tableSQL table }
    decodeCanonicalTableStep layout.rootPage (CatalogEntry.ofEncoded entry)
      (physicalPages.map CoreFile.Page.bytes ++ suffix) =
        some (table.withoutIndexes, physicalPages.length, suffix) := by
  dsimp only
  unfold decodeCanonicalTableStep CatalogEntry.ofEncoded CoreFile.tableSQL
  simp only [Bool.false_eq_true, if_false]
  simp only [dif_pos True.intro]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseTableSchema_catalogSQL table]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [dif_pos True.intro]
  have groupDecoded := decodeCanonicalTableGroup_tablePages table layout encoded paged built
  have leavesNonempty : layout.leaves ≠ [] := by
    unfold CoreFile.tableLeaves at paged
    rw [encoded] at paged
    simp only [Option.bind_eq_bind, Option.bind, Option.some.injEq] at paged
    rw [← paged]
    exact CellPagination.paginateCells_nonempty cells
  cases leavesShape : layout.leaves with
  | nil => exact absurd leavesShape leavesNonempty
  | cons first rest =>
    cases restShape : rest with
    | nil =>
      unfold CoreFile.tablePages? at built
      rw [leavesShape, restShape] at built
      cases pageResult : CoreFile.tableLeafPage? first with
      | none => simp [pageResult] at built
      | some page =>
          simp only [pageResult, Option.bind_eq_bind, Option.bind] at built
          injection built with equal
          subst physicalPages
          simp only [List.map_cons, List.map_nil, List.nil_append,
            List.cons_append]
          rw [canonicalInteriorLeafCount_tableLeafPage pageResult]
          simp only [Option.bind_eq_bind, Option.bind]
          simp only [List.map_cons, List.map_nil] at groupDecoded
          rw [groupDecoded]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [Core.Table.rebuildFromCatalog_catalogSQL, Core.Table.rebuild_withoutIndexes]
          rfl
    | cons second remaining =>
      unfold CoreFile.tablePages? at built
      rw [leavesShape, restShape] at built
      cases rootResult : CoreFile.tableInteriorPage?
          (layout.rootPage + 1) layout.leaves with
      | none =>
        have rootResult' : CoreFile.tableInteriorPage?
            (layout.rootPage + 1) (first :: second :: remaining) = none := by
          simpa [leavesShape, restShape] using rootResult
        simp [rootResult'] at built
      | some root =>
        have rootResult' : CoreFile.tableInteriorPage?
            (layout.rootPage + 1) (first :: second :: remaining) = some root := by
          simpa [leavesShape, restShape] using rootResult
        simp only [rootResult', Option.bind_eq_bind, Option.bind] at built
        cases leafPagesResult : layout.leaves.mapM CoreFile.tableLeafPage? with
        | none =>
          have leafPagesResult' :
              (first :: second :: remaining).mapM CoreFile.tableLeafPage? = none := by
            simpa [leavesShape, restShape] using leafPagesResult
          simp [leafPagesResult'] at built
        | some leafPages =>
          have leafPagesResult' :
              (first :: second :: remaining).mapM CoreFile.tableLeafPage? =
                some leafPages := by
            simpa [leavesShape, restShape] using leafPagesResult
          simp only [leafPagesResult', Option.bind_eq_bind, Option.bind] at built
          injection built with equal
          subst physicalPages
          have leafCount := canonicalInteriorLeafCount_tableInteriorPage
            (layout.rootPage + 1) layout.leaves (by simp [leavesShape, restShape])
            rootResult
          have pageCount := mapM_length_of_eq_some CoreFile.tableLeafPage?
            layout.leaves leafPages leafPagesResult
          let leafBytes := leafPages.map CoreFile.Page.bytes
          have byteCount : leafBytes.length = layout.leaves.length := by
            simp [leafBytes, pageCount]
          simp only [List.map_cons, List.cons_append]
          rw [leafCount]
          simp only [Option.bind_eq_bind, Option.bind]
          have takeLeaves : (leafBytes ++ suffix).take layout.leaves.length = leafBytes := by
            rw [← byteCount]
            simp
          have dropLeaves : (leafBytes ++ suffix).drop layout.leaves.length = suffix := by
            rw [← byteCount]
            simp
          rw [takeLeaves, dif_pos byteCount, dropLeaves]
          simp only [List.map_cons] at groupDecoded
          change decodeCanonicalTableGroup table.schema
            (root.bytes :: leafBytes) = some table.rows at groupDecoded
          rw [groupDecoded]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [Core.Table.rebuildFromCatalog_catalogSQL, Core.Table.rebuild_withoutIndexes]
          simp [leafBytes]
          rfl

theorem decodeCanonicalTables_encodeTables :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreFile.TableEncoding)
      (indexSuffix : List (List UInt8)),
      CoreFile.encodeTables nextPage tables = some encodings →
      decodeCanonicalTables nextPage
        ((CoreFile.tableEntriesFor tables
          (CoreFile.tableLayoutsOf encodings)).map CatalogEntry.ofEncoded)
        ((CoreFile.tablePagesOf encodings).map CoreFile.Page.bytes ++ indexSuffix) =
          some (tables.map Core.Table.withoutIndexes, indexSuffix)
  | _, [], encodings, indexSuffix, encodedTables => by
      simp only [CoreFile.encodeTables] at encodedTables
      injection encodedTables with equal
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, indexSuffix, encodedTables => by
      simp only [CoreFile.encodeTables, Option.bind_eq_bind, Option.bind] at encodedTables
      cases leavesResult : CoreFile.tableLeaves table with
      | none => simp [leavesResult] at encodedTables
      | some leaves =>
        simp only [leavesResult] at encodedTables
        let layout : CoreFile.TableLayout := ⟨nextPage, leaves⟩
        cases pagesResult : CoreFile.tablePages? layout with
        | none => simp [layout, pagesResult] at encodedTables
        | some physicalPages =>
          simp only [layout, pagesResult] at encodedTables
          cases remainingResult : CoreFile.encodeTables
              (nextPage + CoreFile.tableFootprint leaves) tables with
          | none => simp [remainingResult] at encodedTables
          | some remaining =>
            simp only [remainingResult] at encodedTables
            injection encodedTables with equal
            subst encodings
            cases cellsResult : CoreFile.tableCells table with
            | none =>
              unfold CoreFile.tableLeaves at leavesResult
              simp [cellsResult] at leavesResult
            | some cells =>
              have step := decodeCanonicalTableStep_encoded table layout cellsResult
                (by simpa [layout] using leavesResult) pagesResult
                ((CoreFile.tablePagesOf remaining).map CoreFile.Page.bytes ++ indexSuffix)
              have pageLength := CoreFile.tablePages_length_of_success pagesResult
              have rest := decodeCanonicalTables_encodeTables
                (nextPage + CoreFile.tableFootprint leaves) tables remaining
                indexSuffix remainingResult
              simp only [CoreFile.tableLayoutsOf, CoreFile.tablePagesOf,
                CoreFile.tableEntriesFor, List.map_cons, List.flatMap_cons,
                List.map_append]
              simp only [List.append_assoc]
              dsimp only at step
              unfold CoreFile.tablePagesOf at step rest
              unfold CoreFile.tableLayoutsOf at rest
              dsimp [layout] at step pageLength
              unfold decodeCanonicalTables
              rw [step]
              simp only [Option.bind_eq_bind, Option.bind]
              rw [pageLength, rest]

def page? (pages : List (List UInt8)) (pageNumber : Nat) : Option (List UInt8) :=
  if _positive : 0 < pageNumber then pages[pageNumber - 1]? else none

/-- Read-only pager boundary used by recursive table and index traversal. A
decoder asks only for pages reachable from a root; the backing store decides
whether those pages are already resident, cached, or read on demand. -/
structure PageSource where
  pageCount : Nat
  readPage : Nat → Option (List UInt8)

def PageSource.ofList (physicalPages : List (List UInt8)) : PageSource := {
  pageCount := physicalPages.length
  readPage := page? physicalPages }

/-- Effectful counterpart of `PageSource`.  The parser and tree algorithms
remain pure Lean; only page acquisition is effectful, permitting a file-backed
pager to fetch a reachable page on demand. -/
structure IOPageSource where
  usable : UsablePageSize := PhysicalCodec.usablePageSize
  textEncoding : Nat := 1
  pageCount : Nat
  readPage : Nat → IO (Option (List UInt8))
  observeRow : Option (Core.Schema → Core.Row → List RecordField → IO Unit) := none


/-- Observe original fields only after the ordinary record/schema checks have
succeeded. Both production row readers call this same effectful boundary. -/
def finishRowRead (schema : Core.Schema) (source : IOPageSource) (rowid : Core.Integer)
    (physical fields : List RecordField) : IO (Option Core.Row) := do
  let decoded := CoreRecord.decodeRowFields schema rowid fields
  if let some row := decoded then
    if let some observe := source.observeRow then observe schema row physical
  return decoded


theorem finishRowRead_unobserved (schema : Core.Schema) (source : IOPageSource)
    (rowid : Core.Integer) (physical fields : List RecordField)
    (unobserved : source.observeRow = none) :
    finishRowRead schema source rowid physical fields = pure (CoreRecord.decodeRowFields schema rowid fields) := by
  cases decoded : CoreRecord.decodeRowFields schema rowid fields <;>
    simp [finishRowRead, decoded, unobserved]

def sequenceOptions : List (Option α) → Option (List α)
  | [] => some []
  | some value :: rest => (sequenceOptions rest).map (value :: ·)
  | none :: _ => none

/-- Validate one decoded overflow page and either finish or invoke the
continuation on its successor. -/
def finishOverflowStep (recurse : Nat → Nat → Option (List UInt8))
    (remaining : Nat) (overflow : OverflowPage PhysicalCodec.usablePageSize)
    (suffix : List UInt8) : Option (List UInt8) :=
  if _consumed : suffix = [] then
    let amount := min remaining CoreOverflow.overflowCapacity
    let chunk := overflow.payload.bytes.take amount
    if _final : remaining ≤ CoreOverflow.overflowCapacity then
      match overflow.next with
      | .endOfChain => some chunk
      | .page _ => none
    else
      match overflow.next with
      | .endOfChain => none
      | .page next => do
          let rest ← recurse
            (remaining - CoreOverflow.overflowCapacity) next.value.val
          some (chunk ++ rest)
  else none

/-- Consume one nonempty logical segment of an overflow chain.  Factoring this
transition out of the fuel recursion keeps both the executable state machine
and its inverse theorem compositional. -/
def readOverflowStep (source : PageSource)
    (recurse : Nat → Nat → Option (List UInt8))
    (remaining pageNumber : Nat) : Option (List UInt8) := do
  let page ← source.readPage pageNumber
  let (overflow, suffix) ←
    decodeOverflowPage PhysicalCodec.usablePageSize page
  finishOverflowStep recurse remaining overflow suffix

/-- Resolve exactly the requested logical bytes from a SQLite overflow chain.
The page-count fuel rejects cycles and overlong malformed chains. -/
def readOverflowFrom (source : PageSource) :
    Nat → Nat → Nat → Option (List UInt8)
  | _, 0, _ => some []
  | 0, _ + 1, _ => none
  | fuel + 1, remaining, pageNumber =>
      readOverflowStep source (readOverflowFrom source fuel) remaining pageNumber

/-- The pages generated for one overflow payload are present at the page
numbers encoded in their next pointers.  This relation is intentionally about
page reads, not list positions, so the same inverse theorem applies to an
in-memory image and to a pager. -/
def ReadsGeneratedOverflow (source : PageSource) (start count : Nat)
    (bytes : List UInt8) : Prop :=
  ∀ offset, offset < count →
    source.readPage (start + offset) = some
      (CoreOverflow.overflowPageBytes start count offset bytes)

def ReadsPagesFrom (source : PageSource) (start : Nat)
    (pages : List CoreFile.Page) : Prop :=
  ∀ (offset : Nat) (inBounds : offset < pages.length),
    source.readPage (start + offset) = some pages[offset].bytes

theorem ReadsPagesFrom.left {source : PageSource} {start : Nat}
    {left right : List CoreFile.Page}
    (reads : ReadsPagesFrom source start (left ++ right)) :
    ReadsPagesFrom source start left := by
  intro offset inBounds
  have available := reads offset (by simp; omega)
  rw [List.getElem_append_left inBounds] at available
  exact available

theorem ReadsPagesFrom.right {source : PageSource} {start : Nat}
    {left right : List CoreFile.Page}
    (reads : ReadsPagesFrom source start (left ++ right)) :
    ReadsPagesFrom source (start + left.length) right := by
  intro offset inBounds
  have available := reads (left.length + offset) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at available
  have indexEq : left.length + offset - left.length = offset := by omega
  simpa only [indexEq, Nat.add_assoc] using available

theorem ReadsPagesFrom.ofList_append (leading : List (List UInt8))
    (pages : List CoreFile.Page) (suffix : List (List UInt8)) :
    ReadsPagesFrom
      (.ofList (leading ++ pages.map CoreFile.Page.bytes ++ suffix))
      (leading.length + 1) pages := by
  intro offset inBounds
  unfold PageSource.ofList page?
  dsimp only
  rw [dif_pos (by omega)]
  have indexEqual : leading.length + 1 + offset - 1 =
      leading.length + offset := by omega
  rw [indexEqual]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by omega)]
  have offsetEqual : leading.length + offset - leading.length = offset := by omega
  rw [offsetEqual, List.getElem?_map,
    List.getElem?_eq_getElem inBounds]
  rfl

theorem ReadsPagesFrom.ofList_tail (pages : List CoreFile.Page) :
    ReadsPagesFrom (.ofList (pages.map CoreFile.Page.bytes)) 2 pages.tail := by
  cases pages with
  | nil => simp [ReadsPagesFrom]
  | cons first rest =>
      simpa using ReadsPagesFrom.ofList_append [first.bytes] rest []

theorem ReadsPagesFrom.encodeOverflowIndexes (source : PageSource) :
    ∀ (nextPage : Nat) (indexes : List (Core.Table × Core.Index))
      (encodings : List CoreOverflow.IndexEncoding),
      CoreOverflow.encodeIndexes nextPage indexes = some encodings →
      ReadsPagesFrom source nextPage
        (CoreOverflow.indexPagesOf encodings) →
      ∀ encoding ∈ encodings,
        ReadsPagesFrom source encoding.rootPage encoding.pages
  | _, [], encodings, encoded, _ => by
      simp only [CoreOverflow.encodeIndexes, Option.some.injEq] at encoded
      subst encodings
      simp
  | nextPage, indexed :: indexes, encodings, encoded, reads => by
      simp only [CoreOverflow.encodeIndexes, Option.bind_eq_bind,
        Option.bind] at encoded
      cases headResult : CoreOverflow.encodeIndex nextPage indexed.1 indexed.2 with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : CoreOverflow.encodeIndexes
            (nextPage + head.pages.length) indexes with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          have normalized : ReadsPagesFrom source nextPage
              (head.pages ++ CoreOverflow.indexPagesOf tail) := by
            simpa [CoreOverflow.indexPagesOf] using reads
          have headReads : ReadsPagesFrom source nextPage head.pages :=
            ReadsPagesFrom.left normalized
          have tailReads : ReadsPagesFrom source
              (nextPage + head.pages.length)
              (CoreOverflow.indexPagesOf tail) :=
            ReadsPagesFrom.right normalized
          have identity := CoreOverflow.encodeIndex_identity headResult
          intro encoding member
          simp only [List.mem_cons] at member
          rcases member with rfl | tailMember
          · simpa [identity.2.2] using headReads
          · exact ReadsPagesFrom.encodeOverflowIndexes source
              (nextPage + head.pages.length) indexes tail tailResult tailReads
              encoding tailMember

theorem ReadsPagesFrom.encodeOverflowIndexTableGroups (source : PageSource) :
    ∀ (nextPage : Nat) (tables : List Core.Table)
      (encodings : List CoreOverflow.IndexEncoding),
      CoreOverflow.encodeIndexTableGroups nextPage tables = some encodings →
      ReadsPagesFrom source nextPage
        (CoreOverflow.indexPagesOf encodings) →
      ∀ encoding ∈ encodings,
        ReadsPagesFrom source encoding.rootPage encoding.pages
  | _, [], encodings, encoded, _ => by
      simp only [CoreOverflow.encodeIndexTableGroups, Option.some.injEq]
        at encoded
      subst encodings
      simp
  | nextPage, table :: tables, encodings, encoded, reads => by
      simp only [CoreOverflow.encodeIndexTableGroups, Option.bind_eq_bind,
        Option.bind] at encoded
      cases currentResult : CoreOverflow.encodeIndexes nextPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
        simp only [currentResult] at encoded
        cases remainingResult : CoreOverflow.encodeIndexTableGroups
            (nextPage + (CoreOverflow.indexPagesOf current).length) tables with
        | none => simp [remainingResult] at encoded
        | some remaining =>
          simp only [remainingResult, Option.some.injEq] at encoded
          subst encodings
          have normalized : ReadsPagesFrom source nextPage
              (CoreOverflow.indexPagesOf current ++
                CoreOverflow.indexPagesOf remaining) := by
            simpa [CoreOverflow.indexPagesOf] using reads
          have currentReads : ReadsPagesFrom source nextPage
              (CoreOverflow.indexPagesOf current) :=
            ReadsPagesFrom.left normalized
          have remainingReads : ReadsPagesFrom source
              (nextPage + (CoreOverflow.indexPagesOf current).length)
              (CoreOverflow.indexPagesOf remaining) :=
            ReadsPagesFrom.right normalized
          intro encoding member
          simp only [List.mem_append] at member
          rcases member with currentMember | remainingMember
          · exact ReadsPagesFrom.encodeOverflowIndexes source nextPage _ current
              currentResult currentReads encoding currentMember
          · exact ReadsPagesFrom.encodeOverflowIndexTableGroups source
              (nextPage + (CoreOverflow.indexPagesOf current).length) tables
              remaining remainingResult remainingReads encoding remainingMember

theorem readsGeneratedOverflow_of_makeOverflowPages
    (source : PageSource) (start : Nat) (bytes : List UInt8)
    (pages : List CoreFile.Page)
    (built : CoreOverflow.makeOverflowPages? start bytes = some pages)
    (reads : ReadsPagesFrom source start pages) :
    ReadsGeneratedOverflow source start
      (CoreOverflow.overflowPageCount bytes) bytes := by
  rw [CoreOverflow.makeOverflowPages?_eq] at built
  injection built with pagesEqual
  subst pages
  intro offset inBounds
  have available := reads offset (by simpa using inBounds)
  simpa [CoreOverflow.overflowPage] using available

set_option maxRecDepth 8192 in
theorem readOverflowFrom_generated_final (source : PageSource)
    (start : Nat) (bytes : List UInt8) (nonempty : bytes ≠ [])
    (fits : bytes.length ≤ CoreOverflow.overflowCapacity)
    (bounded : start + 1 < 2 ^ 32)
    (firstRead : source.readPage start = some
      (CoreOverflow.overflowPageBytes start 1 0 bytes)) :
    readOverflowFrom source 2 bytes.length start = some bytes := by
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

theorem finishOverflowStep_generated_step (count : Nat)
    (recurse : Nat → Nat → Option (List UInt8))
    (start : Nat) (bytes : List UInt8) (countPositive : 0 < count)
    (tooLarge : CoreOverflow.overflowCapacity < bytes.length)
    (bounded : start + (count + 1) < 2 ^ 32)
    (tailDecoded : recurse
      (bytes.drop CoreOverflow.overflowCapacity).length (start + 1) =
        some (bytes.drop CoreOverflow.overflowCapacity)) :
    finishOverflowStep recurse bytes.length
      (CoreOverflow.generatedOverflowPage start (count + 1) 0 bytes bounded) [] =
        some bytes := by
  unfold finishOverflowStep
  obtain ⟨next, nextEqual, nextValue⟩ :=
    CoreOverflow.generatedOverflowPage_next_step start count bytes
      countPositive bounded
  have payloadTake := CoreOverflow.generatedOverflowPage_payload_take_step
    start count bytes tooLarge bounded
  rw [dif_pos rfl, dif_neg (by omega), nextEqual]
  have minCapacity : min bytes.length CoreOverflow.overflowCapacity =
      CoreOverflow.overflowCapacity := Nat.min_eq_right (by omega)
  rw [minCapacity, payloadTake]
  have remaining : bytes.length - CoreOverflow.overflowCapacity =
      (bytes.drop CoreOverflow.overflowCapacity).length := by simp
  rw [remaining]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [nextValue, tailDecoded]
  exact congrArg some (List.take_append_drop _ bytes)

end CoreDecode

end SQLeanite
