import SQLeanite.CoreOverflow.PayloadKind
import SQLeanite.RecursivePageBTree.IndexStore

namespace SQLeanite
namespace CoreOverflow
open FileFormat

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

/-- A logical row is inline when its SQLite record payload fits the table-leaf
local-payload bound.  This is deliberately a property of the record, not of a
particular encoder result: localized mutation may use it to prove that the
overflow-aware encoder cannot allocate hidden pages. -/
def RowInline (schema : Core.Schema) (row : Core.Row) : Prop :=
  ∀ record, CoreRecord.rowRecord? schema row = some record →
    record.encode.length ≤ maxLocal .table

/-- Literal schema used by the VeriBetrKV YCSB evaluation.  It is a rowid
table with a non-aliasing TEXT primary key, hence the declared key remains in
the record and Core's internal integer rowid is stored only in the cell
header. -/
def ycsbSchema : Core.Schema := {
  name := "usertable"
  columns := [
    { name := "ycsb_key", notNull := true, textPrimaryKey := true },
    { name := "field0" },
    Core.hiddenRowidColumn]
  primaryKey := 2
  declaredPrimaryKey := 0 }

def ycsbRow (rowid : Core.Integer) (key field : PhysicalCodec.Text) :
    Core.Row := {
  rowid
  values := [.text key, .text field, .integer rowid] }

/-- VeriBetrKV/YCSB uses a 64-bit-hash decimal key (`user` plus at most twenty
digits) and one 512-byte field.  Those literal records are comfortably below
SQLite's 4 KiB table-leaf local-payload limit, so the semantic premise of the
localized crash theorem is mechanically discharged for every benchmark row. -/
theorem ycsbRow_inline (rowid : Core.Integer)
    (key field : PhysicalCodec.Text)
    (keyBound : key.bytes.length ≤ 24)
    (fieldBound : field.bytes.length ≤ 512) :
    RowInline ycsbSchema (ycsbRow rowid key field) := by
  intro record encoded
  unfold CoreRecord.rowRecord? at encoded
  simp [CoreRecord.rowRecordFields, ycsbSchema, ycsbRow,
    Core.Schema.hasHiddenRowid] at encoded
  rcases encoded with ⟨bound, rfl⟩
  rw [PhysicalRecord.encode_length]
  simp only [PhysicalRecord.headerSize, PhysicalRecord.encodePayload,
    List.flatMap_cons, List.flatMap_nil, List.length_append,
    PhysicalCodec.Value.recordField, PhysicalCodec.Text.recordField,
    RecordField.encodePayload, List.length_nil, Nat.add_zero]
  have serialBound := encodeRecordSerialTypes_length_le
    [key.recordField, field.recordField]
  have headerBound := recordHeaderSize_le
    (encodeRecordSerialTypes [key.recordField, field.recordField]).length
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceMul] at serialBound
  change recordHeaderSize
      (encodeRecordSerialTypes [key.recordField, field.recordField]).length +
    (key.bytes.length + field.bytes.length) ≤ maxLocal .table
  simp only [maxLocal, PhysicalCodec.usablePageSize, PhysicalCodec.pageSize,
    tableLeafMaxLocal]
  omega

/-- Extensional row shape generated by the exact VeriBetrKV YCSB driver. -/
def YCSBRow (row : Core.Row) : Prop :=
  ∃ key field : PhysicalCodec.Text,
    row = ycsbRow row.rowid key field ∧
    key.bytes.length ≤ 24 ∧ field.bytes.length ≤ 512

theorem YCSBRow.inline {row : Core.Row} (shape : YCSBRow row) :
    RowInline ycsbSchema row := by
  rcases shape with ⟨key, field, equal, keyBound, fieldBound⟩
  rw [equal]
  exact ycsbRow_inline _ key field keyBound fieldBound

instance (schema : Core.Schema) (row : Core.Row) :
    Decidable (RowInline schema row) := by
  unfold RowInline
  infer_instance

/-- A successful table-cell plan for an inline row retains the semantic
payload bound. -/
theorem tableCellPlan_payload_le_of_inline
    {schema : Core.Schema} {row : Core.Row} {plan : CellPlan}
    (inline : RowInline schema row)
    (planned : tableCellPlan? schema row = some plan) :
    plan.payload.length ≤ maxLocal .table := by
  unfold tableCellPlan? at planned
  cases recordResult : CoreRecord.rowRecord? schema row with
  | none => simp [recordResult] at planned
  | some record =>
      simp only [recordResult, Option.bind_eq_bind, Option.bind] at planned
      split at planned
      next bounded =>
        injection planned with equal
        subst plan
        exact inline record recordResult
      next => contradiction

@[simp] theorem tableCellPlan_kind
    {schema : Core.Schema} {row : Core.Row} {plan : CellPlan}
    (planned : tableCellPlan? schema row = some plan) :
    plan.kind = .table := by
  unfold tableCellPlan? at planned
  cases recordResult : CoreRecord.rowRecord? schema row with
  | none => simp [recordResult] at planned
  | some record =>
      simp only [recordResult, Option.bind_eq_bind, Option.bind] at planned
      split at planned
      next =>
        injection planned with equal
        subst plan
        rfl
      next => contradiction

/-- Resolving plans whose payloads all fit locally cannot allocate an overflow
page.  Unlike a post-hoc `pages = []` check, this theorem states the reusable
input condition that rules overflow out. -/
theorem resolvePlans_pages_eq_nil_of_payload_le :
    ∀ {next : Nat} {plans : List CellPlan} {resolved : Resolved},
      resolvePlans next plans = some resolved →
      (∀ plan ∈ plans, plan.payload.length ≤ maxLocal plan.kind) →
      resolved.pages = []
  | _, [], resolved, success, _ => by
      simp only [resolvePlans, Option.some.injEq] at success
      subst resolved
      rfl
  | next, plan :: plans, resolved, success, fits => by
      simp only [resolvePlans, Option.bind_eq_bind, Option.bind] at success
      have headFits := fits plan (by simp)
      have noOverflow : plan.overflowBytes = [] := by
        unfold CellPlan.overflowBytes
        cases kind : plan.kind with
        | table =>
            simp only [localSize]
            rw [tableLeafLocalPayloadSize_eq_payload_of_fits
              PhysicalCodec.usablePageSize plan.payload.length (by
                simpa [maxLocal, kind] using headFits)]
            exact List.drop_length
        | index =>
            simp only [localSize]
            rw [indexLocalPayloadSize_eq_payload_of_fits
              PhysicalCodec.usablePageSize plan.payload.length (by
                simpa [maxLocal, kind] using headFits)]
            exact List.drop_length
      have countZero : overflowPageCount plan.overflowBytes = 0 :=
        (overflowPageCount_eq_zero_iff plan.overflowBytes).2 noOverflow
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
                  have pagesEmpty : pages = [] := by
                    rw [makeOverflowPages?_eq, noOverflow] at pagesResult
                    simp only [overflowPageCount, List.isEmpty_nil, if_pos,
                      List.range_zero, List.map_nil, Option.some.injEq] at pagesResult
                    exact pagesResult.symm
                  have tailFits : ∀ candidate ∈ plans,
                      candidate.payload.length ≤ maxLocal candidate.kind := by
                    intro candidate member
                    exact fits candidate (by simp [member])
                  have tailEmpty := resolvePlans_pages_eq_nil_of_payload_le
                    restResult tailFits
                  simp [pagesEmpty, tailEmpty]

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

end CoreOverflow

end SQLeanite
