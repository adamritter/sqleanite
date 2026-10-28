import SQLeanite.RecursivePageBTree.IndexPlanReplaceCellsBalanced

namespace SQLeanite
namespace RecursivePageBTree

/-- The single owner of an index page topology.  Construction performs the
byte-capacity pagination once; later payload-pointer resolution may replace
cells, but cannot silently choose a different page graph. -/
structure IndexStore where
  plan : IndexPlan
  cells : List (List UInt8)
  balanced : plan.Balanced
  represents : plan.toCells = cells

def IndexStore.build? (cells : List (List UInt8)) : Option IndexStore :=
  let leaves := CellPagination.paginateCells cells
  match built : buildIndex leaves with
  | none => none
  | some plan => some {
      plan
      cells
      balanced := buildIndex_balanced built
      represents := (buildIndex_toCells built).trans
        (CellPagination.flatten_paginateCells cells) }

theorem IndexStore.build?_cells {cells : List (List UInt8)}
    {store : IndexStore} (built : IndexStore.build? cells = some store) :
    store.cells = cells := by
  simp only [IndexStore.build?] at built
  split at built
  next => contradiction
  next plan result =>
    simp only [Option.some.injEq] at built
    subst store
    rfl

theorem IndexStore.build?_balanced {cells : List (List UInt8)}
    {store : IndexStore} (_built : IndexStore.build? cells = some store) :
    store.plan.Balanced := by
  exact store.balanced

/-- Retarget bytes in in-order positions without recomputing pagination.
This is the index analogue of retaining `PersistentPageTree.Store` identities
while changing its logical witness. -/
def IndexStore.retarget? (store : IndexStore)
    (cells : List (List UInt8)) : Option IndexStore :=
  match replaced : store.plan.withCells? cells with
  | none => none
  | some plan => some {
      plan
      cells
      balanced := IndexPlan.withCells?_balanced store.balanced replaced
      represents := IndexPlan.withCells?_toCells replaced }

theorem IndexStore.retarget?_pageCount {store updated : IndexStore}
    {cells : List (List UInt8)}
    (retargeted : store.retarget? cells = some updated) :
    updated.plan.pageCount = store.plan.pageCount := by
  unfold IndexStore.retarget? at retargeted
  split at retargeted
  next => contradiction
  next plan replaced =>
    simp only [Option.some.injEq] at retargeted
    subst updated
    exact IndexPlan.withCells?_pageCount replaced

theorem IndexStore.retarget?_represents {store updated : IndexStore}
    {cells : List (List UInt8)}
    (retargeted : store.retarget? cells = some updated) :
    updated.plan.toCells = cells := by
  unfold IndexStore.retarget? at retargeted
  split at retargeted
  next => contradiction
  next plan replaced =>
    simp only [Option.some.injEq] at retargeted
    subst updated
    exact IndexPlan.withCells?_toCells replaced

/-- Insert one encoded index cell while preserving the existing page graph.
The caller still has to prove that the changed leaf serializes within its
SQLite page; failure at that boundary falls back to the bulk encoder. -/
def IndexStore.insertAt? (store : IndexStore) (position : Nat)
    (cell : List UInt8) : Option IndexStore :=
  match inserted : store.plan.insertAt? position cell with
  | none => none
  | some plan => some {
      plan
      cells := insertCellAt position cell store.cells
      balanced := IndexPlan.insertAt?_balanced store.balanced inserted
      represents := by
        rw [IndexPlan.insertAt?_toCells inserted, store.represents] }

theorem IndexStore.insertAt?_pageCount {store updated : IndexStore}
    {position : Nat} {cell : List UInt8}
    (inserted : store.insertAt? position cell = some updated) :
    updated.plan.pageCount = store.plan.pageCount := by
  unfold IndexStore.insertAt? at inserted
  split at inserted
  next => contradiction
  next plan planInserted =>
    simp only [Option.some.injEq] at inserted
    subst updated
    exact IndexPlan.insertAt?_pageCount planInserted

theorem IndexStore.insertAt?_cells {store updated : IndexStore}
    {position : Nat} {cell : List UInt8}
    (inserted : store.insertAt? position cell = some updated) :
    updated.cells = insertCellAt position cell store.cells := by
  unfold IndexStore.insertAt? at inserted
  split at inserted
  next => contradiction
  next =>
    simp only [Option.some.injEq] at inserted
    subst updated
    rfl

theorem IndexStore.insertAt?_represents {store updated : IndexStore}
    {position : Nat} {cell : List UInt8}
    (inserted : store.insertAt? position cell = some updated) :
    updated.plan.toCells = insertCellAt position cell store.cells := by
  rw [updated.represents, IndexStore.insertAt?_cells inserted]

def IndexPlan.references (startPage : Nat) : IndexPlan → List PageReference
  | .leaf _ => []
  | .branch2 left _ right =>
      let leftRoot := startPage + 1
      let rightRoot := leftRoot + left.pageCount
      [⟨startPage, leftRoot⟩, ⟨startPage, rightRoot⟩] ++
        left.references leftRoot ++ right.references rightRoot
  | .branch3 left _ middle _ right =>
      let leftRoot := startPage + 1
      let middleRoot := leftRoot + left.pageCount
      let rightRoot := middleRoot + middle.pageCount
      [⟨startPage, leftRoot⟩, ⟨startPage, middleRoot⟩,
        ⟨startPage, rightRoot⟩] ++
        left.references leftRoot ++ middle.references middleRoot ++
        right.references rightRoot

theorem IndexPlan.references_bounded (plan : IndexPlan) (startPage : Nat)
    (reference : PageReference) (member : reference ∈ plan.references startPage) :
    startPage ≤ reference.parent ∧
    reference.parent < startPage + plan.pageCount ∧
    startPage < reference.child ∧
    reference.child < startPage + plan.pageCount := by
  induction plan generalizing startPage with
  | leaf cells => simp [IndexPlan.references] at member
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.references, List.mem_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at member
      rcases member with beforeRight | rightMember
      · rcases beforeRight with immediate | leftMember
        · rcases immediate with rfl | rfl
          all_goals
            have leftPositive := left.pageCount_pos
            have rightPositive := right.pageCount_pos
            simp only [IndexPlan.pageCount]
            omega
        · have bounded := leftInduction (startPage := startPage + 1)
            leftMember
          rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
          simp only [IndexPlan.pageCount]
          omega
      · have bounded := rightInduction
          (startPage := startPage + 1 + left.pageCount) rightMember
        rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
        simp only [IndexPlan.pageCount]
        omega
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.references, List.mem_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at member
      rcases member with beforeRight | rightMember
      · rcases beforeRight with beforeMiddle | middleMember
        · rcases beforeMiddle with immediate | leftMember
          · rcases immediate with rfl | rfl | rfl
            all_goals
              have leftPositive := left.pageCount_pos
              have middlePositive := middle.pageCount_pos
              have rightPositive := right.pageCount_pos
              simp only [IndexPlan.pageCount]
              omega
          · have bounded := leftInduction (startPage := startPage + 1)
              leftMember
            rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
            simp only [IndexPlan.pageCount]
            omega
        · have bounded := middleInduction
            (startPage := startPage + 1 + left.pageCount) middleMember
          rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
          simp only [IndexPlan.pageCount]
          omega
      · have bounded := rightInduction
          (startPage := startPage + 1 + left.pageCount + middle.pageCount)
          rightMember
        rcases bounded with ⟨parentLow, parentHigh, childLow, childHigh⟩
        simp only [IndexPlan.pageCount]
        omega

def indexInteriorPage? (children : List (Nat × List UInt8))
    (rightmostPage : Nat) : Option CoreFile.Page := do
  let rightmost ← boundedU32? rightmostPage
  let cells ← children.mapM fun child => do
    let childPage ← boundedU32? child.1
    some (PhysicalTableBTree.encodeU32Nat childPage.val ++ child.2)
  if fits : PhysicalTableBTree.InteriorPageFit cells then
    some {
      bytes := CoreFile.replaceFirst 2
        (PhysicalTableBTree.interiorPageBody rightmost cells)
      length_eq := by
        rw [CoreFile.replaceFirst_length]
        exact PhysicalTableBTree.interiorPageBody_length rightmost cells fits }
  else none

def IndexPlan.encodePagesFrom (startPage : Nat) :
    IndexPlan → Option (List CoreFile.Page)
  | .leaf cells => do
      let page ← CoreFile.indexLeafPage? cells
      some [page]
  | .branch2 left separator right => do
      let leftRoot := startPage + 1
      let rightRoot := leftRoot + left.pageCount
      let root ← indexInteriorPage? [(leftRoot, separator)] rightRoot
      let leftPages ← left.encodePagesFrom leftRoot
      let rightPages ← right.encodePagesFrom rightRoot
      some (root :: (leftPages ++ rightPages))
  | .branch3 left firstSeparator middle secondSeparator right => do
      let leftRoot := startPage + 1
      let middleRoot := leftRoot + left.pageCount
      let rightRoot := middleRoot + middle.pageCount
      let root ← indexInteriorPage?
        [(leftRoot, firstSeparator), (middleRoot, secondSeparator)] rightRoot
      let leftPages ← left.encodePagesFrom leftRoot
      let middlePages ← middle.encodePagesFrom middleRoot
      let rightPages ← right.encodePagesFrom rightRoot
      some (root :: (leftPages ++ middlePages ++ rightPages))

theorem IndexPlan.encodePagesFrom_length {plan : IndexPlan} {startPage : Nat}
    {pages : List CoreFile.Page} (encoded : plan.encodePagesFrom startPage = some pages) :
    pages.length = plan.pageCount := by
  induction plan generalizing startPage pages with
  | leaf cells =>
      simp only [IndexPlan.encodePagesFrom, Option.bind_eq_bind, Option.bind]
        at encoded
      cases pageResult : CoreFile.indexLeafPage? cells with
      | none => simp [pageResult] at encoded
      | some page =>
        simp only [pageResult, Option.some.injEq] at encoded
        subst pages
        rfl
  | branch2 left separator right leftInduction rightInduction =>
      simp only [IndexPlan.encodePagesFrom, Option.bind_eq_bind, Option.bind]
        at encoded
      cases rootResult : indexInteriorPage?
          [(startPage + 1, separator)]
          (startPage + 1 + left.pageCount) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult] at encoded
        cases leftResult : left.encodePagesFrom (startPage + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases rightResult : right.encodePagesFrom
              (startPage + 1 + left.pageCount) with
          | none => simp [rightResult] at encoded
          | some rightPages =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst pages
            simp only [List.length_cons, List.length_append,
              IndexPlan.pageCount]
            rw [leftInduction leftResult, rightInduction rightResult]
            omega
  | branch3 left firstSeparator middle secondSeparator right
      leftInduction middleInduction rightInduction =>
      simp only [IndexPlan.encodePagesFrom, Option.bind_eq_bind, Option.bind]
        at encoded
      cases rootResult : indexInteriorPage?
          [(startPage + 1, firstSeparator),
            (startPage + 1 + left.pageCount, secondSeparator)]
          (startPage + 1 + left.pageCount + middle.pageCount) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult] at encoded
        cases leftResult : left.encodePagesFrom (startPage + 1) with
        | none => simp [leftResult] at encoded
        | some leftPages =>
          simp only [leftResult] at encoded
          cases middleResult : middle.encodePagesFrom
              (startPage + 1 + left.pageCount) with
          | none => simp [middleResult] at encoded
          | some middlePages =>
            simp only [middleResult] at encoded
            cases rightResult : right.encodePagesFrom
                (startPage + 1 + left.pageCount + middle.pageCount) with
            | none => simp [rightResult] at encoded
            | some rightPages =>
              simp only [rightResult, Option.some.injEq] at encoded
              subst pages
              simp only [List.length_cons, List.length_append,
                IndexPlan.pageCount]
              rw [leftInduction leftResult, middleInduction middleResult,
                rightInduction rightResult]
              omega

structure TableEncoding where
  table : Core.Table
  rootPage : Nat
  plan : Plan
  pages : List CoreFile.Page

def encodeTable (rootPage : Nat) (table : Core.Table) : Option TableEncoding := do
  let leaves ← CoreFile.tableLeaves table
  let plan ← build leaves
  let pages ← plan.encodePagesFrom rootPage
  some ⟨table, rootPage, plan, pages⟩

/-- Physical planning refines the table's row-cell sequence, not merely its
length: every encoded cell occurs once and in rowid order. -/
theorem encodeTable_refines {rootPage : Nat} {table : Core.Table}
    {encoding : TableEncoding} (encoded : encodeTable rootPage table = some encoding) :
    ∃ cells leaves,
      CoreFile.tableCells table = some cells ∧
      CoreFile.tableLeaves table = some leaves ∧
      encoding.plan.toCells = cells := by
  unfold encodeTable at encoded
  cases leavesResult : CoreFile.tableLeaves table with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : build leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        unfold CoreFile.tableLeaves at leavesResult
        cases cellsResult : CoreFile.tableCells table with
        | none => simp [cellsResult] at leavesResult
        | some cells =>
          simp only [cellsResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at leavesResult
          subst leaves
          refine ⟨cells, CellPagination.paginateCells cells, rfl, ?_, ?_⟩
          · simp [CoreFile.tableLeaves, cellsResult]
          · rw [build_toCells planResult]
            exact CellPagination.flatten_paginateCells cells

def TableEncoding.catalogEntry (encoding : TableEncoding) : CoreFile.CatalogEntry := {
  kind := "table"
  name := encoding.table.schema.name
  table := encoding.table.schema.name
  rootPage := encoding.rootPage
  sql := CoreFile.tableSQL encoding.table }

theorem encodeTable_table {rootPage : Nat} {table : Core.Table}
    {encoding : TableEncoding} (encoded : encodeTable rootPage table = some encoding) :
    encoding.table = table := by
  unfold encodeTable at encoded
  cases leavesResult : CoreFile.tableLeaves table with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : build leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        rfl

def encodeTables : Nat → List Core.Table → Option (List TableEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let encoded ← encodeTable nextPage table
      let remaining ← encodeTables (nextPage + encoded.plan.pageCount) tables
      some (encoded :: remaining)

def tablePagesOf (encodings : List TableEncoding) : List CoreFile.Page :=
  encodings.flatMap (fun encoding => encoding.pages)

def tableEntriesOf (encodings : List TableEncoding) : List CoreFile.CatalogEntry :=
  encodings.map TableEncoding.catalogEntry

theorem encodeTable_pages_length {rootPage : Nat} {table : Core.Table}
    {encoding : TableEncoding} (encoded : encodeTable rootPage table = some encoding) :
    encoding.pages.length = encoding.plan.pageCount := by
  unfold encodeTable at encoded
  cases leavesResult : CoreFile.tableLeaves table with
  | none => simp [leavesResult] at encoded
  | some leaves =>
    simp only [leavesResult, Option.bind_eq_bind, Option.bind] at encoded
    cases planResult : build leaves with
    | none => simp [planResult] at encoded
    | some plan =>
      simp only [planResult] at encoded
      cases pagesResult : plan.encodePagesFrom rootPage with
      | none => simp [pagesResult] at encoded
      | some pages =>
        simp only [pagesResult, Option.some.injEq] at encoded
        subst encoding
        exact plan.encodePagesFrom_length pagesResult

theorem encodeTables_tables : ∀ (nextPage : Nat) (tables : List Core.Table)
    (encodings : List TableEncoding), encodeTables nextPage tables = some encodings →
      encodings.map (fun encoding => encoding.table) = tables
  | _, [], encodings, encoded => by
      simp only [encodeTables, Option.some.injEq] at encoded
      subst encodings
      rfl
  | nextPage, table :: tables, encodings, encoded => by
      simp only [encodeTables, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeTable nextPage table with
      | none => simp [headResult] at encoded
      | some head =>
        simp only [headResult] at encoded
        cases tailResult : encodeTables
            (nextPage + head.plan.pageCount) tables with
        | none => simp [tailResult] at encoded
        | some tail =>
          simp only [tailResult, Option.some.injEq] at encoded
          subst encodings
          have headTable : head.table = table := encodeTable_table headResult
          simp [headTable,
            encodeTables_tables (nextPage + head.plan.pageCount) tables tail
              tailResult]

structure IndexEncoding where
  table : Core.Table
  index : Core.Index
  rootPage : Nat
  plan : IndexPlan
  pages : List CoreFile.Page

def encodeIndex (rootPage : Nat) (table : Core.Table) (index : Core.Index) :
    Option IndexEncoding := do
  let leaves ← CoreFile.indexLeaves table index
  let plan ← buildIndex leaves
  let pages ← plan.encodePagesFrom rootPage
  some ⟨table, index, rootPage, plan, pages⟩

end RecursivePageBTree

end SQLeanite
