import SQLeanite.CorePageCodec.DecodeTableInteriorEncodeChunkRootBranch2

namespace SQLeanite
namespace CorePageCodec

/-- A localized root-to-leaf encoding contains only pages from the complete
encoding of the same persistent tree.  It may omit unchanged siblings, but it
cannot invent a page identity or byte image. -/
theorem encodeChunkPath_subset_encodeChunkNode (schema : Core.Schema)
    (key : Nat) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (path pages : List NumberedPage),
      encodeChunkPath schema key node = some path →
      encodeChunkNode schema node = some pages →
      ∀ page ∈ path, page ∈ pages
  | .leaf pageId entries, path, pages, pathEncoded, pagesEncoded => by
      cases leafResult : encodeChunkLeaf schema entries with
      | none =>
        simp [encodeChunkPath, encodeChunkRoot, leafResult] at pathEncoded
      | some leaf =>
        simp [encodeChunkPath, encodeChunkRoot, encodeChunkNode, leafResult] at pathEncoded pagesEncoded
        subst path
        subst pages
        simp
  | .branch2 pageId left separator right, path, pages, pathEncoded,
      pagesEncoded => by
      cases keyResult : maximumChunkRowid? left with
      | none =>
        simp [encodeChunkPath, encodeChunkRoot, keyResult] at pathEncoded
      | some leftKey =>
        cases pageResult : RecursivePageBTree.interiorPage?
            [(left.rootId, leftKey)] right.rootId with
        | none =>
          simp [encodeChunkPath, encodeChunkRoot, keyResult, pageResult] at pathEncoded
        | some rootPage =>
          cases leftResult : encodeChunkNode schema left with
          | none =>
            simp [encodeChunkNode, keyResult, pageResult, leftResult] at pagesEncoded
          | some leftPages =>
            cases rightResult : encodeChunkNode schema right with
            | none =>
              simp [encodeChunkNode, keyResult, pageResult, leftResult,
                rightResult] at pagesEncoded
            | some rightPages =>
              simp [encodeChunkNode, keyResult, pageResult, leftResult,
                rightResult] at pagesEncoded
              subst pages
              by_cases route : key < separator
              · cases childResult : encodeChunkPath schema key left with
                | none =>
                  simp [encodeChunkPath, encodeChunkRoot, keyResult, pageResult,
                    route, childResult] at pathEncoded
                | some child =>
                  simp [encodeChunkPath, encodeChunkRoot, keyResult, pageResult,
                    route, childResult] at pathEncoded
                  subst path
                  intro page member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | childMember
                  · simp
                  · simp only [List.mem_cons, List.mem_append]
                    exact .inr (.inl
                      (encodeChunkPath_subset_encodeChunkNode schema key left
                        child leftPages childResult leftResult page childMember))
              · cases childResult : encodeChunkPath schema key right with
                | none =>
                  simp [encodeChunkPath, encodeChunkRoot, keyResult, pageResult,
                    route, childResult] at pathEncoded
                | some child =>
                  simp [encodeChunkPath, encodeChunkRoot, keyResult, pageResult,
                    route, childResult] at pathEncoded
                  subst path
                  intro page member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | childMember
                  · simp
                  · simp only [List.mem_cons, List.mem_append]
                    exact .inr (.inr
                      (encodeChunkPath_subset_encodeChunkNode schema key right
                        child rightPages childResult rightResult page childMember))
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      path, pages, pathEncoded, pagesEncoded => by
      cases leftKeyResult : maximumChunkRowid? left with
      | none =>
        simp [encodeChunkPath, encodeChunkRoot, leftKeyResult] at pathEncoded
      | some leftKey =>
        cases middleKeyResult : maximumChunkRowid? middle with
        | none =>
          simp [encodeChunkPath, encodeChunkRoot, leftKeyResult,
            middleKeyResult] at pathEncoded
        | some middleKey =>
          cases pageResult : RecursivePageBTree.interiorPage?
              [(left.rootId, leftKey), (middle.rootId, middleKey)]
              right.rootId with
          | none =>
            simp [encodeChunkPath, encodeChunkRoot, leftKeyResult,
              middleKeyResult, pageResult] at pathEncoded
          | some rootPage =>
            cases leftResult : encodeChunkNode schema left with
            | none =>
              simp [encodeChunkNode, leftKeyResult, middleKeyResult, pageResult,
                leftResult] at pagesEncoded
            | some leftPages =>
              cases middleResult : encodeChunkNode schema middle with
              | none =>
                simp [encodeChunkNode, leftKeyResult, middleKeyResult,
                  pageResult, leftResult, middleResult] at pagesEncoded
              | some middlePages =>
                cases rightResult : encodeChunkNode schema right with
                | none =>
                  simp [encodeChunkNode, leftKeyResult, middleKeyResult,
                    pageResult, leftResult, middleResult, rightResult] at pagesEncoded
                | some rightPages =>
                  simp [encodeChunkNode, leftKeyResult, middleKeyResult,
                    pageResult, leftResult, middleResult, rightResult] at pagesEncoded
                  subst pages
                  by_cases leftRoute : key < firstSeparator
                  · cases childResult : encodeChunkPath schema key left with
                    | none =>
                      simp [encodeChunkPath, encodeChunkRoot, leftKeyResult,
                        middleKeyResult, pageResult, leftRoute, childResult] at pathEncoded
                    | some child =>
                      simp [encodeChunkPath, encodeChunkRoot, leftKeyResult,
                        middleKeyResult, pageResult, leftRoute, childResult] at pathEncoded
                      subst path
                      intro page member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | childMember
                      · simp
                      · simp only [List.mem_cons, List.mem_append]
                        exact .inr (.inl
                          (encodeChunkPath_subset_encodeChunkNode schema key left
                            child leftPages childResult leftResult page childMember))
                  · by_cases middleRoute : key < secondSeparator
                    · cases childResult : encodeChunkPath schema key middle with
                      | none =>
                        simp [encodeChunkPath, encodeChunkRoot, leftKeyResult,
                          middleKeyResult, pageResult, leftRoute, middleRoute,
                          childResult] at pathEncoded
                      | some child =>
                        simp [encodeChunkPath, encodeChunkRoot, leftKeyResult,
                          middleKeyResult, pageResult, leftRoute, middleRoute,
                          childResult] at pathEncoded
                        subst path
                        intro page member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | childMember
                        · simp
                        · simp only [List.mem_cons, List.mem_append]
                          exact .inr (.inr (.inl
                            (encodeChunkPath_subset_encodeChunkNode schema key
                              middle child middlePages childResult middleResult
                              page childMember)))
                    · cases childResult : encodeChunkPath schema key right with
                      | none =>
                        simp [encodeChunkPath, encodeChunkRoot, leftKeyResult,
                          middleKeyResult, pageResult, leftRoute, middleRoute,
                          childResult] at pathEncoded
                      | some child =>
                        simp [encodeChunkPath, encodeChunkRoot, leftKeyResult,
                          middleKeyResult, pageResult, leftRoute, middleRoute,
                          childResult] at pathEncoded
                        subst path
                        intro page member
                        simp only [List.mem_cons] at member
                        rcases member with rfl | childMember
                        · simp
                        · simp only [List.mem_cons, List.mem_append]
                          exact .inr (.inr (.inr
                            (encodeChunkPath_subset_encodeChunkNode schema key
                              right child rightPages childResult rightResult page
                              childMember)))

def encodeChunkTable (state : CoreChunkPageState.TableState) :
    Option (List NumberedPage) :=
  encodeChunkNode state.table.schema state.tree.root

def encodeChunkTables : List CoreChunkPageState.TableState →
    Option (List NumberedPage)
  | [] => some []
  | table :: tables => do
      let head ← encodeChunkTable table
      let tail ← encodeChunkTables tables
      some (head ++ tail)

/-- A store-owned table encoding. Tree page identities come exclusively from
the persistent node; overflow pages are allocated after the entire identified
tree interval and therefore cannot perturb its topology. -/
structure OverflowEncoding where
  treePages : List NumberedPage
  overflowPages : List CoreFile.Page
  nextPage : Nat

/-- Every row stored below a persistent table node has a record payload which
fits in the local part of a SQLite table-leaf cell.  The recursive shape makes
the invariant compositional across page-local tree edits. -/
def NodeRowsInline (schema : Core.Schema) :
    PersistentPageTree.Node CoreChunkPageState.Chunk → Prop
  | .leaf _ entries => ∀ entry ∈ entries, ∀ row ∈ entry.2,
      CoreOverflow.RowInline schema row
  | .branch2 _ left _ right =>
      NodeRowsInline schema left ∧ NodeRowsInline schema right
  | .branch3 _ left _ middle _ right =>
      NodeRowsInline schema left ∧ NodeRowsInline schema middle ∧
        NodeRowsInline schema right

/-- A pointwise property of the logical row abstraction establishes the
recursive inline invariant, independent of the tree's current topology. -/
theorem nodeRowsInline_of_mem_rows (schema : Core.Schema) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk),
      (∀ row ∈ CoreChunkPageState.Node.rows node,
        CoreOverflow.RowInline schema row) →
      NodeRowsInline schema node
  | .leaf pageId entries, inline => by
      simp only [NodeRowsInline]
      intro entry entryMember row rowMember
      apply inline row
      unfold CoreChunkPageState.Node.rows
      simp only [PersistentPageTree.Node.erase,
        RecursiveBPlusTree.Node.toList]
      exact List.mem_flatMap.mpr ⟨entry, entryMember, rowMember⟩
  | .branch2 pageId left separator right, inline => by
      simp only [NodeRowsInline]
      constructor
      · apply nodeRowsInline_of_mem_rows schema left
        intro row member
        apply inline row
        unfold CoreChunkPageState.Node.rows at member ⊢
        simp only [PersistentPageTree.Node.erase,
          RecursiveBPlusTree.Node.toList, List.flatMap_append,
          List.mem_append]
        exact Or.inl member
      · apply nodeRowsInline_of_mem_rows schema right
        intro row member
        apply inline row
        unfold CoreChunkPageState.Node.rows at member ⊢
        simp only [PersistentPageTree.Node.erase,
          RecursiveBPlusTree.Node.toList, List.flatMap_append,
          List.mem_append]
        exact Or.inr member
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      inline => by
      simp only [NodeRowsInline]
      constructor
      · apply nodeRowsInline_of_mem_rows schema left
        intro row member
        apply inline row
        unfold CoreChunkPageState.Node.rows at member ⊢
        simp only [PersistentPageTree.Node.erase,
          RecursiveBPlusTree.Node.toList, List.flatMap_append,
          List.mem_append]
        exact Or.inl (Or.inl member)
      · constructor
        · apply nodeRowsInline_of_mem_rows schema middle
          intro row member
          apply inline row
          unfold CoreChunkPageState.Node.rows at member ⊢
          simp only [PersistentPageTree.Node.erase,
            RecursiveBPlusTree.Node.toList, List.flatMap_append,
            List.mem_append]
          exact Or.inl (Or.inr member)
        · apply nodeRowsInline_of_mem_rows schema right
          intro row member
          apply inline row
          unfold CoreChunkPageState.Node.rows at member ⊢
          simp only [PersistentPageTree.Node.erase,
            RecursiveBPlusTree.Node.toList, List.flatMap_append,
            List.mem_append]
          exact Or.inr member

/-- A table state's logical representation equation lifts a row-wise payload
bound to the exact persistent tree used by the localized writer. -/
theorem tableStateRowsInline_of_rows
    (state : CoreChunkPageState.TableState)
    (inline : ∀ row ∈ state.table.rows,
      CoreOverflow.RowInline state.table.schema row) :
    NodeRowsInline state.table.schema state.tree.root := by
  apply nodeRowsInline_of_mem_rows state.table.schema state.tree.root
  intro row member
  apply inline row
  rw [← state.represents]
  exact member

/-- Exact logical table condition used by the paper's YCSB evaluation. -/
def YCSBTableState (state : CoreChunkPageState.TableState) : Prop :=
  state.table.schema = CoreOverflow.ycsbSchema ∧
    ∀ row ∈ state.table.rows, CoreOverflow.YCSBRow row

theorem YCSBTableState.rowsInline
    {state : CoreChunkPageState.TableState}
    (shape : YCSBTableState state) :
    NodeRowsInline state.table.schema state.tree.root := by
  apply tableStateRowsInline_of_rows state
  intro row member
  rw [shape.1]
  exact (shape.2 row member).inline

theorem tableCellPlans_payload_le_of_rowsInline
    (schema : Core.Schema) : ∀ (rows : List Core.Row)
      (plans : List CoreOverflow.CellPlan),
      rows.mapM (CoreOverflow.tableCellPlan? schema) = some plans →
      (∀ row ∈ rows, CoreOverflow.RowInline schema row) →
      ∀ plan ∈ plans,
        plan.payload.length ≤ CoreOverflow.maxLocal plan.kind
  | [], plans, planned, _ => by
      change some [] = some plans at planned
      have empty : plans = [] := (Option.some.inj planned).symm
      subst plans
      simp
  | row :: rows, plans, planned, inline => by
      simp only [List.mapM_cons] at planned
      cases planResult : CoreOverflow.tableCellPlan? schema row with
      | none => simp [planResult] at planned
      | some plan =>
          simp only [planResult, Option.bind_eq_bind, Option.bind] at planned
          cases tailResult : rows.mapM (CoreOverflow.tableCellPlan? schema) with
          | none => simp [tailResult] at planned
          | some tail =>
              simp only [tailResult, Option.some.injEq] at planned
              have plansEqual : plans = plan :: tail :=
                (Option.some.inj planned).symm
              subst plans
              intro candidate member
              simp only [List.mem_cons] at member
              rcases member with rfl | tailMember
              · have rowInline := inline row (by simp)
                have payload := CoreOverflow.tableCellPlan_payload_le_of_inline
                  rowInline planResult
                rw [CoreOverflow.tableCellPlan_kind planResult]
                exact payload
              · apply tableCellPlans_payload_le_of_rowsInline schema rows tail
                  tailResult
                · intro tailRow tailRowMember
                  exact inline tailRow (by simp [tailRowMember])
                · exact tailMember

theorem tableCellPlan_cellBytes_none_encodeCell
    {schema : Core.Schema} {row : Core.Row}
    {plan : CoreOverflow.CellPlan} {cell : List UInt8}
    (planned : CoreOverflow.tableCellPlan? schema row = some plan)
    (built : plan.cellBytes? none = some cell) :
    CoreRecord.encodeCell? schema row = some cell := by
  unfold CoreOverflow.tableCellPlan? at planned
  unfold CoreRecord.encodeCell?
  cases recordResult : CoreRecord.rowRecord? schema row with
  | none => simp [recordResult] at planned
  | some record =>
    simp only [recordResult, Option.bind_eq_bind, Option.bind] at planned ⊢
    split at planned
    next bounded =>
      simp only [Option.some.injEq] at planned
      subst plan
      unfold CoreOverflow.CellPlan.cellBytes? at built
      split at built
      next =>
        simp only [Option.some.injEq] at built
        subst cell
        rw [dif_pos bounded]
      next => simp at built
    next => contradiction

theorem tableCellPlan_cellBytes_none_of_inline_encodeCell
    {schema : Core.Schema} {row : Core.Row} {cell : List UInt8}
    (inline : CoreOverflow.RowInline schema row)
    (encoded : CoreRecord.encodeCell? schema row = some cell) :
    ∃ plan : CoreOverflow.CellPlan,
      CoreOverflow.tableCellPlan? schema row = some plan ∧
      plan.cellBytes? none = some cell := by
  unfold CoreRecord.encodeCell? at encoded
  cases recordResult : CoreRecord.rowRecord? schema row with
  | none => simp [recordResult] at encoded
  | some record =>
      simp only [recordResult, Option.bind_eq_bind, Option.bind] at encoded
      split at encoded
      next bounded =>
        injection encoded with cellEqual
        subst cell
        let plan : CoreOverflow.CellPlan := {
          kind := .table
          cellPrefix := FileFormat.encodeVarint
              ⟨record.encode.length, by simpa using bounded⟩ ++
            FileFormat.encodeVarint (FileFormat.signedInteger64Bits row.rowid)
          payload := record.encode }
        refine ⟨plan, ?_, ?_⟩
        · simp [CoreOverflow.tableCellPlan?, recordResult, bounded, plan]
        · simp [CoreOverflow.CellPlan.cellBytes?,
            inline record recordResult, plan, List.append_assoc]
      next => contradiction

theorem tableCellPlans_of_inline_encodeCells
    (schema : Core.Schema) : ∀ (rows : List Core.Row)
      (cells : List (List UInt8)),
      rows.mapM (CoreRecord.encodeCell? schema) = some cells →
      (∀ row ∈ rows, CoreOverflow.RowInline schema row) →
      ∃ plans : List CoreOverflow.CellPlan,
        rows.mapM (CoreOverflow.tableCellPlan? schema) = some plans ∧
        plans.mapM (fun plan => plan.cellBytes? none) = some cells
  | [], cells, encoded, _ => by
      change some [] = some cells at encoded
      have empty : cells = [] := (Option.some.inj encoded).symm
      subst cells
      exact ⟨[], rfl, rfl⟩
  | row :: rows, cells, encoded, inline => by
      simp only [List.mapM_cons] at encoded
      cases cellResult : CoreRecord.encodeCell? schema row with
      | none => simp [cellResult] at encoded
      | some cell =>
          simp only [cellResult, Option.bind_eq_bind, Option.bind] at encoded
          cases tailResult : rows.mapM (CoreRecord.encodeCell? schema) with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              have cellsEqual : cells = cell :: tail :=
                (Option.some.inj encoded).symm
              subst cells
              rcases tableCellPlan_cellBytes_none_of_inline_encodeCell
                  (inline row (by simp)) cellResult with
                ⟨plan, planResult, planCell⟩
              rcases tableCellPlans_of_inline_encodeCells schema rows tail
                  tailResult (by
                    intro tailRow member
                    exact inline tailRow (by simp [member])) with
                ⟨plans, plansResult, planCells⟩
              refine ⟨plan :: plans, ?_, ?_⟩
              · simp [planResult, plansResult]
              · simp [planCell, planCells]

end CorePageCodec

end SQLeanite
