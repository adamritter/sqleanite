import SQLeanite.CorePageCodec.EncodeChunkPathSubsetEncodeChunkNode

namespace SQLeanite
namespace CorePageCodec

private theorem tableCellPlans_noOverflow_encodeCells
    (schema : Core.Schema) : ∀ (rows : List Core.Row)
      (plans : List CoreOverflow.CellPlan) (cells : List (List UInt8)),
      rows.mapM (CoreOverflow.tableCellPlan? schema) = some plans →
      plans.mapM (fun plan => plan.cellBytes? none) = some cells →
      rows.mapM (CoreRecord.encodeCell? schema) = some cells
  | [], plans, cells, planned, built => by
      change some [] = some plans at planned
      have plansEmpty : plans = [] := (Option.some.inj planned).symm
      subst plans
      change some [] = some cells at built
      have cellsEmpty : cells = [] := (Option.some.inj built).symm
      subst cells
      rfl
  | row :: rows, plans, cells, planned, built => by
      simp only [List.mapM_cons] at planned built ⊢
      cases planResult : CoreOverflow.tableCellPlan? schema row with
      | none => simp [planResult] at planned
      | some plan =>
        simp only [planResult, Option.bind_eq_bind, Option.bind] at planned
        cases tailPlansResult :
            rows.mapM (CoreOverflow.tableCellPlan? schema) with
        | none => simp [tailPlansResult] at planned
        | some tailPlans =>
          simp only [tailPlansResult] at planned
          change some (plan :: tailPlans) = some plans at planned
          have plansEqual : plans = plan :: tailPlans :=
            (Option.some.inj planned).symm
          subst plans
          rw [List.mapM_cons] at built
          cases cellResult : plan.cellBytes? none with
          | none => simp [cellResult] at built
          | some cell =>
            rw [cellResult] at built
            cases tailCellsResult :
                tailPlans.mapM (fun candidate => candidate.cellBytes? none) with
            | none =>
              rw [tailCellsResult] at built
              change none = some cells at built
              contradiction
            | some tailCells =>
              rw [tailCellsResult] at built
              change some (cell :: tailCells) = some cells at built
              have cellsEqual : cells = cell :: tailCells :=
                (Option.some.inj built).symm
              subst cells
              have headEncoded := tableCellPlan_cellBytes_none_encodeCell
                planResult cellResult
              have tailEncoded := tableCellPlans_noOverflow_encodeCells schema
                rows tailPlans tailCells tailPlansResult tailCellsResult
              rw [headEncoded, tailEncoded]
              rfl

def encodeChunkNodeWithOverflow (schema : Core.Schema) :
    PersistentPageTree.Node CoreChunkPageState.Chunk → Nat →
      Option OverflowEncoding
  | .leaf pageId entries, nextOverflow => do
      let rows := entries.flatMap fun entry => entry.2
      let plans ← rows.mapM (CoreOverflow.tableCellPlan? schema)
      let resolved ← CoreOverflow.resolvePlans nextOverflow plans
      let page ← CoreFile.tableLeafPage? resolved.cells
      some ⟨[⟨pageId, page⟩], resolved.pages, resolved.nextPage⟩
  | node@(.branch2 _ left _ right), nextOverflow => do
      let root ← encodeChunkRoot schema node
      let leftEncoding ← encodeChunkNodeWithOverflow schema left nextOverflow
      let rightEncoding ← encodeChunkNodeWithOverflow schema right
        leftEncoding.nextPage
      some {
        treePages := root :: leftEncoding.treePages ++ rightEncoding.treePages
        overflowPages := leftEncoding.overflowPages ++
          rightEncoding.overflowPages
        nextPage := rightEncoding.nextPage }
  | node@(.branch3 _ left _ middle _ right), nextOverflow => do
      let root ← encodeChunkRoot schema node
      let leftEncoding ← encodeChunkNodeWithOverflow schema left nextOverflow
      let middleEncoding ← encodeChunkNodeWithOverflow schema middle
        leftEncoding.nextPage
      let rightEncoding ← encodeChunkNodeWithOverflow schema right
        middleEncoding.nextPage
      some {
        treePages := root :: leftEncoding.treePages ++
          middleEncoding.treePages ++ rightEncoding.treePages
        overflowPages := leftEncoding.overflowPages ++
          middleEncoding.overflowPages ++ rightEncoding.overflowPages
        nextPage := rightEncoding.nextPage }

/-- For inline rows, the general overflow-aware encoder is exactly the live
localized tree encoder plus an empty overflow run.  This is the constructive
direction of the representation bridge: a successful live encoding determines
the complete general encoding without a second executable pass. -/
theorem encodeChunkNodeWithOverflow_of_inline
    (schema : Core.Schema) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (nextOverflow : Nat) (pages : List NumberedPage),
      NodeRowsInline schema node →
      encodeChunkNode schema node = some pages →
      encodeChunkNodeWithOverflow schema node nextOverflow = some {
        treePages := pages
        overflowPages := []
        nextPage := nextOverflow }
  | .leaf pageId entries, nextOverflow, pages, inline, encoded => by
      simp only [encodeChunkNode] at encoded
      cases leafResult : encodeChunkLeaf schema entries with
      | none => simp [leafResult] at encoded
      | some page =>
          simp only [leafResult, Option.bind_eq_bind, Option.bind,
            Option.some.injEq] at encoded
          subst pages
          unfold encodeChunkLeaf encodeLeaf at leafResult
          cases cellsResult :
              (entries.flatMap fun entry =>
                entry.2.map fun row => (row.treeKey, row)).mapM
                  (fun entry => CoreRecord.encodeCell? schema entry.2) with
          | none => simp [cellsResult] at leafResult
          | some cells =>
              simp only [cellsResult, Option.bind_eq_bind, Option.bind]
                at leafResult
              let rows := entries.flatMap fun entry => entry.2
              have rowCells : rows.mapM (CoreRecord.encodeCell? schema) =
                  some cells := by
                rw [← mapM_map_entry_values] at cellsResult
                simpa [rows, List.map_flatMap, List.map_map,
                  Function.comp_def] using cellsResult
              have rowsInline : ∀ row ∈ rows,
                  CoreOverflow.RowInline schema row := by
                intro row member
                rcases List.mem_flatMap.mp member with
                  ⟨chunk, chunkMember, rowMember⟩
                exact inline chunk chunkMember row rowMember
              rcases tableCellPlans_of_inline_encodeCells schema rows cells
                  rowCells rowsInline with ⟨plans, plansResult, planCells⟩
              have resolved := CoreOverflow.resolvePlans_of_cellBytes_none
                nextOverflow plans cells planCells
              have plansResult' :
                  (entries.flatMap fun entry => entry.2).mapM
                      (CoreOverflow.tableCellPlan? schema) = some plans := by
                simpa [rows] using plansResult
              simp only [encodeChunkNodeWithOverflow, plansResult',
                Option.bind_eq_bind, Option.bind]
              simp [resolved, leafResult]
  | .branch2 pageId left separator right, nextOverflow, pages,
      inline, encoded => by
      simp only [NodeRowsInline] at inline
      simp only [encodeChunkNode] at encoded
      cases leftKeyResult : maximumChunkRowid? left with
      | none => simp [leftKeyResult] at encoded
      | some leftKey =>
          simp only [leftKeyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases pageResult : RecursivePageBTree.interiorPage?
              [(left.rootId, leftKey)] right.rootId with
          | none => simp [pageResult] at encoded
          | some page =>
              simp only [pageResult] at encoded
              cases leftResult : encodeChunkNode schema left with
              | none => simp [leftResult] at encoded
              | some leftPages =>
                  simp only [leftResult] at encoded
                  cases rightResult : encodeChunkNode schema right with
                  | none => simp [rightResult] at encoded
                  | some rightPages =>
                      simp only [rightResult, Option.some.injEq] at encoded
                      subst pages
                      have rootResult : encodeChunkRoot schema
                          (.branch2 pageId left separator right) =
                          some ⟨pageId, page⟩ := by
                        simp [encodeChunkRoot, leftKeyResult, pageResult]
                      have leftEncoded := encodeChunkNodeWithOverflow_of_inline
                        schema left nextOverflow leftPages inline.1 leftResult
                      have rightEncoded := encodeChunkNodeWithOverflow_of_inline
                        schema right nextOverflow rightPages inline.2 rightResult
                      simp [encodeChunkNodeWithOverflow, rootResult, leftEncoded,
                        rightEncoded]
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      nextOverflow, pages, inline, encoded => by
      simp only [NodeRowsInline] at inline
      simp only [encodeChunkNode] at encoded
      cases leftKeyResult : maximumChunkRowid? left with
      | none => simp [leftKeyResult] at encoded
      | some leftKey =>
          simp only [leftKeyResult, Option.bind_eq_bind, Option.bind] at encoded
          cases middleKeyResult : maximumChunkRowid? middle with
          | none => simp [middleKeyResult] at encoded
          | some middleKey =>
              simp only [middleKeyResult] at encoded
              cases pageResult : RecursivePageBTree.interiorPage?
                  [(left.rootId, leftKey), (middle.rootId, middleKey)]
                  right.rootId with
              | none => simp [pageResult] at encoded
              | some page =>
                  simp only [pageResult] at encoded
                  cases leftResult : encodeChunkNode schema left with
                  | none => simp [leftResult] at encoded
                  | some leftPages =>
                      simp only [leftResult] at encoded
                      cases middleResult : encodeChunkNode schema middle with
                      | none => simp [middleResult] at encoded
                      | some middlePages =>
                          simp only [middleResult] at encoded
                          cases rightResult : encodeChunkNode schema right with
                          | none => simp [rightResult] at encoded
                          | some rightPages =>
                              simp only [rightResult, Option.some.injEq] at encoded
                              subst pages
                              have rootResult : encodeChunkRoot schema
                                  (.branch3 pageId left firstSeparator middle
                                    secondSeparator right) =
                                  some ⟨pageId, page⟩ := by
                                simp [encodeChunkRoot, leftKeyResult,
                                  middleKeyResult, pageResult]
                              have leftEncoded :=
                                encodeChunkNodeWithOverflow_of_inline schema left
                                  nextOverflow leftPages inline.1 leftResult
                              have middleEncoded :=
                                encodeChunkNodeWithOverflow_of_inline schema middle
                                  nextOverflow middlePages inline.2.1 middleResult
                              have rightEncoded :=
                                encodeChunkNodeWithOverflow_of_inline schema right
                                  nextOverflow rightPages inline.2.2 rightResult
                              simp [encodeChunkNodeWithOverflow, rootResult,
                                leftEncoded, middleEncoded, rightEncoded]

/-- The overflow-aware encoder emits no overflow run when the logical rows
meet `NodeRowsInline`.  This turns inline storage from a caller-supplied fact
about an opaque encoder result into a semantic invariant of the table rows. -/
theorem encodeChunkNodeWithOverflow_inline
    (schema : Core.Schema) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (nextOverflow : Nat) (encoding : OverflowEncoding),
      NodeRowsInline schema node →
      encodeChunkNodeWithOverflow schema node nextOverflow = some encoding →
      encoding.overflowPages = []
  | .leaf pageId entries, nextOverflow, encoding, inline, encoded => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      let rows := entries.flatMap fun entry => entry.2
      cases plansResult : rows.mapM (CoreOverflow.tableCellPlan? schema) with
      | none => simp [rows, plansResult] at encoded
      | some plans =>
          simp only [rows, plansResult, Option.bind_eq_bind, Option.bind] at encoded
          cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
          | none => simp [resolvedResult] at encoded
          | some resolved =>
              simp only [resolvedResult] at encoded
              cases pageResult : CoreFile.tableLeafPage? resolved.cells with
              | none => simp [pageResult] at encoded
              | some page =>
                  simp only [pageResult, Option.some.injEq] at encoded
                  subst encoding
                  have rowsInline : ∀ row ∈ rows,
                      CoreOverflow.RowInline schema row := by
                    intro row member
                    rcases List.mem_flatMap.mp member with
                      ⟨chunk, chunkMember, rowMember⟩
                    exact inline chunk chunkMember row rowMember
                  have payloads := tableCellPlans_payload_le_of_rowsInline
                    schema rows plans plansResult rowsInline
                  exact CoreOverflow.resolvePlans_pages_eq_nil_of_payload_le
                    resolvedResult payloads
  | .branch2 pageId left separator right, nextOverflow, encoding, inline,
      encoded => by
      simp only [NodeRowsInline] at inline
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left nextOverflow with
          | none => simp [leftResult] at encoded
          | some leftEncoding =>
              simp only [leftResult] at encoded
              cases rightResult : encodeChunkNodeWithOverflow schema right
                  leftEncoding.nextPage with
              | none => simp [rightResult] at encoded
              | some rightEncoding =>
                  simp only [rightResult, Option.some.injEq] at encoded
                  subst encoding
                  have leftEmpty := encodeChunkNodeWithOverflow_inline schema left
                    nextOverflow leftEncoding inline.1 leftResult
                  have rightEmpty := encodeChunkNodeWithOverflow_inline schema right
                    leftEncoding.nextPage rightEncoding inline.2 rightResult
                  simp [leftEmpty, rightEmpty]
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      nextOverflow, encoding, inline, encoded => by
      simp only [NodeRowsInline] at inline
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
          simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
          cases leftResult : encodeChunkNodeWithOverflow schema left nextOverflow with
          | none => simp [leftResult] at encoded
          | some leftEncoding =>
              simp only [leftResult] at encoded
              cases middleResult : encodeChunkNodeWithOverflow schema middle
                  leftEncoding.nextPage with
              | none => simp [middleResult] at encoded
              | some middleEncoding =>
                  simp only [middleResult] at encoded
                  cases rightResult : encodeChunkNodeWithOverflow schema right
                      middleEncoding.nextPage with
                  | none => simp [rightResult] at encoded
                  | some rightEncoding =>
                      simp only [rightResult, Option.some.injEq] at encoded
                      subst encoding
                      have leftEmpty := encodeChunkNodeWithOverflow_inline schema left
                        nextOverflow leftEncoding inline.1 leftResult
                      have middleEmpty := encodeChunkNodeWithOverflow_inline schema
                        middle leftEncoding.nextPage middleEncoding inline.2.1
                          middleResult
                      have rightEmpty := encodeChunkNodeWithOverflow_inline schema
                        right middleEncoding.nextPage rightEncoding inline.2.2
                          rightResult
                      simp [leftEmpty, middleEmpty, rightEmpty]

/-- The general encoder and the localized tree encoder produce identical tree
pages whenever the general encoding emits no overflow run.  This is the
representation bridge for page-local mutations of inline SQLite records. -/
theorem encodeChunkNodeWithOverflow_noOverflow
    (schema : Core.Schema) :
    ∀ (node : PersistentPageTree.Node CoreChunkPageState.Chunk)
      (nextOverflow : Nat) (encoding : OverflowEncoding),
      encodeChunkNodeWithOverflow schema node nextOverflow = some encoding →
      encoding.overflowPages = [] →
      encodeChunkNode schema node = some encoding.treePages
  | .leaf pageId entries, nextOverflow, encoding, encoded, empty => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      let rows := entries.flatMap fun entry => entry.2
      cases plansResult : rows.mapM (CoreOverflow.tableCellPlan? schema) with
      | none => simp [rows, plansResult] at encoded
      | some plans =>
        simp only [rows, plansResult, Option.bind_eq_bind, Option.bind] at encoded
        cases resolvedResult : CoreOverflow.resolvePlans nextOverflow plans with
        | none => simp [resolvedResult] at encoded
        | some resolved =>
          simp only [resolvedResult] at encoded
          cases pageResult : CoreFile.tableLeafPage? resolved.cells with
          | none => simp [pageResult] at encoded
          | some page =>
            simp only [pageResult, Option.some.injEq] at encoded
            subst encoding
            have noOverflow :=
              CoreOverflow.resolvePlans_noOverflow resolvedResult empty
            have rowCells := tableCellPlans_noOverflow_encodeCells schema
              rows plans resolved.cells plansResult noOverflow.1
            have leafEncoded : encodeChunkLeaf schema entries = some page := by
              unfold encodeChunkLeaf encodeLeaf
              have cellsResult :
                  (entries.flatMap fun entry =>
                    entry.2.map fun row => (row.treeKey, row)).mapM
                      (fun entry => CoreRecord.encodeCell? schema entry.2) =
                    some resolved.cells := by
                rw [← mapM_map_entry_values]
                simpa [rows, List.map_flatMap, List.map_map,
                  Function.comp_def] using rowCells
              rw [cellsResult]
              simpa only [bind, Option.bind] using pageResult
            simp [encodeChunkNode, leafEncoded]
  | .branch2 pageId left separator right, nextOverflow, encoding,
      encoded, empty => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch2 pageId left separator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left nextOverflow with
        | none => simp [leftResult] at encoded
        | some leftEncoding =>
          simp only [leftResult] at encoded
          cases rightResult : encodeChunkNodeWithOverflow schema right
              leftEncoding.nextPage with
          | none => simp [rightResult] at encoded
          | some rightEncoding =>
            simp only [rightResult, Option.some.injEq] at encoded
            subst encoding
            have emptyParts : leftEncoding.overflowPages = [] ∧
                rightEncoding.overflowPages = [] :=
              List.append_eq_nil_iff.mp empty
            have leftEncoded := encodeChunkNodeWithOverflow_noOverflow schema
              left nextOverflow leftEncoding leftResult emptyParts.1
            have rightEncoded := encodeChunkNodeWithOverflow_noOverflow schema
              right leftEncoding.nextPage rightEncoding rightResult emptyParts.2
            simp only [encodeChunkRoot] at rootResult
            cases keyResult : maximumChunkRowid? left with
            | none => simp [keyResult] at rootResult
            | some key =>
              simp only [keyResult, Option.bind_eq_bind, Option.bind]
                at rootResult
              cases pageResult : RecursivePageBTree.interiorPage?
                  [(left.rootId, key)] right.rootId with
              | none => simp [pageResult] at rootResult
              | some page =>
                simp only [pageResult, Option.some.injEq] at rootResult
                subst root
                simp [encodeChunkNode, keyResult, pageResult, leftEncoded,
                  rightEncoded]
  | .branch3 pageId left firstSeparator middle secondSeparator right,
      nextOverflow, encoding, encoded, empty => by
      simp only [encodeChunkNodeWithOverflow] at encoded
      cases rootResult : encodeChunkRoot schema
          (.branch3 pageId left firstSeparator middle secondSeparator right) with
      | none => simp [rootResult] at encoded
      | some root =>
        simp only [rootResult, Option.bind_eq_bind, Option.bind] at encoded
        cases leftResult : encodeChunkNodeWithOverflow schema left nextOverflow with
        | none => simp [leftResult] at encoded
        | some leftEncoding =>
          simp only [leftResult] at encoded
          cases middleResult : encodeChunkNodeWithOverflow schema middle
              leftEncoding.nextPage with
          | none => simp [middleResult] at encoded
          | some middleEncoding =>
            simp only [middleResult] at encoded
            cases rightResult : encodeChunkNodeWithOverflow schema right
                middleEncoding.nextPage with
            | none => simp [rightResult] at encoded
            | some rightEncoding =>
              simp only [rightResult, Option.some.injEq] at encoded
              subst encoding
              have emptyParts : leftEncoding.overflowPages = [] ∧
                  middleEncoding.overflowPages = [] ∧
                  rightEncoding.overflowPages = [] := by
                have parts := List.append_eq_nil_iff.mp empty
                have firstParts := List.append_eq_nil_iff.mp parts.1
                exact ⟨firstParts.1, firstParts.2, parts.2⟩
              have leftEncoded := encodeChunkNodeWithOverflow_noOverflow schema
                left nextOverflow leftEncoding leftResult emptyParts.1
              have middleEncoded := encodeChunkNodeWithOverflow_noOverflow schema
                middle leftEncoding.nextPage middleEncoding middleResult
                  emptyParts.2.1
              have rightEncoded := encodeChunkNodeWithOverflow_noOverflow schema
                right middleEncoding.nextPage rightEncoding rightResult
                  emptyParts.2.2
              simp only [encodeChunkRoot] at rootResult
              cases leftKeyResult : maximumChunkRowid? left with
              | none => simp [leftKeyResult] at rootResult
              | some leftKey =>
                simp only [leftKeyResult, Option.bind_eq_bind, Option.bind]
                  at rootResult
                cases middleKeyResult : maximumChunkRowid? middle with
                | none => simp [middleKeyResult] at rootResult
                | some middleKey =>
                  simp only [middleKeyResult] at rootResult
                  cases pageResult : RecursivePageBTree.interiorPage?
                      [(left.rootId, leftKey), (middle.rootId, middleKey)]
                      right.rootId with
                  | none => simp [pageResult] at rootResult
                  | some page =>
                    simp only [pageResult, Option.some.injEq] at rootResult
                    subst root
                    simp [encodeChunkNode, leftKeyResult, middleKeyResult,
                      pageResult, leftEncoded, middleEncoded, rightEncoded]

end CorePageCodec

end SQLeanite
