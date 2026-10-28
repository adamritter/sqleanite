import SQLeanite.CorePageCodec.LookupTableRowidFromEncodeChunkNodeWithOverflow
import SQLeanite.CoreWideIndex.PromoteChildrenToCells

namespace SQLeanite
namespace CoreWideIndex

def indexRowsInline (table : Core.Table) (index : Core.Index) : Bool :=
  (CoreFile.sortedIndexRows table index).all fun row =>
    match CoreFile.indexRecord? index row with
    | none => false
    | some record => decide
        (record.encode.length ≤ CoreOverflow.maxLocal .index)

theorem indexRowsInline_spec {table : Core.Table} {index : Core.Index}
    (success : indexRowsInline table index = true) :
    ∀ row ∈ CoreFile.sortedIndexRows table index, ∀ record,
      CoreFile.indexRecord? index row = some record →
        record.encode.length ≤ CoreOverflow.maxLocal .index := by
  intro row member record encoded
  have rowTrue := (List.all_eq_true.mp success) row member
  simp only [indexRowsInline] at success
  rw [encoded] at rowTrue
  exact of_decide_eq_true rowTrue

theorem decodeIndexCellWithSuffixFrom_inline
    {index : Core.Index} {row : Core.Row} {cell : Cell}
    (source : CoreDecode.PageSource) (fuel : Nat)
    (inline : ∀ record, CoreFile.indexRecord? index row = some record →
      record.encode.length ≤ CoreOverflow.maxLocal .index)
    (built : CoreFile.indexCell? index row = some cell) (suffix : List UInt8) :
    CoreDecode.decodeIndexCellWithSuffixFrom source fuel (cell ++ suffix) =
      some (⟨row.value index.column, row.rowid⟩, suffix) := by
  unfold CoreFile.indexCell? at built
  cases recordResult : CoreFile.indexRecord? index row with
  | none => simp [recordResult] at built
  | some record =>
      simp only [recordResult, Option.bind_eq_bind, Option.bind] at built
      split at built
      next payloadBound =>
        injection built with cellEqual
        subst cell
        let plan : CoreOverflow.CellPlan := {
          kind := .index
          cellPrefix := FileFormat.encodeVarint
            ⟨record.encode.length, by simpa using payloadBound⟩
          payload := record.encode }
        have planned : CoreOverflow.indexCellPlan? index row = some plan := by
          unfold CoreOverflow.indexCellPlan?
          rw [recordResult]
          simp only [Option.bind_eq_bind, Option.bind]
          rw [dif_pos payloadBound]
        have cellBuilt : plan.cellBytes? none = some
            (FileFormat.encodeVarint
                ⟨record.encode.length, by simpa using payloadBound⟩ ++
              record.encode) := by
          unfold CoreOverflow.CellPlan.cellBytes?
          rw [dif_pos (inline record recordResult)]
        exact CoreDecode.decodeIndexCellWithSuffixFrom_indexPlan_inline
          recordResult planned (inline record recordResult) source fuel none
          cellBuilt suffix
      next => contradiction

theorem indexCellsDecode_rows (source : CoreDecode.PageSource)
    (fuel : Nat) (index : Core.Index) : ∀ (rows : List Core.Row)
    {cells : List Cell},
    (∀ row ∈ rows, ∀ record,
      CoreFile.indexRecord? index row = some record →
        record.encode.length ≤ CoreOverflow.maxLocal .index) →
    rows.mapM (CoreFile.indexCell? index) = some cells →
    CoreDecode.IndexCellsDecode source fuel cells
      (rows.map fun row => ⟨row.value index.column, row.rowid⟩)
  | [], cells, _, encoded => by
      simp only [List.mapM_nil, pure, Pure.pure, Option.some.injEq] at encoded
      subst cells
      exact .nil
  | row :: rows, cells, inline, encoded => by
      simp only [List.mapM_cons] at encoded
      rcases Option.bind_eq_some_iff.mp encoded with
        ⟨cell, headResult, encoded⟩
      rcases Option.bind_eq_some_iff.mp encoded with
        ⟨tail, tailResult, equal⟩
      simp only [pure, Pure.pure, Option.some.injEq] at equal
      subst cells
      apply CoreDecode.IndexCellsDecode.cons
      · apply decodeIndexCellWithSuffixFrom_inline source fuel
          (inline := ?_) headResult
        intro record recordResult
        exact inline row (by simp) record recordResult
      · exact indexCellsDecode_rows source fuel index rows
          (fun candidate member => inline candidate (by simp [member])) tailResult

theorem indexCellsDecode_indexCells (source : CoreDecode.PageSource)
    (fuel : Nat) (table : Core.Table) (index : Core.Index)
    (inline : indexRowsInline table index = true) {cells : List Cell}
    (encoded : CoreFile.indexCells table index = some cells) :
    CoreDecode.IndexCellsDecode source fuel cells
      (CoreDecode.expectedIndexEntries table index) := by
  unfold CoreFile.indexCells at encoded
  unfold CoreDecode.expectedIndexEntries
  exact indexCellsDecode_rows source fuel index
    (CoreFile.sortedIndexRows table index)
    (fun row member record recordResult =>
      indexRowsInline_spec inline row member record recordResult) encoded

structure IndexEncoding where
  table : Core.Table
  index : Core.Index
  startPage : Nat
  rootPage : Nat
  nextPage : Nat
  store : Store
  numberedPages : List CorePageCodec.NumberedPage
  startExact : startPage = store.startPage
  nextExact : nextPage = store.nextPage
  rootExact : rootPage = store.root.rootId
  cellsEncoded : CoreFile.indexCells table index = some store.cells
  inline : indexRowsInline table index = true
  pagesEncoded : store.root.encodePages = some numberedPages
  numbers : (CorePageCodec.orderNumberedPages numberedPages).map
    CorePageCodec.NumberedPage.pageNumber =
      List.range' startPage (store.nextPage - startPage)

def IndexEncoding.pages (encoding : IndexEncoding) : List CoreFile.Page :=
  (CorePageCodec.orderNumberedPages encoding.numberedPages).map
    CorePageCodec.NumberedPage.page

def IndexEncoding.catalogEntry (encoding : IndexEncoding) :
    CoreFile.CatalogEntry := {
  kind := "index"
  name := encoding.index.name
  table := encoding.table.schema.name
  rootPage := encoding.rootPage
  sql := CoreFile.indexSQL encoding.table encoding.index
  sqlIsNull := encoding.index.isImplicitPrimary encoding.table.schema }

def encodeIndex (startPage : Nat) (table : Core.Table) (index : Core.Index) :
    Option IndexEncoding := do
  if inline : indexRowsInline table index then
    match cellsResult : CoreFile.indexCells table index with
    | none => none
    | some cells =>
      match storeResult : Store.build? startPage cells with
      | none => none
      | some store =>
        match pagesResult : store.root.encodePages with
        | none => none
        | some numberedPages =>
          if _numbers : (CorePageCodec.orderNumberedPages numberedPages).map
              CorePageCodec.NumberedPage.pageNumber =
                List.range' startPage (store.nextPage - startPage) then
            some {
              table
              index
              startPage
              rootPage := store.root.rootId
              nextPage := store.nextPage
              store
              numberedPages
              startExact := (Store.build?_startPage storeResult).symm
              nextExact := rfl
              rootExact := rfl
              cellsEncoded := by
                rw [Store.build?_cells storeResult]
                exact cellsResult
              inline
              pagesEncoded := pagesResult
              numbers := _numbers }
          else none
  else none

def encodeIndexes : Nat → List (Core.Table × Core.Index) →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, pair :: pairs => do
      let head ← encodeIndex nextPage pair.1 pair.2
      let tail ← encodeIndexes head.nextPage pairs
      some (head :: tail)

def indexPagesOf (encodings : List IndexEncoding) : List CoreFile.Page :=
  encodings.flatMap IndexEncoding.pages

def encodeIndexTableGroups : Nat → List Core.Table →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let current ← encodeIndexes nextPage
        (table.indexes.map fun index => (table, index))
      let after := nextPage + (indexPagesOf current).length
      let remaining ← encodeIndexTableGroups after tables
      some (current ++ remaining)

def indexEntriesOf (encodings : List IndexEncoding) :
    List CoreFile.CatalogEntry :=
  encodings.map IndexEncoding.catalogEntry

theorem IndexEncoding.numberedPages_length (encoding : IndexEncoding) :
    encoding.numberedPages.length =
      encoding.store.nextPage - encoding.startPage := by
  have lengths := congrArg List.length encoding.numbers
  simpa [CorePageCodec.orderNumberedPages] using lengths

theorem IndexEncoding.pages_length (encoding : IndexEncoding) :
    encoding.pages.length = encoding.numberedPages.length := by
  simp [IndexEncoding.pages, CorePageCodec.orderNumberedPages]

theorem IndexEncoding.next_eq (encoding : IndexEncoding) :
    encoding.nextPage = encoding.startPage + encoding.pages.length := by
  have startLe : encoding.startPage ≤ encoding.store.nextPage := by
    rw [encoding.startExact]
    exact encoding.store.startLeNext
  rw [encoding.nextExact, encoding.pages_length,
    encoding.numberedPages_length]
  omega

theorem encodeIndex_identity {startPage : Nat} {table : Core.Table}
    {index : Core.Index} {encoding : IndexEncoding}
    (success : encodeIndex startPage table index = some encoding) :
    encoding.startPage = startPage ∧
    encoding.table = table ∧ encoding.index = index := by
  simp only [encodeIndex] at success
  split at success <;> try contradiction
  all_goals split at success <;> try contradiction
  all_goals split at success <;> try contradiction
  all_goals split at success <;> try contradiction
  all_goals split at success <;> try contradiction
  all_goals
    injection success with equal
    subst encoding
    simp

theorem encodeIndexes_pairs : ∀ (nextPage : Nat)
    (pairs : List (Core.Table × Core.Index))
    (encodings : List IndexEncoding),
    encodeIndexes nextPage pairs = some encodings →
    encodings.map (fun encoding => (encoding.table, encoding.index)) = pairs
  | _, [], encodings, encoded => by
      simp only [encodeIndexes, Option.some.injEq] at encoded
      subst encodings
      rfl
  | nextPage, pair :: pairs, encodings, encoded => by
      simp only [encodeIndexes, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeIndex nextPage pair.1 pair.2 with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeIndexes head.nextPage pairs with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encodings
              have identity := encodeIndex_identity headResult
              simp only [List.map_cons]
              rw [identity.2.1, identity.2.2,
                encodeIndexes_pairs head.nextPage pairs tail tailResult]

theorem encodeIndexTableGroups_pairs : ∀ (nextPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups nextPage tables = some encodings →
    encodings.map (fun encoding => (encoding.table, encoding.index)) =
      tables.flatMap fun table =>
        table.indexes.map fun index => (table, index)
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

def numberedPagesOf (encodings : List IndexEncoding) :
    List CorePageCodec.NumberedPage :=
  encodings.flatMap fun encoding =>
    CorePageCodec.orderNumberedPages encoding.numberedPages

theorem numberedPages_length_le_of_mem {encoding : IndexEncoding} :
    ∀ {encodings : List IndexEncoding}, encoding ∈ encodings →
      encoding.numberedPages.length ≤ (numberedPagesOf encodings).length
  | [], member => by simp at member
  | head :: tail, member => by
      simp only [List.mem_cons] at member
      unfold numberedPagesOf
      simp only [List.flatMap_cons, List.length_append]
      rcases member with rfl | member
      · have orderedLength :
            (CorePageCodec.orderNumberedPages encoding.numberedPages).length =
              encoding.numberedPages.length := by
          simp [CorePageCodec.orderNumberedPages]
        omega
      · have tailBound := numberedPages_length_le_of_mem member
        unfold numberedPagesOf at tailBound
        omega

theorem indexPagesOf_eq_map (encodings : List IndexEncoding) :
    indexPagesOf encodings =
      (numberedPagesOf encodings).map CorePageCodec.NumberedPage.page := by
  unfold indexPagesOf numberedPagesOf IndexEncoding.pages
  rw [List.map_flatMap]

theorem encodeIndexes_numbers : ∀ (startPage : Nat)
    (pairs : List (Core.Table × Core.Index))
    (encodings : List IndexEncoding),
    encodeIndexes startPage pairs = some encodings →
    (numberedPagesOf encodings).map
        CorePageCodec.NumberedPage.pageNumber =
      List.range' startPage (indexPagesOf encodings).length
  | _, [], encodings, encoded => by
      simp only [encodeIndexes, Option.some.injEq] at encoded
      subst encodings
      rfl
  | startPage, pair :: pairs, encodings, encoded => by
      simp only [encodeIndexes, Option.bind_eq_bind, Option.bind] at encoded
      cases headResult : encodeIndex startPage pair.1 pair.2 with
      | none => simp [headResult] at encoded
      | some head =>
          simp only [headResult] at encoded
          cases tailResult : encodeIndexes head.nextPage pairs with
          | none => simp [tailResult] at encoded
          | some tail =>
              simp only [tailResult, Option.some.injEq] at encoded
              subst encodings
              have identity := encodeIndex_identity headResult
              have headNumbers :
                  (CorePageCodec.orderNumberedPages head.numberedPages).map
                      CorePageCodec.NumberedPage.pageNumber =
                    List.range' startPage head.pages.length := by
                rw [head.numbers]
                congr 2
                · exact identity.1
                · rw [head.pages_length, head.numberedPages_length]
              have tailNumbers := encodeIndexes_numbers head.nextPage pairs
                tail tailResult
              unfold numberedPagesOf indexPagesOf at tailNumbers ⊢
              simp only [List.flatMap_cons, List.map_append,
                List.length_append]
              rw [headNumbers, tailNumbers, head.next_eq, identity.1]
              exact List.range'_append_1

theorem encodeIndexTableGroups_numbers : ∀ (startPage : Nat)
    (tables : List Core.Table) (encodings : List IndexEncoding),
    encodeIndexTableGroups startPage tables = some encodings →
    (numberedPagesOf encodings).map
        CorePageCodec.NumberedPage.pageNumber =
      List.range' startPage (indexPagesOf encodings).length
  | _, [], encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.some.injEq] at encoded
      subst encodings
      rfl
  | startPage, table :: tables, encodings, encoded => by
      simp only [encodeIndexTableGroups, Option.bind_eq_bind, Option.bind]
        at encoded
      cases currentResult : encodeIndexes startPage
          (table.indexes.map fun index => (table, index)) with
      | none => simp [currentResult] at encoded
      | some current =>
          simp only [currentResult] at encoded
          cases remainingResult : encodeIndexTableGroups
              (startPage + (indexPagesOf current).length) tables with
          | none => simp [remainingResult] at encoded
          | some remaining =>
              simp only [remainingResult, Option.some.injEq] at encoded
              subst encodings
              have currentNumbers := encodeIndexes_numbers startPage _ current
                currentResult
              have remainingNumbers := encodeIndexTableGroups_numbers
                (startPage + (indexPagesOf current).length) tables remaining
                  remainingResult
              unfold numberedPagesOf indexPagesOf at currentNumbers remainingNumbers ⊢
              simp only [List.flatMap_append, List.map_append,
                List.length_append]
              rw [currentNumbers, remainingNumbers]
              exact List.range'_append_1

theorem IndexEncoding.decode_exact (source : CoreDecode.PageSource)
    (encoding : IndexEncoding)
    (contains : CorePageCodec.PageSourceContains source
      encoding.numberedPages)
    (pagesBound : encoding.numberedPages.length < source.pageCount + 1) :
    CoreDecode.decodeIndexSubtreeFrom source (source.pageCount + 1)
        encoding.rootPage =
      some (CoreDecode.expectedIndexEntries encoding.table encoding.index) := by
  have cellsDecoded := indexCellsDecode_indexCells source
    (source.pageCount + 1) encoding.table encoding.index encoding.inline
      encoding.cellsEncoded
  have rootCellsDecoded : CoreDecode.IndexCellsDecode source
      (source.pageCount + 1) encoding.store.root.toCells
      (CoreDecode.expectedIndexEntries encoding.table encoding.index) := by
    rw [encoding.store.represents]
    exact cellsDecoded
  have rootDecoded := NodeDecodes.ofCells rootCellsDecoded
  have encodedLength := Node.encodePages_length encoding.pagesEncoded
  have fuelBound : encoding.store.root.pageIds.length <
      source.pageCount + 1 := by omega
  have exact := decodeIndexSubtreeFrom_encodePages source
    encoding.pagesEncoded contains rootDecoded fuelBound
  rw [encoding.rootExact]
  exact exact

end CoreWideIndex

end SQLeanite
