import SQLeanite.CoreFile.TableInteriorPage

namespace SQLeanite
namespace CoreFile
attribute [local instance] lexOrd
open FileFormat

theorem integerIndexRowLe_trans (index : Core.Index)
    (left middle right : Core.Row)
    (leftMiddle : integerIndexRowLe index left middle = true)
    (middleRight : integerIndexRowLe index middle right = true) :
    integerIndexRowLe index left right = true := by
  simp only [integerIndexRowLe, decide_eq_true_eq] at leftMiddle middleRight ⊢
  omega

theorem integerIndexRowLe_total (index : Core.Index)
    (left right : Core.Row) :
    (integerIndexRowLe index left right ||
      integerIndexRowLe index right left) = true := by
  simp only [integerIndexRowLe, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem integerIndexRowLe_valueLe (index : Core.Index)
    (left right : Core.Row)
    (leftInteger : ∃ value : Core.Integer,
      left.value index.column = .integer value)
    (rightInteger : ∃ value : Core.Integer,
      right.value index.column = .integer value)
    (ordered : integerIndexRowLe index left right = true) :
    indexRowValueLe index left right := by
  rcases leftInteger with ⟨leftValue, leftEqual⟩
  rcases rightInteger with ⟨rightValue, rightEqual⟩
  simp only [integerIndexRowLe, integerIndexKey, leftEqual, rightEqual,
    decide_eq_true_eq] at ordered
  unfold indexRowValueLe
  simp only [leftEqual, rightEqual, PhysicalQuery.compareValue]
  have gtIff : compare leftValue.value rightValue.value = .gt ↔
      rightValue.value < leftValue.value := by
    change compareOfLessAndEq leftValue.value rightValue.value = .gt ↔ _
    exact compareOfLessAndEq_eq_gt Int.le_antisymm Int.le_total Int.not_le _ _
  intro greater
  have := gtIff.mp greater
  omega

theorem pairwise_integerIndexRowLe_valueLe (index : Core.Index) :
    ∀ (rows : List Core.Row),
      (∀ row ∈ rows, ∃ value : Core.Integer,
        row.value index.column = .integer value) →
      rows.Pairwise (fun left right =>
        integerIndexRowLe index left right = true) →
      rows.Pairwise (indexRowValueLe index)
  | [], _, _ => by simp
  | row :: rows, allInteger, sorted => by
      apply List.pairwise_cons.mpr
      constructor
      · intro candidate member
        exact integerIndexRowLe_valueLe index row candidate
          (allInteger row (by simp))
          (allInteger candidate (by simp [member]))
          ((List.pairwise_cons.mp sorted).1 candidate member)
      · exact pairwise_integerIndexRowLe_valueLe index rows
          (fun candidate member => allInteger candidate (by simp [member]))
          (List.pairwise_cons.mp sorted).2

/-- Total executable TEXT sort key.  The fallback key is unreachable on the
certified fast path but keeps the comparator lawful over all `Core.Row`s. -/
def textIndexSortKey (index : Core.Index) (row : Core.Row) :
    List UInt8 × Int :=
  let bytes := match row.value index.column with
    | .text value => value.bytes
    | _ => []
  (bytes, row.rowid.value)

def textIndexRowLe (index : Core.Index) (left right : Core.Row) : Bool :=
  (compare (textIndexSortKey index left) (textIndexSortKey index right)).isLE

theorem textIndexRowLe_trans (index : Core.Index)
    (left middle right : Core.Row)
    (leftMiddle : textIndexRowLe index left middle = true)
    (middleRight : textIndexRowLe index middle right = true) :
    textIndexRowLe index left right = true := by
  unfold textIndexRowLe at leftMiddle middleRight ⊢
  exact Std.TransOrd.isLE_trans leftMiddle middleRight

theorem textIndexRowLe_total (index : Core.Index)
    (left right : Core.Row) :
    (textIndexRowLe index left right || textIndexRowLe index right left) =
      true := by
  unfold textIndexRowLe
  cases comparison : compare (textIndexSortKey index left)
      (textIndexSortKey index right) with
  | lt => simp [comparison]
  | eq => simp [comparison]
  | gt =>
      have reverse : compare (textIndexSortKey index right)
          (textIndexSortKey index left) = .lt :=
        Std.OrientedCmp.lt_of_gt comparison
      simp [comparison, reverse]

theorem textIndexRowLe_valueLe (index : Core.Index)
    (left right : Core.Row)
    (leftText : ∃ value : PhysicalCodec.Text,
      left.value index.column = .text value)
    (rightText : ∃ value : PhysicalCodec.Text,
      right.value index.column = .text value)
    (ordered : textIndexRowLe index left right = true) :
    indexRowValueLe index left right := by
  rcases leftText with ⟨leftValue, leftEqual⟩
  rcases rightText with ⟨rightValue, rightEqual⟩
  unfold textIndexRowLe textIndexSortKey at ordered
  simp only [leftEqual, rightEqual] at ordered
  unfold indexRowValueLe
  simp only [leftEqual, rightEqual, PhysicalQuery.compareValue]
  intro greater
  have keyGreater : compare (leftValue.bytes, left.rowid.value)
      (rightValue.bytes, right.rowid.value) = .gt := by
    change (compare leftValue.bytes rightValue.bytes).then
      (compare left.rowid.value right.rowid.value) = .gt
    rw [greater]
    rfl
  rw [keyGreater] at ordered
  contradiction

theorem pairwise_textIndexRowLe_valueLe (index : Core.Index) :
    ∀ (rows : List Core.Row),
      (∀ row ∈ rows, ∃ value : PhysicalCodec.Text,
        row.value index.column = .text value) →
      rows.Pairwise (fun left right => textIndexRowLe index left right = true) →
      rows.Pairwise (indexRowValueLe index)
  | [], _, _ => by simp
  | row :: rows, allText, sorted => by
      apply List.pairwise_cons.mpr
      constructor
      · intro candidate member
        exact textIndexRowLe_valueLe index row candidate
          (allText row (by simp))
          (allText candidate (by simp [member]))
          ((List.pairwise_cons.mp sorted).1 candidate member)
      · exact pairwise_textIndexRowLe_valueLe index rows
          (fun candidate member => allText candidate (by simp [member]))
          (List.pairwise_cons.mp sorted).2

def sortedIndexRows (table : Core.Table) (index : Core.Index) :
    List Core.Row :=
  if indexValuesInteger table index then
    table.rows.mergeSort (integerIndexRowLe index)
  else if indexValuesText table index then
    table.rows.mergeSort (textIndexRowLe index)
  else table.rows.foldl (fun rows row => insertIndexRow index row rows) []

/-- An INTEGER-certified generated index is ordered by its SQL comparison
value. Rowid tie-breaking may refine equal values, but never reverses their
value order. -/
theorem sortedIndexRows_pairwise_valueLe (table : Core.Table)
    (index : Core.Index)
    (integers : indexValuesInteger table index = true) :
    (sortedIndexRows table index).Pairwise (indexRowValueLe index) := by
  rw [sortedIndexRows, if_pos integers]
  apply pairwise_integerIndexRowLe_valueLe index
  · intro row member
    exact (indexValuesInteger_iff table index).mp integers row
      (List.mem_mergeSort.mp member)
  · exact List.pairwise_mergeSort (integerIndexRowLe_trans index)
      (integerIndexRowLe_total index) table.rows

theorem sortedIndexRows_pairwise_valueLe_text (table : Core.Table)
    (index : Core.Index)
    (texts : indexValuesText table index = true) :
    (sortedIndexRows table index).Pairwise (indexRowValueLe index) := by
  unfold sortedIndexRows
  by_cases integers : indexValuesInteger table index = true
  · rw [if_pos integers]
    have empty : table.rows = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro row member
      rcases (indexValuesInteger_iff table index).mp integers row member with
        ⟨integer, integerEqual⟩
      rcases (indexValuesText_iff table index).mp texts row member with
        ⟨text, textEqual⟩
      rw [integerEqual] at textEqual
      contradiction
    simp [empty]
  · rw [if_neg integers]
    rw [if_pos texts]
    apply pairwise_textIndexRowLe_valueLe index
    · intro row member
      exact (indexValuesText_iff table index).mp texts row
        (List.mem_mergeSort.mp member)
    · exact List.pairwise_mergeSort (textIndexRowLe_trans index)
        (textIndexRowLe_total index) table.rows

theorem foldInsertIndexRow_perm (index : Core.Index)
    (rows accumulator : List Core.Row) :
    (rows.foldl (fun sorted row => insertIndexRow index row sorted)
      accumulator).Perm (rows ++ accumulator) := by
  induction rows generalizing accumulator with
  | nil => exact List.Perm.refl _
  | cons row rows induction =>
      have tail := induction (insertIndexRow index row accumulator)
      have inserted :=
        (insertIndexRow_perm index row accumulator).append_left rows
      exact tail.trans (inserted.trans List.perm_middle)

theorem sortedIndexRows_perm (table : Core.Table) (index : Core.Index) :
    (sortedIndexRows table index).Perm table.rows := by
  unfold sortedIndexRows
  split
  · exact List.mergeSort_perm table.rows (integerIndexRowLe index)
  · split
    · exact List.mergeSort_perm table.rows (textIndexRowLe index)
    · simpa using foldInsertIndexRow_perm index table.rows []

def indexCells (table : Core.Table) (index : Core.Index) :
    Option (List (List UInt8)) :=
  (sortedIndexRows table index).mapM (indexCell? index)

/-- Index cells split into leaf-sized runs, same byte-driven policy as tables. -/
def indexLeaves (table : Core.Table) (index : Core.Index) :
    Option (List (List (List UInt8))) := do
  let cells ← indexCells table index
  some (CellPagination.paginateCells cells)

theorem sortedIndexRows_canonicalize (table : Core.Table) (index : Core.Index) :
    sortedIndexRows table.canonicalize index = sortedIndexRows table index := by
  simp [sortedIndexRows, Core.Table.canonicalize_rows]

theorem indexCells_canonicalize (table : Core.Table) (index : Core.Index) :
    indexCells table.canonicalize index = indexCells table index := by
  unfold indexCells
  rw [sortedIndexRows_canonicalize]

theorem indexLeaves_canonicalize (table : Core.Table) (index : Core.Index) :
    indexLeaves table.canonicalize index = indexLeaves table index := by
  unfold indexLeaves
  rw [indexCells_canonicalize]

def indexLeafPage? (cells : List (List UInt8)) : Option Page := do
  let body ← leafBody? 10 0 cells
  some { bytes := body.bytes, length_eq := by simpa using body.length_eq }

/-- In an index B-tree the interior cells are *themselves* index entries, not
mere separators as in a table B-tree. So the promoted key must be removed from
its leaf, or the index would hold it twice and C SQLite reports
"wrong # of entries in index".

Splits leaves into (leaves with promoted keys removed, promoted keys). -/
def promoteSeparators :
    List (List (List UInt8)) → List (List (List UInt8)) × List (List UInt8)
  | [] => ([], [])
  | [last] => ([last], [])
  | leaf :: rest =>
      let (trimmed, separators) := promoteSeparators rest
      match leaf.getLast? with
      | some key => (leaf.dropLast :: trimmed, key :: separators)
      | none => (leaf :: trimmed, separators)

/-- Interior index page (type 2). An interior index cell is a 4-byte left-child
page number followed by the same payload an index leaf cell carries. -/
def indexInteriorPage? (firstLeaf : Nat) (separators : List (List UInt8))
    (leafCount : Nat) : Option Page := do
  let rightmostNumber := firstLeaf + leafCount - 1
  if rightmostBound : rightmostNumber < 2 ^ 32 then
    let rightmost : U32Value := ⟨rightmostNumber, by simpa using rightmostBound⟩
    let cells ← (separators.zipIdx).mapM fun pair => do
      let childNumber := firstLeaf + pair.2
      if childBound : childNumber < 2 ^ 32 then
        let child : U32Value := ⟨childNumber, by simpa using childBound⟩
        some (PhysicalTableBTree.encodeU32Nat child.val ++ pair.1)
      else none
    if fits : PhysicalTableBTree.InteriorPageFit cells then
      -- interiorPageBody emits an interior TABLE header (type 5); an interior
      -- index page is type 2. Patch the tag, as leafBody? does for leaves.
      some {
        bytes := replaceFirst 2 (PhysicalTableBTree.interiorPageBody rightmost cells)
        length_eq := by
          rw [replaceFirst_length]
          exact PhysicalTableBTree.interiorPageBody_length rightmost cells fits }
    else none
  else none

/-- Pages for one index, in page-number order: root first, then leaves. -/
def indexPages? (rootPage : Nat) (leaves : List (List (List UInt8))) :
    Option (List Page) :=
  match leaves with
  | [] => do let page ← indexLeafPage? []; some [page]
  | [only] => do let page ← indexLeafPage? only; some [page]
  | _ => do
      let (trimmed, separators) := promoteSeparators leaves
      let root ← indexInteriorPage? (rootPage + 1) separators trimmed.length
      let leafPages ← trimmed.mapM indexLeafPage?
      some (root :: leafPages)

structure PageList (length : Nat) where
  pages : List Page
  pages_length : pages.length = length

def mapPages? {A : Type} (makePage : A → Option Page) :
    (values : List A) → Option (PageList values.length)
  | [] => some ⟨[], rfl⟩
  | value :: values => do
      let page ← makePage value
      let remaining ← mapPages? makePage values
      some ⟨page :: remaining.pages, by simp [remaining.pages_length]⟩

/-- Every table's pages, concatenated in page-number order. -/
def allTablePages (layouts : List TableLayout) : Option (List Page) := do
  let grouped ← layouts.mapM tablePages?
  some grouped.flatten

def allIndexPages (layouts : List IndexLayout) : Option (List Page) := do
  let grouped ← layouts.mapM fun layout => indexPages? layout.rootPage layout.leaves
  some grouped.flatten

/-- One table's layout and already-built pages. Keeping these together avoids
recomputing the page grouping and gives the codec proof an aligned witness. -/
structure TableEncoding where
  layout : TableLayout
  pages : List Page

def encodeTables : Nat → List Core.Table → Option (List TableEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let leaves ← tableLeaves table
      let layout : TableLayout := ⟨nextPage, leaves⟩
      let physicalPages ← tablePages? layout
      let remaining ← encodeTables (nextPage + tableFootprint leaves) tables
      some (⟨layout, physicalPages⟩ :: remaining)

theorem encodeTables_canonicalize : ∀ (nextPage : Nat)
    (tables : List Core.Table),
    encodeTables nextPage (tables.map Core.Table.canonicalize) =
      encodeTables nextPage tables
  | _, [] => rfl
  | nextPage, table :: tables => by
      simp only [List.map_cons, encodeTables]
      rw [tableLeaves_canonicalize]
      cases leavesResult : tableLeaves table with
      | none => rfl
      | some leaves =>
          simp only [Option.bind_eq_bind, Option.bind]
          cases pagesResult : tablePages? ⟨nextPage, leaves⟩ with
          | none => rfl
          | some pages =>
              simp only
              rw [encodeTables_canonicalize]

def tableLayoutsOf (encodings : List TableEncoding) : List TableLayout :=
  encodings.map (·.layout)

def tablePagesOf (encodings : List TableEncoding) : List Page :=
  encodings.flatMap (·.pages)

structure IndexEncoding where
  table : Core.Table
  index : Core.Index
  layout : IndexLayout
  pages : List Page

def IndexEncoding.canonicalize (encoding : IndexEncoding) : IndexEncoding := {
  encoding with table := encoding.table.canonicalize }

@[simp] theorem IndexEncoding.canonicalize_pages (encoding : IndexEncoding) :
    encoding.canonicalize.pages = encoding.pages := rfl

def encodeIndexes : Nat → List (Core.Table × Core.Index) →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, indexed :: indexes => do
      let leaves ← indexLeaves indexed.1 indexed.2
      let layout : IndexLayout := ⟨nextPage, leaves⟩
      let physicalPages ← indexPages? layout.rootPage layout.leaves
      let remaining ← encodeIndexes (nextPage + tableFootprint leaves) indexes
      some (⟨indexed.1, indexed.2, layout, physicalPages⟩ :: remaining)

def indexPagesOf (encodings : List IndexEncoding) : List Page :=
  encodings.flatMap (·.pages)

def IndexEncoding.catalogEntry (encoding : IndexEncoding) : CatalogEntry := {
  kind := "index"
  name := encoding.index.name
  table := encoding.table.schema.name
  rootPage := encoding.layout.rootPage
  sql := indexSQL encoding.table encoding.index
  sqlIsNull := encoding.index.isImplicitPrimary encoding.table.schema }

@[simp] theorem IndexEncoding.canonicalize_catalogEntry
    (encoding : IndexEncoding) :
    encoding.canonicalize.catalogEntry = encoding.catalogEntry := by
  unfold IndexEncoding.canonicalize IndexEncoding.catalogEntry indexSQL
  simp

def indexEntriesOf (encodings : List IndexEncoding) : List CatalogEntry :=
  encodings.map (·.catalogEntry)

theorem indexEntriesOf_kind (encodings : List IndexEncoding)
    (entry : CatalogEntry) (member : entry ∈ indexEntriesOf encodings) :
    entry.kind = "index" := by
  unfold indexEntriesOf at member
  rcases List.mem_map.mp member with ⟨encoding, _, rfl⟩
  rfl

/-- First unused page after an aligned run of already-built index encodings. -/
def indexEndPage (nextPage : Nat) (encodings : List IndexEncoding) : Nat :=
  encodings.foldl
    (fun page encoding => page + tableFootprint encoding.layout.leaves) nextPage

/-- Encode indexes table by table. Besides matching catalog order, this exposes
the table boundary needed by the decoder proof instead of recovering that
boundary from a flattened list after the fact. -/
def encodeIndexTableGroups : Nat → List Core.Table →
    Option (List IndexEncoding)
  | _, [] => some []
  | nextPage, table :: tables => do
      let current ← encodeIndexes nextPage
        (table.indexes.map fun index => (table, index))
      let remaining ← encodeIndexTableGroups (indexEndPage nextPage current) tables
      some (current ++ remaining)

theorem encodeIndexes_canonicalize : ∀ (nextPage : Nat)
    (table : Core.Table) (indexes : List Core.Index),
    encodeIndexes nextPage
        (indexes.map fun index => (table.canonicalize, index)) =
      (encodeIndexes nextPage
        (indexes.map fun index => (table, index))).map
          (List.map IndexEncoding.canonicalize)
  | _, _, [] => rfl
  | nextPage, table, index :: indexes => by
      simp only [List.map_cons, encodeIndexes]
      rw [indexLeaves_canonicalize]
      cases leavesResult : indexLeaves table index with
      | none => rfl
      | some leaves =>
          simp only [Option.bind_eq_bind, Option.bind]
          cases pagesResult : indexPages? nextPage leaves with
          | none => rfl
          | some pages =>
              simp only
              rw [encodeIndexes_canonicalize]
              cases remainingResult : encodeIndexes
                  (nextPage + tableFootprint leaves)
                  (indexes.map fun candidate => (table, candidate)) with
              | none => rfl
              | some remaining => rfl

theorem indexEndPage_canonicalize : ∀ (encodings : List IndexEncoding)
    (nextPage : Nat),
    indexEndPage nextPage (encodings.map IndexEncoding.canonicalize) =
      indexEndPage nextPage encodings
  | [], _ => rfl
  | encoding :: encodings, nextPage => by
      simp only [List.map_cons, indexEndPage, List.foldl_cons,
        IndexEncoding.canonicalize]
      exact indexEndPage_canonicalize encodings
        (nextPage + tableFootprint encoding.layout.leaves)

end CoreFile

end SQLeanite
