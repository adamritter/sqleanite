import SQLeanite.CoreChunkPageDelta.ReplaceBetweenTreePagesAccounted

namespace SQLeanite
namespace CoreChunkPageDelta
attribute [local instance] lexOrd

theorem indexEntryLess_eq_textCompare
    (left right : CoreDecode.IndexEntry)
    {leftText rightText : PhysicalCodec.Text}
    (leftEq : left.value = .text leftText)
    (rightEq : right.value = .text rightText) :
    indexEntryLess left right =
      (compare (textIndexEntrySortKey left)
        (textIndexEntrySortKey right)).isLT := by
  unfold indexEntryLess textIndexEntrySortKey
  simp only [leftEq, rightEq, PhysicalQuery.compareValue]
  change (match compare leftText.bytes rightText.bytes with
    | .lt => true
    | .gt => false
    | .eq => decide (left.rowid.value < right.rowid.value)) =
      ((compare leftText.bytes rightText.bytes).then
        (compare left.rowid.value right.rowid.value)).isLT
  cases comparison : compare leftText.bytes rightText.bytes <;>
    simp [comparison]
  by_cases less : left.rowid.value < right.rowid.value
  · have ordered : compare left.rowid.value right.rowid.value = .lt :=
      compareOfLessAndEq_eq_lt.mpr less
    simp [less, ordered]
  · have notOrdered : compare left.rowid.value right.rowid.value ≠ .lt :=
      fun ordered => less (compareOfLessAndEq_eq_lt.mp ordered)
    cases ordered : compare left.rowid.value right.rowid.value <;> simp_all

theorem insertIndexEntry_perm (entry : CoreDecode.IndexEntry) :
    ∀ entries, (insertIndexEntry entry entries).Perm (entry :: entries)
  | [] => List.Perm.refl _
  | candidate :: entries => by
      unfold insertIndexEntry
      split
      · exact List.Perm.refl _
      · exact (insertIndexEntry_perm entry entries).cons candidate |>.trans
          (List.Perm.swap entry candidate entries)

theorem textKey_reverse_le_of_not_lt
    (left right : CoreDecode.IndexEntry)
    (notLess : (compare (textIndexEntrySortKey left)
      (textIndexEntrySortKey right)).isLT = false) :
    textIndexEntryLe right left = true := by
  unfold textIndexEntryLe
  cases comparison : compare (textIndexEntrySortKey left)
      (textIndexEntrySortKey right) with
  | lt => simp [comparison] at notLess
  | eq =>
      have reverse := Std.OrientedCmp.eq_comm.mp comparison
      simp [reverse]
  | gt =>
      have reverse := Std.OrientedCmp.lt_of_gt comparison
      simp [reverse]

theorem insertIndexEntry_pairwise_text
    (entry : CoreDecode.IndexEntry) {entryText : PhysicalCodec.Text}
    (entryEq : entry.value = .text entryText) : ∀ entries,
    (∀ candidate ∈ entries, ∃ text : PhysicalCodec.Text,
      candidate.value = .text text) →
    entries.Pairwise (fun left right => textIndexEntryLe left right = true) →
    (insertIndexEntry entry entries).Pairwise
      (fun left right => textIndexEntryLe left right = true)
  | [], _, _ => by simp [insertIndexEntry]
  | candidate :: entries, allText, sorted => by
      rcases allText candidate (by simp) with ⟨candidateText, candidateEq⟩
      have tailText : ∀ current ∈ entries,
          ∃ text : PhysicalCodec.Text, current.value = .text text := by
        intro current member
        exact allText current (by simp [member])
      have candidateBefore : ∀ current ∈ entries,
          textIndexEntryLe candidate current = true :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted := (List.pairwise_cons.mp sorted).2
      unfold insertIndexEntry
      split
      next less =>
        have lessCompare := indexEntryLess_eq_textCompare entry candidate
          entryEq candidateEq
        rw [lessCompare] at less
        have entryBeforeCandidate :
            textIndexEntryLe entry candidate = true := by
          unfold textIndexEntryLe
          cases comparison : compare (textIndexEntrySortKey entry)
              (textIndexEntrySortKey candidate) <;> simp_all
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          rcases List.mem_cons.mp member with rfl | member
          · exact entryBeforeCandidate
          · unfold textIndexEntryLe at entryBeforeCandidate ⊢
            exact Std.TransOrd.isLE_trans entryBeforeCandidate
              (candidateBefore current member)
        · exact sorted
      next notLess =>
        have notLessFalse : indexEntryLess entry candidate = false :=
          (Bool.not_eq_true _).mp notLess
        have compareEq := indexEntryLess_eq_textCompare entry candidate
          entryEq candidateEq
        rw [compareEq] at notLessFalse
        have candidateEntry := textKey_reverse_le_of_not_lt entry candidate
          notLessFalse
        apply List.pairwise_cons.mpr
        constructor
        · intro current member
          have sourceMember : current ∈ entry :: entries :=
            (insertIndexEntry_perm entry entries).subset member
          rcases List.mem_cons.mp sourceMember with rfl | sourceMember
          · exact candidateEntry
          · exact candidateBefore current sourceMember
        · exact insertIndexEntry_pairwise_text entry entryEq entries
            tailText tailSorted

theorem textIndexEntryLe_trans (left middle right : CoreDecode.IndexEntry)
    (leftMiddle : textIndexEntryLe left middle = true)
    (middleRight : textIndexEntryLe middle right = true) :
    textIndexEntryLe left right = true := by
  unfold textIndexEntryLe at leftMiddle middleRight ⊢
  exact Std.TransOrd.isLE_trans leftMiddle middleRight

theorem textIndexEntryLe_total (left right : CoreDecode.IndexEntry) :
    (textIndexEntryLe left right || textIndexEntryLe right left) = true := by
  unfold textIndexEntryLe
  cases comparison : compare (textIndexEntrySortKey left)
      (textIndexEntrySortKey right) with
  | lt => simp [comparison]
  | eq => simp [comparison]
  | gt =>
      have reverse := Std.OrientedCmp.lt_of_gt comparison
      simp [comparison, reverse]

theorem textIndexEntryLe_antisymm
    (left right : CoreDecode.IndexEntry)
    {leftText rightText : PhysicalCodec.Text}
    (leftEq : left.value = .text leftText)
    (rightEq : right.value = .text rightText)
    (leftRight : textIndexEntryLe left right = true)
    (rightLeft : textIndexEntryLe right left = true) : left = right := by
  unfold textIndexEntryLe at leftRight rightLeft
  have comparison := Std.OrientedCmp.isLE_antisymm leftRight rightLeft
  have keyBeq := Std.LawfulBEqOrd.compare_eq_iff_beq.mp comparison
  have keyEq := LawfulBEq.eq_of_beq keyBeq
  simp only [textIndexEntrySortKey, leftEq, rightEq,
    Prod.mk.injEq] at keyEq
  rcases keyEq with ⟨bytesEq, rowidValueEq⟩
  have textEq : leftText = rightText := by
    cases leftText
    cases rightText
    simp_all
  have rowidEq : left.rowid = right.rowid := by
    cases leftRow : left.rowid with
    | mk leftRowid leftLower leftUpper =>
      cases rightRow : right.rowid with
      | mk rightRowid rightLower rightUpper =>
        have rowidValues : leftRowid = rightRowid := by
          simpa [leftRow, rightRow] using rowidValueEq
        subst rightRowid
        congr
  cases left
  cases right
  simp_all

theorem mergeSort_append_text_insert
    (entries : List CoreDecode.IndexEntry) (entry : CoreDecode.IndexEntry)
    {entryText : PhysicalCodec.Text}
    (entryEq : entry.value = .text entryText)
    (allText : ∀ candidate ∈ entries,
      ∃ text : PhysicalCodec.Text, candidate.value = .text text) :
    (entries ++ [entry]).mergeSort textIndexEntryLe =
      insertIndexEntry entry (entries.mergeSort textIndexEntryLe) := by
  apply List.Perm.eq_of_pairwise
  · intro left right leftMember rightMember leftRight rightLeft
    have leftSource : left ∈ entries ++ [entry] :=
      (List.mergeSort_perm (entries ++ [entry]) textIndexEntryLe).subset
        leftMember
    have textOfSource : ∀ candidate ∈ entries ++ [entry],
        ∃ text : PhysicalCodec.Text, candidate.value = .text text := by
      intro candidate member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact allText candidate old
      · exact ⟨entryText, entryEq⟩
    rcases textOfSource left leftSource with ⟨leftText, leftEq⟩
    rcases textOfSource right (by
      have permSource := (insertIndexEntry_perm entry
        (entries.mergeSort textIndexEntryLe)).subset rightMember
      rcases List.mem_cons.mp permSource with rfl | sortedMember
      · simp
      · have oldMember := List.mem_mergeSort.mp sortedMember
        exact List.mem_append_left _ oldMember) with ⟨rightText, rightEq⟩
    exact textIndexEntryLe_antisymm left right leftEq rightEq
      leftRight rightLeft
  · exact List.pairwise_mergeSort textIndexEntryLe_trans
      textIndexEntryLe_total (entries ++ [entry])
  · apply insertIndexEntry_pairwise_text entry entryEq
    · intro candidate member
      exact allText candidate (List.mem_mergeSort.mp member)
    · exact List.pairwise_mergeSort textIndexEntryLe_trans
        textIndexEntryLe_total entries
  · have insertedPerm := insertIndexEntry_perm entry
      (entries.mergeSort textIndexEntryLe)
    have sortedPerm := List.mergeSort_perm entries textIndexEntryLe
    have moved := List.perm_middle (a := entry) (l₁ := entries) (l₂ := [])
    have moved' : (entries ++ [entry]).Perm (entry :: entries) := by
      simp only [List.append_nil] at moved
      exact moved
    have finalPerm := List.mergeSort_perm (entries ++ [entry]) textIndexEntryLe
    exact finalPerm.trans
      (moved'.trans ((sortedPerm.cons entry).symm.trans insertedPerm.symm))

def indexEntriesText (entries : List CoreDecode.IndexEntry) : Bool :=
  entries.all fun entry => CoreFile.valueIsText entry.value

def sortIndexEntries (entries : List CoreDecode.IndexEntry) :
    List CoreDecode.IndexEntry :=
  if indexEntriesInteger entries then
    entries.mergeSort integerIndexEntryLe
  else if indexEntriesText entries then
    entries.mergeSort textIndexEntryLe
  else entries.foldl (fun sorted entry => insertIndexEntry entry sorted) []

theorem sortIndexEntries_append_text_insert
    (entries : List CoreDecode.IndexEntry) (entry : CoreDecode.IndexEntry)
    {entryText : PhysicalCodec.Text}
    (entryEq : entry.value = .text entryText)
    (allText : ∀ candidate ∈ entries,
      ∃ text : PhysicalCodec.Text, candidate.value = .text text) :
    sortIndexEntries (entries ++ [entry]) =
      insertIndexEntry entry (sortIndexEntries entries) := by
  cases entries with
  | nil =>
      simp [sortIndexEntries, indexEntriesInteger, indexEntriesText,
        entryEq, insertIndexEntry]
  | cons head tail =>
      rcases allText head (by simp) with ⟨headText, headEq⟩
      have oldNotInteger : indexEntriesInteger (head :: tail) ≠ true := by
        simp [indexEntriesInteger, headEq, CoreFile.valueIsInteger]
      have newNotInteger :
          indexEntriesInteger ((head :: tail) ++ [entry]) ≠ true := by
        simp [indexEntriesInteger, headEq, CoreFile.valueIsInteger]
      have oldText : indexEntriesText (head :: tail) = true := by
        apply List.all_eq_true.mpr
        intro candidate member
        rcases allText candidate member with ⟨text, equal⟩
        simp [indexEntriesText, CoreFile.valueIsText, equal]
      have newText : indexEntriesText ((head :: tail) ++ [entry]) = true := by
        apply List.all_eq_true.mpr
        intro candidate member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · rcases allText candidate old with ⟨text, equal⟩
          simp [CoreFile.valueIsText, equal]
        · simp [CoreFile.valueIsText, entryEq]
      unfold sortIndexEntries
      rw [if_neg newNotInteger, if_pos newText,
        if_neg oldNotInteger, if_pos oldText]
      exact mergeSort_append_text_insert (head :: tail) entry entryEq allText

theorem integerIndexRowLe_entry (index : Core.Index)
    (left right : Core.Row) :
    CoreFile.integerIndexRowLe index left right =
      integerIndexEntryLe (indexEntryOfRow index left)
        (indexEntryOfRow index right) := by
  rfl

theorem textIndexRowLe_entry (index : Core.Index)
    (left right : Core.Row) :
    CoreFile.textIndexRowLe index left right =
      textIndexEntryLe (indexEntryOfRow index left)
        (indexEntryOfRow index right) := by
  rfl

theorem indexEntriesInteger_map (index : Core.Index) (rows : List Core.Row) :
    indexEntriesInteger (rows.map (indexEntryOfRow index)) =
      rows.all (fun row => CoreFile.valueIsInteger (row.value index.column)) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      unfold indexEntriesInteger at induction ⊢
      simp only [List.map_cons, List.all_cons, indexEntryOfRow, induction]

theorem indexEntriesText_map (index : Core.Index) (rows : List Core.Row) :
    indexEntriesText (rows.map (indexEntryOfRow index)) =
      rows.all (fun row => CoreFile.valueIsText (row.value index.column)) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      unfold indexEntriesText at induction ⊢
      simp only [List.map_cons, List.all_cons, indexEntryOfRow, induction]

theorem map_insertIndexRow (index : Core.Index) (row : Core.Row) :
    ∀ rows,
    (CoreFile.insertIndexRow index row rows).map (indexEntryOfRow index) =
      insertIndexEntry (indexEntryOfRow index row)
        (rows.map (indexEntryOfRow index))
  | [] => rfl
  | candidate :: rows => by
      simp only [CoreFile.insertIndexRow, insertIndexEntry, List.map_cons]
      have comparison : indexEntryLess (indexEntryOfRow index row)
          (indexEntryOfRow index candidate) =
          CoreFile.indexRowLess index row candidate := rfl
      rw [comparison]
      split
      · rfl
      · simp only [List.map_cons, map_insertIndexRow index row rows]

theorem map_foldInsertIndexRow (index : Core.Index) :
    ∀ (rows accumulator : List Core.Row),
    (rows.foldl (fun sorted row => CoreFile.insertIndexRow index row sorted)
        accumulator).map (indexEntryOfRow index) =
      (rows.map (indexEntryOfRow index)).foldl
        (fun sorted entry => insertIndexEntry entry sorted)
        (accumulator.map (indexEntryOfRow index))
  | [], _ => rfl
  | row :: rows, accumulator => by
      simp only [List.foldl_cons, List.map_cons]
      rw [map_foldInsertIndexRow index rows
        (CoreFile.insertIndexRow index row accumulator)]
      rw [map_insertIndexRow]

theorem expectedIndexEntries_eq_sortSource (table : Core.Table)
    (index : Core.Index) :
    CoreDecode.expectedIndexEntries table index =
      sortIndexEntries (table.rows.map (indexEntryOfRow index)) := by
  unfold CoreDecode.expectedIndexEntries CoreFile.sortedIndexRows
    sortIndexEntries
  by_cases integers : CoreFile.indexValuesInteger table index = true
  · rw [if_pos integers]
    have sourceIntegers :
        indexEntriesInteger (table.rows.map (indexEntryOfRow index)) = true := by
      rw [indexEntriesInteger_map]
      exact integers
    rw [if_pos sourceIntegers]
    exact List.map_mergeSort fun left _ right _ =>
      integerIndexRowLe_entry index left right
  · rw [if_neg integers]
    have sourceNotIntegers :
        indexEntriesInteger (table.rows.map (indexEntryOfRow index)) ≠ true := by
      rw [indexEntriesInteger_map]
      exact integers
    rw [if_neg sourceNotIntegers]
    by_cases texts : CoreFile.indexValuesText table index = true
    · rw [if_pos texts]
      have sourceTexts :
          indexEntriesText (table.rows.map (indexEntryOfRow index)) = true := by
        rw [indexEntriesText_map]
        exact texts
      rw [if_pos sourceTexts]
      exact List.map_mergeSort fun left _ right _ =>
        textIndexRowLe_entry index left right
    · rw [if_neg texts]
      have sourceNotTexts :
          indexEntriesText (table.rows.map (indexEntryOfRow index)) ≠ true := by
        rw [indexEntriesText_map]
        exact texts
      rw [if_neg sourceNotTexts]
      exact map_foldInsertIndexRow index table.rows []

theorem expectedIndexEntries_append_text
    (before after : Core.Table) (index : Core.Index) (row : Core.Row)
    (rowsEq : after.rows = before.rows ++ [row])
    (beforeText : CoreFile.indexValuesText before index = true)
    {rowText : PhysicalCodec.Text}
    (rowTextEq : row.value index.column = .text rowText) :
    CoreDecode.expectedIndexEntries after index =
      insertIndexEntry (indexEntryOfRow index row)
        (CoreDecode.expectedIndexEntries before index) := by
  rw [expectedIndexEntries_eq_sortSource,
    expectedIndexEntries_eq_sortSource, rowsEq, List.map_append]
  simp only [List.map_singleton]
  apply sortIndexEntries_append_text_insert
  · exact rowTextEq
  · intro candidate member
    rcases List.mem_map.mp member with ⟨sourceRow, sourceMember, rfl⟩
    rcases (CoreFile.indexValuesText_iff before index).mp beforeText sourceRow
      sourceMember with ⟨text, equal⟩
    exact ⟨text, equal⟩

theorem indexValuesText_append_text
    (before after : Core.Table) (index : Core.Index) (row : Core.Row)
    (rowsEq : after.rows = before.rows ++ [row])
    (beforeText : CoreFile.indexValuesText before index = true)
    {rowText : PhysicalCodec.Text}
    (rowTextEq : row.value index.column = .text rowText) :
    CoreFile.indexValuesText after index = true := by
  unfold CoreFile.indexValuesText at beforeText ⊢
  rw [rowsEq, List.all_eq_true]
  intro candidate member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact (List.all_eq_true.mp beforeText) candidate old
  · simp [CoreFile.valueIsText, rowTextEq]

/-- Primary-order index inputs. Equality is linear to decide; unlike
`indexImage`, it does not sort every index twice on each table mutation. -/
def indexSourceImage (table : Core.Table) :
    List (Core.Index × List CoreDecode.IndexEntry) :=
  table.indexes.map fun index =>
    (index, table.rows.map (indexEntryOfRow index))

def sortIndexSourceImage
    (source : List (Core.Index × List CoreDecode.IndexEntry)) :
    List (Core.Index × List CoreDecode.IndexEntry) :=
  source.map fun pair => (pair.1, sortIndexEntries pair.2)

theorem indexImage_eq_sortIndexSourceImage (table : Core.Table) :
    indexImage table = sortIndexSourceImage (indexSourceImage table) := by
  unfold indexImage indexSourceImage sortIndexSourceImage
  rw [List.map_map]
  apply List.map_congr_left
  intro index _
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  exact expectedIndexEntries_eq_sortSource table index

def TableDelta.tablePagesSufficient (delta : TableDelta) : Bool :=
  (delta.before.table.schema == delta.after.table.schema &&
    (delta.before.table.indexes == delta.after.table.indexes &&
      delta.before.table.catalogSQL == delta.after.table.catalogSQL)) &&
    (delta.before.table.indexes.isEmpty ||
      (delta.before.table.rows.length == delta.after.table.rows.length &&
        indexSourceImage delta.before.table == indexSourceImage delta.after.table))

/-- The linear source-image check is strong enough to leave physical index
pages untouched: deterministic logical sorting maps equal sources to the exact
same promoted-key index image. -/
theorem TableDelta.tablePagesSufficient_indexImage (delta : TableDelta)
    (sufficient : delta.tablePagesSufficient = true) :
    indexImage delta.before.table = indexImage delta.after.table := by
  by_cases empty : delta.before.table.indexes = []
  · simp [TableDelta.tablePagesSufficient, empty] at sufficient
    unfold indexImage
    rw [sufficient.2.1]
    simp [empty]
  · simp [TableDelta.tablePagesSufficient, empty] at sufficient
    rw [indexImage_eq_sortIndexSourceImage,
      indexImage_eq_sortIndexSourceImage, sufficient.2.2]

theorem TableDelta.tablePagesSufficient_rowsLength_of_indexed
    (delta : TableDelta) (sufficient : delta.tablePagesSufficient = true)
    (indexed : delta.before.table.indexes ≠ []) :
    delta.after.table.rows.length = delta.before.table.rows.length := by
  simp [TableDelta.tablePagesSufficient, indexed] at sufficient
  exact sufficient.2.1.symm

/-- The part of table identity stored in `sqlite_master`.  Rows and proof-tree
topology are deliberately absent: a data mutation changes both without
changing the catalog declaration. -/
def TableMetadataEq (before after : Core.Table) : Prop :=
  before.schema = after.schema ∧ before.indexes = after.indexes ∧ before.catalogSQL = after.catalogSQL

inductive TablesMetadataAligned : List Core.Table → List Core.Table → Prop where
  | nil : TablesMetadataAligned [] []
  | cons {before after : Core.Table} {befores afters : List Core.Table}
      (head : TableMetadataEq before after)
      (tail : TablesMetadataAligned befores afters) :
      TablesMetadataAligned (before :: befores) (after :: afters)

theorem TableDelta.tablePagesSufficient_metadata (delta : TableDelta)
    (sufficient : delta.tablePagesSufficient = true) :
    TableMetadataEq delta.before.table delta.after.table := by
  simp only [TableDelta.tablePagesSufficient, Bool.and_eq_true,
    beq_iff_eq] at sufficient
  exact sufficient.1

end CoreChunkPageDelta

end SQLeanite
